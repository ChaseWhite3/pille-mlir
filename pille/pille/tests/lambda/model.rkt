#lang racket/base

;; A lambda calculus and the closure conversion that compiles it, in Redex (SYNTHETIC), for
;; pille/tests/mlir_lambda.rhm, which lowers the converted programs to MLIR and runs them.
;;
;; MLIR has no operation for a lambda that captures its free variables. A function value it has
;; (func.constant, func.call_indirect), but not one with an environment. A compiler makes closures
;; the way assembly does: a record on the heap holding a code pointer and the captured values, and
;; a call that loads the code pointer from the record and passes it the record. That compilation is
;; closure conversion. This module states it twice over:
;;
;;   Λ     the source: numbers, variables, (λ (x) e), application, (+ e e), call by value
;;   Λc    the target: first-order code blocks, each taking its closure record and one argument;
;;         (closure ℓ c ...) builds a record, (env-ref k) reads the record's k-th captured value,
;;         (call c c) calls through a record
;;   convert   Λ → Λc
;;
;; and gives each language its own reduction relation, so that what conversion must preserve can
;; be checked rather than assumed: a program and its conversion reduce to the same number, both to
;; a procedure, or both get stuck (`conversion-preserves?`). It is checked on random terms three ways
;; (`conversion_holds`): redex-check over the grammar, redex-check over a type judgment, and terms drawn
;; by hand so that records hold several values, which neither of Redex's generators gave.
;; Addition wraps at 64 bits in both, as the machine's does.

(require redex/reduction-semantics
         racket/list
         racket/match)

(provide Λ Λc ->Λ ->Λc fv convert
         answer_of_source answer_of_converted
         conversion_holds random_programs examples widest)

;;==================================================================================================
;; The source

(define-language Λ
  (e ::= n x (λ (x) e) (e e) (+ e e))
  (n ::= integer)
  (x ::= variable-not-otherwise-mentioned)
  (v ::= n (λ (x) e))
  (E ::= hole (E e) (v E) (+ E e) (+ v E))
  #:binding-forms
  (λ (x) e #:refers-to x))

(define (wrap64 n)
  (define m (bitwise-and n #xFFFFFFFFFFFFFFFF))
  (if (>= m #x8000000000000000) (- m #x10000000000000000) m))

(define ->Λ
  (reduction-relation
   Λ #:domain e
   (--> (in-hole E ((λ (x) e) v)) (in-hole E (substitute e x v)) "β")
   (--> (in-hole E (+ n_1 n_2)) (in-hole E ,(wrap64 (+ (term n_1) (term n_2)))) "+")))

;; The free variables of a term, each once, in the order they are first said.
(define-metafunction Λ
  fv : e -> (x ...)
  [(fv n) ()]
  [(fv x) (x)]
  [(fv (λ (x) e)) ,(remove (term x) (term (fv e)))]
  [(fv (+ e_1 e_2)) ,(remove-duplicates (append (term (fv e_1)) (term (fv e_2))))]
  [(fv (e_1 e_2)) ,(remove-duplicates (append (term (fv e_1)) (term (fv e_2))))])

;;==================================================================================================
;; The target

(define-language Λc
  (p ::= (program (code ℓ x c) ... c))
  (c ::= n x (+ c c) (closure ℓ c ...) (env-ref k) (call c c))
  (n ::= integer)
  (k ::= natural)
  (x ℓ ::= variable-not-otherwise-mentioned)
  ;; a closure value: the code's label and the values it captured
  (w ::= n (closure ℓ w ...))
  (E ::= hole (+ E c) (+ w E) (closure ℓ w ... E c ...) (call E c) (call w E)))

;; A code block's body with its argument and its record's values in place: x is the argument,
;; (env-ref k) the record's k-th value. A body has no binders, so this is plain replacement, and
;; a label (the ℓ of a closure the body builds) is never replaced.
(define-metafunction Λc
  instantiate : c x w (w ...) -> c
  [(instantiate n x w_a (w ...)) n]
  [(instantiate x x w_a (w ...)) w_a]
  [(instantiate x_other x w_a (w ...)) x_other]
  [(instantiate (+ c_1 c_2) x w_a (w ...))
   (+ (instantiate c_1 x w_a (w ...)) (instantiate c_2 x w_a (w ...)))]
  [(instantiate (closure ℓ c ...) x w_a (w ...)) (closure ℓ (instantiate c x w_a (w ...)) ...)]
  [(instantiate (env-ref k) x w_a (w ...)) ,(list-ref (term (w ...)) (term k))]
  [(instantiate (call c_1 c_2) x w_a (w ...))
   (call (instantiate c_1 x w_a (w ...)) (instantiate c_2 x w_a (w ...)))])

(define ->Λc
  (reduction-relation
   Λc #:domain p
   (--> (program (code ℓ_c x_c c_c) ... (in-hole E (+ n_1 n_2)))
        (program (code ℓ_c x_c c_c) ... (in-hole E ,(wrap64 (+ (term n_1) (term n_2)))))
        "+")
   ;; a call through a record: the record's label says which code runs
   (--> (program (code ℓ_1 x_1 c_1) ... (code ℓ x c_body) (code ℓ_2 x_2 c_2) ...
                 (in-hole E (call (closure ℓ w ...) w_a)))
        (program (code ℓ_1 x_1 c_1) ... (code ℓ x c_body) (code ℓ_2 x_2 c_2) ...
                 (in-hole E (instantiate c_body x w_a (w ...))))
        "call")))

;;==================================================================================================
;; Closure conversion

;; A closed Λ term as a Λc program. Each λ becomes a code block whose record holds the λ's free
;; variables in `fv` order; inside the block, its own parameter stays a variable and each free
;; variable is read from the record.
(define (convert e)
  (define codes '())
  (define count 0)
  (define (fresh)
    (begin0 (string->symbol (format "lambda~a" count))
            (set! count (add1 count))))
  ;; `param` is the enclosing block's parameter (#f at the top), `free` its record's variables
  (define (cc e param free)
    (match e
      [(? exact-integer?) e]
      [(? symbol? x)
       (cond
         [(eq? x param) x]
         [(index-of free x) => (λ (k) `(env-ref ,k))]
         [else (error 'convert "~a is free in a term that must be closed" x)])]
      [`(+ ,a ,b) `(+ ,(cc a param free) ,(cc b param free))]
      [`(λ (,x) ,body)
       (define captured (term (fv ,e)))
       (define label (fresh))
       (define converted-body (cc body x captured))
       (set! codes (cons `(code ,label ,x ,converted-body) codes))
       `(closure ,label ,@(for/list ([z (in-list captured)]) (cc z param free)))]
      [`(,f ,a) `(call ,(cc f param free) ,(cc a param free))]))
  (define main (cc e #f '()))
  `(program ,@(reverse codes) ,main))

;;==================================================================================================
;; Running

;; Reduce until no rule applies, or until the fuel is spent (a term may not terminate). Both
;; relations are deterministic: a term with two next steps is an error in the model.
(define (reduce relation t fuel)
  (let loop ([t t] [fuel fuel])
    (if (zero? fuel)
        (values t #f)
        (match (apply-reduction-relation relation t)
          ['() (values t #t)]
          [(list next) (loop next (sub1 fuel))]
          [several (error 'reduce "~a steps from ~s" (length several) t)]))))

;; What a program comes to: an integer, 'procedure, 'stuck, or 'no-answer when the fuel ran out.
(define (answer_of_source e #:fuel [fuel 5000])
  (define-values (final done?) (reduce ->Λ e fuel))
  (cond
    [(not done?) 'no-answer]
    [(exact-integer? final) final]
    [(redex-match? Λ (λ (x) e) final) 'procedure]
    [else 'stuck]))

(define (answer_of_converted p #:fuel [fuel 5000])
  (define-values (final done?) (reduce ->Λc p fuel))
  (define last (and done? (car (reverse final))))
  (cond
    [(not done?) 'no-answer]
    [(exact-integer? last) last]
    [(redex-match? Λc (closure ℓ w ...) last) 'procedure]
    [else 'stuck]))

;;==================================================================================================
;; What conversion preserves

;; A random term with its free variables replaced by numbers, so that it is closed.
(define (closed e)
  (for/fold ([t e]) ([x (in-list (term (fv ,e)))] [i (in-naturals 1)])
    (term (substitute ,t ,x ,i) #:lang Λ)))

(define (conversion-preserves? e)
  (define source (answer_of_source e))
  (or (eq? source 'no-answer)
      (equal? source (answer_of_converted (convert e)))))

;; Terms drawn from the grammar are mostly tiny, and a variable an inner λ captures is rare among
;; them (a free variable is closed with a number). So conversion is also checked over terms drawn
;; from a judgment: a copy of Λ whose λ says its parameter's type, and the terms it types as int.
;; Such a term always comes to a number, and uses the variables around it, so its conversion
;; captures. Its annotations are erased before it is reduced or converted.
(define-extended-language Λτ Λ
  (e ::= .... (λ (x τ) e))
  (τ ::= int (→ τ τ))
  (Γ ::= · (x τ Γ)))

(define-metafunction Λτ
  lookup : Γ x -> τ or #f
  [(lookup · x) #f]
  [(lookup (x τ Γ) x) τ]
  [(lookup (x_1 τ Γ) x_2) (lookup Γ x_2)])

(define-judgment-form Λτ
  #:mode (types I I O)
  [-------------------- "number"
   (types Γ n int)]
  [(where τ (lookup Γ x))
   -------------------- "variable"
   (types Γ x τ)]
  [(types (x τ_1 Γ) e τ_2)
   -------------------- "λ"
   (types Γ (λ (x τ_1) e) (→ τ_1 τ_2))]
  [(types Γ e_1 (→ τ_1 τ_2)) (types Γ e_2 τ_1)
   -------------------- "application"
   (types Γ (e_1 e_2) τ_2)]
  [(types Γ e_1 int) (types Γ e_2 int)
   -------------------- "+"
   (types Γ (+ e_1 e_2) int)])

(define (erased e)
  (match e
    [`(λ (,x ,_) ,body) `(λ (,x) ,(erased body))]
    [(list parts ...) (map erased parts)]
    [_ e]))

;; The most values any record of a converted program holds.
(define (widest p)
  (match p
    [`(closure ,_ ,fields ...) (apply max (length fields) (map widest fields))]
    [(list parts ...) (apply max 0 (map widest parts))]
    [_ 0]))

;; Redex's generator from the judgment above never gave a record of two values (measured
;; 2026-11-18: 800 terms, sizes 4 to 10), so a conversion that put a record's values in the wrong
;; order passed. These terms are drawn by hand instead, well typed by construction and biased
;; toward the variables around them, so that a λ inside λs captures several. Redex's reduction
;; relations still say what each comes to. `random` is the generator to draw from.
(define names '(a b c f g h k x y))
(define (scoped-term random)
  (define (pick xs) (list-ref xs (random (length xs))))
  (define (chance n) (zero? (random n)))
  ;; a term of type τ, with Γ the variables in scope ((x . τ) ...), innermost first
  (define (gen τ Γ depth)
    (define here (for/list ([b (in-list Γ)] #:when (equal? (cdr b) τ)
                            #:unless (assq (car b) (takef Γ (λ (o) (not (eq? o b))))))
                   (car b)))
    (define callers (for/list ([b (in-list Γ)]
                               #:when (match (cdr b) [`(→ ,_ ,r) (equal? r τ)] [_ #f])
                               #:unless (assq (car b) (takef Γ (λ (o) (not (eq? o b))))))
                      b))
    (cond
      [(and (pair? here) (or (<= depth 0) (chance 2))) (pick here)]
      [(and (pair? callers) (> depth 0) (chance 2))
       (match-define (cons f `(→ ,σ ,_)) (pick callers))
       `(,f ,(gen σ Γ (sub1 depth)))]
      [(<= depth 0)
       (match τ
         ['int (random 10)]
         [`(→ ,σ ,ρ) (let ([x (pick names)]) `(λ (,x) ,(gen ρ (cons (cons x σ) Γ) 0)))])]
      [else
       (match τ
         ['int
          (case (random 4)
            [(0) (random 10)]
            [(1 2) `(+ ,(gen 'int Γ (sub1 depth)) ,(gen 'int Γ (sub1 depth)))]
            [else
             ;; a λ applied at once: a new variable in scope for what follows
             (define σ (pick '(int int (→ int int))))
             (define x (pick names))
             `((λ (,x) ,(gen 'int (cons (cons x σ) Γ) (sub1 depth))) ,(gen σ Γ (sub1 depth)))])]
         [`(→ ,σ ,ρ)
          (define x (pick names))
          `(λ (,x) ,(gen ρ (cons (cons x σ) Γ) (sub1 depth)))])]))
  (gen 'int '() 7))

;; `count` such terms whose conversion captures, drawn from a seeded generator: [term, ...]. Every
;; other one has a record of two values or more.
(define (scoped-terms count seed)
  (define generator (make-pseudo-random-generator))
  (parameterize ([current-pseudo-random-generator generator])
    (random-seed seed)
    (let loop ([found '()] [tries 0])
      (if (or (= (length found) count) (> tries (* 1000 count)))
          (reverse found)
          (let ([e (scoped-term random)])
            (if (> (widest (convert e)) (if (even? (length found)) 1 0))
                (loop (cons e found) (add1 tries))
                (loop found (add1 tries))))))))

;; #t, or the first counterexample: redex-check over `attempts` random closed terms from the
;; grammar (each outcome: a number, a procedure, stuck), and as many from the judgment; then as
;; many drawn by scoped-term, each of which must come to a number.
(define (conversion_holds attempts #:seed [seed 2026])
  (random-seed seed)
  (define untyped
    (redex-check Λ e (conversion-preserves? (closed (term e)))
                 #:attempts attempts
                 #:attempt-size (λ (n) (+ 3 (modulo n 7)))
                 #:print? #f))
  (define typed
    (redex-check Λτ #:satisfying (types · e int)
                 (let ([plain (erased (term e))])
                   (and (exact-integer? (answer_of_source plain))
                        (conversion-preserves? plain)))
                 #:attempts attempts
                 #:print? #f))
  (define scoped
    (or (for/first ([e (in-list (scoped-terms attempts seed))]
                    #:unless (and (exact-integer? (answer_of_source e)) (conversion-preserves? e)))
          e)
        #t))
  (cond
    [(not (eq? untyped #t)) untyped]
    [(not (eq? typed #t)) typed]
    [(not (eq? scoped #t)) (list 'counterexample scoped)]
    [else #t]))

;; Random closed terms that come to a number and whose conversion captures a variable, with that
;; number: [[term, integer], ...], drawn by scoped-term. The machine code the test runs has no
;; tags, so a term that gets stuck in the model has no meaning there; these never do.
(define (random_programs count #:seed [seed 17])
  (for/list ([e (in-list (scoped-terms count seed))])
    (list e (answer_of_source e))))

;;==================================================================================================
;; Examples: a name, a term and the number it comes to

(define examples
  `(["identity applied"
     ((λ (x) (+ x 1)) 41)
     42]
    ;; a closure that captures n: the adder's record holds 5
    ["make-adder"
     (((λ (n) (λ (x) (+ x n))) 5) 37)
     42]
    ;; a closure passed as an argument and called twice
    ["twice"
     ((λ (f) (f (f 10))) (λ (x) (+ x 16)))
     42]
    ;; a closure that captures two closures, in an order that matters: f after g, (20 + 1) doubled,
    ;; where g after f would give 41
    ["compose"
     ((((λ (f) (λ (g) (λ (x) (f (g x))))) (λ (y) (+ y y))) (λ (z) (+ z 1))) 20)
     42]
    ;; Church numerals: three times two, counted with add1 from 0
    ["church multiplication"
     (((((λ (m) (λ (n) (λ (s) (m (n s)))))
         (λ (s) (λ (z) (s (s (s z))))))
        (λ (s) (λ (z) (s (s z)))))
       (λ (k) (+ k 1)))
      0)
     6]
    ;; a variable two closures share, and a shadowed one: the inner x is the argument
    ["shadowing"
     (((λ (x) (λ (x) (+ x x))) 100) 21)
     42]
    ;; the 64-bit wrap the machine has, stated in the model
    ["wraps at 64 bits"
     ((λ (x) (+ x 1)) 9223372036854775807)
     -9223372036854775808]))
