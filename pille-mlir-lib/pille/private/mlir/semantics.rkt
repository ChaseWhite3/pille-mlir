#lang racket/base

(require racket/list
         racket/match
         racket/string
         racket/treelist)

(provide supported-widths
         normalize-literal
         width->type
         type->width
         (struct-out port)
         check-semantics
         semantics->data data->semantics
         semantics->manifest
         sem_operand sem_result sem_local
         sem_const_width sem_const_like sem_binary sem_select
         make_semantics
         semantic_error_node
         (rename-out [expr? is_semantic_expression]
                     [semantics? is_semantics]))

;; The SMT model of an operation is a small typed expression tree over
;; fixed-width bitvectors. It is shared by macro expansion, runtime descriptor
;; reconstruction, and the manifest consumed by the native lowering pass.
;;
;;   (expr 'operand (name))          an operand of the modeled operation
;;   (expr 'local   (index))         an earlier `let` binding of the same model
;;   (expr 'result  (name))          a result; only usable as a literal's width
;;   (expr 'const   (value spec))    spec is (width N) or (like expression)
;;   (expr 'add|'sub|'mul (a b))     wrapping arithmetic, equal widths
;;   (expr 'select  (a b then else)) `then` where a equals b, `else` elsewhere;
;;                                   a and b have equal widths, as do the arms
;;
;; Trees are immutable. Structure is checked by the constructors below; names,
;; arity, coverage, and width relationships are checked by `check-semantics`
;; against the ports of the operation that owns the model.
(struct expr (tag args) #:transparent)
;; A model may also state what it requires of its operands: a list of
;; requirements, each a list of (lhs . rhs) pairs of which at least one must be
;; equal. A requirement is an obligation of every use of the operation, proved
;; along with a query's property; it is never assumed.
(struct semantics (locals results requirements) #:transparent)

;; Errors identify the offending node so that expansion can report the source
;; location of the corresponding syntax. `node` is #f for whole-model errors.
(struct exn:fail:semantics exn:fail:user (node))

(define (semantic-error node message . arguments)
  (raise (exn:fail:semantics (apply format message arguments)
                             (current-continuation-marks)
                             node)))

(define (semantic_error_node value)
  (and (exn:fail:semantics? value) (exn:fail:semantics-node value)))

;; Signless integers of these widths map to SMT bitvectors of exactly the same
;; width. No other type has an SMT sort in this fragment.
(define supported-widths '(1 8 16 32 64))

(define (width->type width) (format "i~a" width))

(define (type->width text)
  (match (regexp-match #px"^i(1|8|16|32|64)$" text)
    [(list _ digits) (string->number digits)]
    [_ #f]))

;; Literal policy: a literal for width w must lie in [-2^(w-1), 2^w - 1], the
;; range MLIR accepts for a signless iN constant. A negative literal denotes
;; its two's complement residue, so the canonical value is always in
;; [0, 2^w - 1]. Out-of-range literals are rejected, never truncated.
(define (normalize-literal value width)
  (and (exact-integer? value)
       (<= (- (expt 2 (sub1 width))) value (sub1 (expt 2 width)))
       (modulo value (expt 2 width))))

(define (items who value)
  (cond
    [(treelist? value) (treelist->list value)]
    [(list? value) value]
    [else (raise-argument-error who "list or treelist" value)]))

(define (name who value)
  (unless (and (string? value)
               (regexp-match? #px"^[A-Za-z_][A-Za-z0-9_]*$" value))
    (raise-argument-error who "identifier string ([A-Za-z_][A-Za-z0-9_]*)" value))
  (string->immutable-string value))

(define (sem_operand value) (expr 'operand (list (name 'sem_operand value))))
(define (sem_result value) (expr 'result (list (name 'sem_result value))))

(define (sem_local index)
  (unless (exact-nonnegative-integer? index)
    (raise-argument-error 'sem_local "exact-nonnegative-integer?" index))
  (expr 'local (list index)))

(define (sem_const_width value width)
  (unless (exact-integer? value)
    (raise-argument-error 'sem_const_width "exact-integer?" value))
  (unless (memv width supported-widths)
    (semantic-error #f "unsupported bitvector width ~a; supported widths are 1, 8, 16, 32, and 64"
                    width))
  (define normalized (normalize-literal value width))
  (unless normalized
    (semantic-error #f "literal ~a does not fit in ~a bits (accepted range is ~a through ~a)"
                    value width (- (expt 2 (sub1 width))) (sub1 (expt 2 width))))
  (expr 'const (list normalized (list 'width width))))

;; The literal takes the width of another expression, or of the result, at each
;; concrete instantiation. Only the width of `target` is used, never its value.
;; The literal's value stays as written until that width is known.
(define (sem_const_like value target)
  (unless (exact-integer? value)
    (raise-argument-error 'sem_const_like "exact-integer?" value))
  (unless (expr? target)
    (raise-argument-error 'sem_const_like "semantic expression" target))
  (unless (normalize-literal value 64)
    (semantic-error #f "literal ~a does not fit in any supported width" value))
  (expr 'const (list value (list 'like target))))

(define (sem_binary tag lhs rhs)
  (define symbol (if (string? tag) (string->symbol tag) tag))
  (unless (memq symbol '(add sub mul))
    (raise-argument-error 'sem_binary "'add, 'sub, or 'mul (symbol or string)" tag))
  (unless (expr? lhs) (raise-argument-error 'sem_binary "semantic expression" lhs))
  (unless (expr? rhs) (raise-argument-error 'sem_binary "semantic expression" rhs))
  (expr symbol (list lhs rhs)))

;; The fragment's only choice. A comparison is not a value of its own: it
;; exists only as the test of a choice, so there is no Boolean sort to keep
;; apart from one-bit bitvectors.
(define (sem_select lhs rhs then else)
  (for ([argument (in-list (list lhs rhs then else))])
    (unless (expr? argument) (raise-argument-error 'sem_select "semantic expression" argument)))
  (expr 'select (list lhs rhs then else)))

(define (bindings who values)
  (for/list ([entry (in-list (items who values))])
    (match (items who entry)
      [(list label (? expr? value)) (cons (name who label) value)]
      [_ (raise-argument-error who "binding [name, semantic expression]" entry)])))

(define (make_semantics locals results [requirements '()])
  (semantics (bindings 'make_semantics locals) (bindings 'make_semantics results)
             (for/list ([requirement (in-list (items 'make_semantics requirements))])
               (define alternatives
                 (for/list ([alternative (in-list (items 'make_semantics requirement))])
                   (match (items 'make_semantics alternative)
                     [(list (? expr? lhs) (? expr? rhs)) (cons lhs rhs)]
                     [_ (raise-argument-error 'make_semantics
                                              "comparison [semantic expression, semantic expression]"
                                              alternative)])))
               (when (null? alternatives)
                 (raise-argument-error 'make_semantics "a requirement with at least one comparison"
                                       requirement))
               alternatives)))

;; A port as seen by the width analysis. `key` identifies an equality class:
;; ports constrained by the same shared schema variable always have the same
;; type. `widths` lists the supported widths the port's constraint admits, or
;; is #f when the constraint is unbounded and only an instance can tell.
(struct port (name key widths) #:transparent)

;; An abstract width is either an exact width or an equality class.
(struct class (key widths label) #:transparent)

(define (describe-widths widths)
  (string-join (map width->type widths) " or "))

(define (describe value)
  (match value
    [(? exact-integer? width) (format "a ~a-bit value" width)]
    [(class _ #f label) label]
    [(class _ widths label) (format "~a (~a)" label (describe-widths widths))]))

;; Widths that can be shown unequal are rejected now. Widths that merely are
;; not known to be equal are accepted: the lowering pass checks every concrete
;; instance, so a schema that permits mixed widths never acquires a hidden
;; same-width assumption.
(define (unify node what lhs rhs)
  (define (mismatch)
    (semantic-error node "~a combines ~a with ~a; widths must be equal and are never coerced"
                    what (describe lhs) (describe rhs)))
  (match* (lhs rhs)
    [((? exact-integer?) (? exact-integer?))
     (unless (= lhs rhs) (mismatch))
     lhs]
    [((? exact-integer? width) (class _ widths _))
     (when (and widths (not (memv width widths))) (mismatch))
     width]
    [((class _ widths _) (? exact-integer? width))
     (when (and widths (not (memv width widths))) (mismatch))
     width]
    [((class key-a widths-a _) (class key-b widths-b _))
     (unless (or (equal? key-a key-b)
                 (not widths-a) (not widths-b)
                 (for/or ([width (in-list widths-a)]) (memv width widths-b)))
       (mismatch))
     lhs]))

(define (check-semantics operation value operands results)
  (define (fail node message . arguments)
    (semantic-error node "~a: SMT semantics: ~a" operation (apply format message arguments)))
  (define (port-named ports label)
    (for/first ([candidate (in-list ports)] #:when (equal? (port-name candidate) label))
      candidate))
  (define (port-class kind candidate)
    (class (port-key candidate) (port-widths candidate)
           (format "~a ~a" kind (port-name candidate))))

  ;; The model is total and has one scalar value: exactly one result, assigned
  ;; exactly once, and no port that could never have a bitvector sort.
  (for ([assignment (in-list (semantics-results value))])
    (define label (car assignment))
    (cond
      [(port-named results label) (void)]
      [(port-named operands label)
       (fail (cdr assignment) "cannot assign to operand ~a; assign to a result" label)]
      [else (fail (cdr assignment) "assignment to unknown result ~a" label)]))
  (let ([duplicate (check-duplicates (map car (semantics-results value)))])
    (when duplicate
      (fail (cdr (last (filter (lambda (assignment) (equal? (car assignment) duplicate))
                               (semantics-results value))))
            "duplicate assignment to result ~a" duplicate)))
  (for ([candidate (in-list results)])
    (unless (assoc (port-name candidate) (semantics-results value))
      (fail #f "result ~a is never assigned" (port-name candidate))))
  (unless (= (length results) 1)
    (fail #f "exactly one result is supported, but the operation declares ~a"
          (length results)))
  (for ([candidate (in-list (append operands results))])
    (when (null? (or (port-widths candidate) '(#t)))
      (fail #f "~a admits no supported bitvector type (i1, i8, i16, i32, or i64)"
            (port-name candidate))))

  (define locals (make-vector (length (semantics-locals value)) #f))
  (define (reference node allow-result?)
    (match node
      [(expr 'operand (list label))
       (define candidate (port-named operands label))
       (unless candidate (fail node "unknown operand reference ~a" label))
       (port-class "operand" candidate)]
      [(expr 'local (list index))
       (define known (and (< index (vector-length locals)) (vector-ref locals index)))
       (unless known (fail node "local ~a is used before its definition" index))
       known]
      [(expr 'result (list label))
       (define candidate (port-named results label))
       (unless candidate (fail node "unknown result reference ~a" label))
       (unless allow-result?
         (fail node "result ~a cannot be read by its own definition; it may only give a literal its width"
               label))
       (port-class "result" candidate)]))
  (define (width-of node)
    (match node
      [(expr (or 'operand 'local 'result) _) (reference node #f)]
      [(expr 'const (list _ (list 'width width))) width]
      [(expr 'const (list literal (list 'like target)))
       (define width
         (if (eq? (expr-tag target) 'result) (reference target #t) (width-of target)))
       (define candidates
         (match width
           [(? exact-integer?) (list width)]
           [(class _ widths _) widths]))
       (when (and candidates
                  (not (for/or ([candidate (in-list candidates)])
                         (normalize-literal literal candidate))))
         (fail node "literal ~a does not fit any width of ~a" literal (describe width)))
       width]
      [(expr (and tag (or 'add 'sub 'mul)) (list lhs rhs))
       (define left (width-of lhs))
       (define right (width-of rhs))
       (unify node (format "~a: SMT semantics: bv.~a" operation tag) left right)]
      [(expr 'select (list lhs rhs then else))
       (define left (width-of lhs))
       (define right (width-of rhs))
       (unify node (format "~a: SMT semantics: the comparison of bv.if" operation) left right)
       (define chosen (width-of then))
       (define otherwise (width-of else))
       (unify node (format "~a: SMT semantics: bv.if" operation) chosen otherwise)]))
  (for ([local (in-list (semantics-locals value))] [index (in-naturals)])
    (vector-set! locals index
                 (match (width-of (cdr local))
                   [(? exact-integer? width) width]
                   [(class key widths _) (class key widths (format "local ~a" (car local)))])))
  (for* ([requirement (in-list (semantics-requirements value))]
         [alternative (in-list requirement)])
    (unify (car alternative)
           (format "~a: SMT semantics: a comparison of `requires`" operation)
           (width-of (car alternative))
           (width-of (cdr alternative))))
  (for ([assignment (in-list (semantics-results value))])
    (unify (cdr assignment)
           (format "~a: SMT semantics: the assignment to ~a" operation (car assignment))
           (port-class "result" (port-named results (car assignment)))
           (width-of (cdr assignment)))))

;; Serialized form: JSON arrays and strings only. Literals are decimal strings
;; so that 64-bit values survive any JSON implementation exactly.
(define (expr->data node)
  (match node
    [(expr (and tag (or 'operand 'result)) (list label)) (list (symbol->string tag) label)]
    [(expr 'local (list index)) (list "local" index)]
    [(expr 'const (list value (list 'width width)))
     (list "const" (number->string value) (list "width" width))]
    [(expr 'const (list value (list 'like reference)))
     (list "const" (number->string value) (list "like" (expr->data reference)))]
    [(expr 'select arguments) (cons "select" (map expr->data arguments))]
    [(expr tag (list lhs rhs)) (list (symbol->string tag) (expr->data lhs) (expr->data rhs))]))

(define (invalid)
  (raise-user-error 'member_deserialize "invalid serialized SMT semantics"))

(define (data->literal text)
  (define value (and (string? text) (regexp-match? #px"^-?[0-9]+$" text) (string->number text)))
  (unless value (invalid))
  value)

(define (data->expr data)
  (match data
    [(list "operand" (? string? label)) (sem_operand label)]
    [(list "result" (? string? label)) (sem_result label)]
    [(list "local" (? exact-nonnegative-integer? index)) (sem_local index)]
    [(list "const" text (list "width" (? exact-integer? width)))
     (sem_const_width (data->literal text) width)]
    [(list "const" text (list "like" target))
     (sem_const_like (data->literal text) (data->expr target))]
    [(list (and tag (or "add" "sub" "mul")) lhs rhs)
     (sem_binary tag (data->expr lhs) (data->expr rhs))]
    [(list "select" lhs rhs then else)
     (sem_select (data->expr lhs) (data->expr rhs) (data->expr then) (data->expr else))]
    [_ (invalid)]))

(define (semantics->data value)
  (define (entries bindings)
    (for/list ([binding (in-list bindings)])
      (list (car binding) (expr->data (cdr binding)))))
  (define requirements
    (for/list ([requirement (in-list (semantics-requirements value))])
      (for/list ([alternative (in-list requirement)])
        (list (expr->data (car alternative)) (expr->data (cdr alternative))))))
  ;; The requirements are written only when there are some, so a model without
  ;; any serializes exactly as it did before they existed.
  (append (list (entries (semantics-locals value)) (entries (semantics-results value)))
          (if (null? requirements) '() (list requirements))))

(define (data->semantics data)
  (define (entries value)
    (unless (list? value) (invalid))
    (for/list ([entry (in-list value)])
      (match entry
        [(list (? string? label) node) (list label (data->expr node))]
        [_ (invalid)])))
  (define (requirements value)
    (unless (list? value) (invalid))
    (for/list ([requirement (in-list value)])
      (unless (list? requirement) (invalid))
      (for/list ([alternative (in-list requirement)])
        (match alternative
          [(list lhs rhs) (list (data->expr lhs) (data->expr rhs))]
          [_ (invalid)]))))
  (match data
    [(list locals results) (make_semantics (entries locals) (entries results))]
    [(list locals results required)
     (make_semantics (entries locals) (entries results) (requirements required))]
    [_ (invalid)]))

;; The lowering pass receives positions rather than names: operand order is the
;; identity that MLIR preserves, and it is checked against each instance.
(define (semantics->manifest value operand-names)
  (define (position label)
    (index-of operand-names label))
  (define (reference node)
    (match node
      [(expr 'operand (list label)) (list "operand" (position label))]
      [(expr 'local (list index)) (list "local" index)]
      [(expr 'result _) (list "result")]))
  (define (convert node)
    (match node
      [(expr (or 'operand 'local) _) (reference node)]
      [(expr 'const (list literal (list 'width width)))
       (list "const" (number->string literal) (list "width" width))]
      [(expr 'const (list literal (list 'like target)))
       (list "const" (number->string literal)
             (list "like" (if (eq? (expr-tag target) 'result) (reference target) (convert target))))]
      [(expr 'select arguments) (cons "select" (map convert arguments))]
      [(expr tag (list lhs rhs)) (list (symbol->string tag) (convert lhs) (convert rhs))]))
  (define assignment (car (semantics-results value)))
  (hasheq 'operands operand-names
          'result (car assignment)
          'locals (for/list ([local (in-list (semantics-locals value))])
                    (list (car local) (convert (cdr local))))
          'value (convert (cdr assignment))
          ;; Each requirement is a predicate over the operands and locals.
          'requires (for/list ([requirement (in-list (semantics-requirements value))])
                      (cons "or"
                            (for/list ([alternative (in-list requirement)])
                              (list "eq" (convert (car alternative)) (convert (cdr alternative))))))))
