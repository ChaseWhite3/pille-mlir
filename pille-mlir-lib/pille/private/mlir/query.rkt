#lang racket/base

(require json
         racket/function
         racket/list
         racket/match
         racket/promise
         racket/string
         racket/treelist
         "schema.rkt"
         "semantics.rkt"
         "solver.rkt"
         "session.rkt"
         "tools.rkt"
         "lower.rhm")

(provide smt_input smt_result smt_result_at smt_const smt_binary smt_ite
         smt_eq smt_cmp smt_no_overflow smt_not smt_and smt_or
         smt_named
         make_smt_objective objective_check objective_inputs objective_assumptions objective_value
         objective_session_check
         make_smt_scope scope_assert scope_push scope_pop scope_check scope_close scope_is_open
         scope_inputs scope_assumptions scope_goal_script scope_check_all
         render_term render_formula
         make_smt_query
         smt_lower_text
         make_spec make_values_spec make_smt_batch make_smt_values_batch make_smt_values_query
         batch_queries batch_check batch_session_check query_session_check values_query_check
         values_query_inputs values_query_assumptions
         query_inputs query_assumptions query_check
         (rename-out [term? is_term]
                     [term-width term_width]
                     [formula? is_formula]
                     [named? is_named]
                     [query-feasibility query_feasibility]
                     [query? is_query]
                     [objective? is_objective]
                     [scope? is_scope]
                     [scope-function scope_function]
                     [scope-dialect-name scope_dialect]
                     [get-objective-module objective_module]
                     [objective-smtlib objective_smtlib]
                     [objective-feasibility objective_feasibility]
                     [objective-function objective_function]
                     [objective-dialect objective_dialect]
                     [objective-direction objective_direction]
                     [objective-term objective_term]
                     [objective-signed? objective_signed]
                     [get-query-module query_module]
                     [query-smtlib query_smtlib]
                     [query-function query_function]
                     [query-dialect query_dialect]
                     [query-property query_property]
                     [query-preconditions query_preconditions]
                     [spec? is_spec]
                     [values-spec? is_values_spec]
                     [batch? is_batch]
                     [values-batch? is_values_batch]
                     [get-batch-module batch_module]
                     [get-batch-smtlib batch_smtlib]
                     [values-query? is_values_query]
                     [get-values-query-module values_query_module]
                     [values-query-smtlib values_query_smtlib]
                     [values-query-function values_query_function]
                     [values-query-dialect values_query_dialect]
                     [values-query-result-width values_query_width]))

;; Properties are built from two distinct sorts. A term is a bitvector with an
;; exact width; a formula is an SMT Boolean. A one-bit term is not a formula,
;; and no constructor converts between the two.
;;
;;   (term 'input (name) width)   a function argument, by display name
;;   (term 'result () width)      the value returned by a one-result function
;;   (term 'result (index) width) one of the values a function returns
;;   (term 'const (value) width)  a typed literal
;;   (term 'add|'sub|'mul (a b) width)
;;   (term 'ite (f a b) width)    a where f holds, else b
;;   (formula 'eq (a b)) (formula 'not (f)) (formula 'and fs) (formula 'or fs)
;;   (formula 'cmp (predicate a b))   predicate one of comparison-predicates
;;   (formula 'no_overflow (operation signed? a b))   operation add, sub or mul
(struct term (tag args width) #:transparent)
(struct formula (tag args) #:transparent)

;; A precondition with a name. Only a query's list of preconditions holds
;; these; a name is no part of a formula.
(struct named (name formula) #:transparent)

;; `feasibility` is the script that asks whether the named preconditions can
;; hold together (#f where none is named), and `feasibility-body` its
;; declarations and assertions alone, for a session.
(struct query (module smtlib dialect function inputs property preconditions feasibility feasibility-body))
(struct spec (function inputs property preconditions) #:transparent)
(struct values-spec (function inputs preconditions) #:transparent)
(struct batch (module smtlib queries))
(struct values-batch (module smtlib queries))
(struct values-query (module smtlib dialect function inputs preconditions result-name result-width defined-name))

;; The least or greatest value of `term` over the inputs that satisfy the
;; preconditions. `symbol` is the SMT-LIB constant the term is bound to.
(struct objective (module smtlib dialect function inputs preconditions term direction signed? symbol
                          feasibility body feasibility-body))

;; Assertions kept in a session's solver over one function's inputs. `frames`
;; is what is asserted now, the innermost frame first: each a list of
;; (formula . SMT-LIB assertions), the latest first.
(struct scope (session dialect module function inputs declarations [frames #:mutable]))
(define (scope-dialect-name value) (dialect_name (scope-dialect value)))

(define (get-objective-module value) (objective-module value))
(define (get-query-module value) (force (query-module value)))
(define (get-values-query-module value) (force (values-query-module value)))
(define (get-batch-module value)
  (if (batch? value) (batch-module value) (values-batch-module value)))
(define (get-batch-smtlib value)
  (if (batch? value) (batch-smtlib value) (values-batch-smtlib value)))
(define (batch_queries value)
  (list->treelist (if (batch? value) (batch-queries value) (values-batch-queries value))))

(define (builder-error who message . arguments)
  (apply raise-user-error who message arguments))

(define (check-width who width)
  (unless (memv width supported-widths)
    (builder-error who "unsupported bitvector width ~a; supported widths are 1, 8, 16, 32, and 64"
                   width))
  width)

;; Display names become SMT-LIB symbols verbatim, because the MLIR exporter
;; prints them without quoting. Only simple identifiers that cannot collide
;; with SMT-LIB syntax or theory symbols are therefore accepted.
(define reserved-names
  '("_" "as" "let" "exists" "forall" "match" "par"
    "BINARY" "DECIMAL" "HEXADECIMAL" "NUMERAL" "STRING"
    "true" "false" "not" "and" "or" "xor" "ite" "distinct"
    "assert" "echo" "exit" "pop" "push" "reset"
    "concat" "extract" "repeat" "zero_extend" "sign_extend"
    "rotate_left" "rotate_right" "Bool" "BitVec"))

(define (smt_input name width)
  (unless (and (string? name) (regexp-match? #px"^[A-Za-z_][A-Za-z0-9_]*$" name))
    (builder-error 'input "invalid input name ~s: use letters, digits, and underscores, not starting with a digit"
                   name))
  (when (or (member name reserved-names) (regexp-match? #px"^bv" name))
    (builder-error 'input "input name ~s is reserved by SMT-LIB or its bitvector theory" name))
  (term 'input (list (string->immutable-string name)) (check-width 'input width)))

(define (smt_result width)
  (term 'result '() (check-width 'result width)))

(define (smt_result_at index width)
  (unless (exact-nonnegative-integer? index)
    (raise-argument-error 'result "exact-nonnegative-integer?" index))
  (term 'result (list index) (check-width 'result width)))

(define (smt_const value width)
  (unless (exact-integer? value)
    (raise-argument-error 'const "exact-integer?" value))
  (check-width 'const width)
  (define normalized (normalize-literal value width))
  (unless normalized
    (builder-error 'const "literal ~a does not fit in ~a bits (accepted range is ~a through ~a)"
                   value width (- (expt 2 (sub1 width))) (sub1 (expt 2 width))))
  (term 'const (list normalized) width))

(define (describe-sort value)
  (cond
    [(term? value) (format "a ~a-bit bitvector" (term-width value))]
    [(formula? value) "a Boolean predicate"]
    [else (format "~e" value)]))

(define (check-terms who lhs rhs)
  (for ([value (in-list (list lhs rhs))])
    (unless (term? value)
      (builder-error who "expected bitvector terms, received ~a; Boolean predicates and bitvectors are distinct sorts"
                     (describe-sort value))))
  (unless (= (term-width lhs) (term-width rhs))
    (builder-error who "width mismatch: ~a and ~a; widths are never converted implicitly"
                   (describe-sort lhs) (describe-sort rhs))))

(define (smt_binary tag lhs rhs)
  (define symbol (if (string? tag) (string->symbol tag) tag))
  (unless (memq symbol '(add sub mul))
    (raise-argument-error 'smt_binary "'add, 'sub, or 'mul (symbol or string)" tag))
  (check-terms symbol lhs rhs)
  (term symbol (list lhs rhs) (term-width lhs)))

(define (smt_eq lhs rhs)
  (check-terms 'eq lhs rhs)
  (formula 'eq (list lhs rhs)))

;; Unsigned and signed orderings. Signedness is said by the predicate, never
;; inferred from a term.
(define comparison-predicates '(ult ule ugt uge slt sle sgt sge))

(define (smt_cmp predicate lhs rhs)
  (define symbol (if (string? predicate) (string->symbol predicate) predicate))
  (unless (memq symbol comparison-predicates)
    (raise-argument-error 'smt_cmp "one of ult ule ugt uge slt sle sgt sge (symbol or string)" predicate))
  (check-terms symbol lhs rhs)
  (formula 'cmp (list symbol lhs rhs)))

(define (check-formula who value)
  (unless (formula? value)
    (builder-error who "expected a Boolean predicate, received ~a; Boolean predicates and bitvectors are distinct sorts"
                   (describe-sort value))))

;; That `lhs op rhs`, read as unsigned or as signed numbers, is not changed by
;; the wrapping of `op`. The arithmetic builders keep their wrapping meaning;
;; this says of one use that it did not wrap.
(define (smt_no_overflow operation lhs rhs signed?)
  (define symbol (if (string? operation) (string->symbol operation) operation))
  (unless (memq symbol '(add sub mul))
    (raise-argument-error 'smt_no_overflow "'add, 'sub, or 'mul (symbol or string)" operation))
  (unless (boolean? signed?)
    (raise-argument-error 'smt_no_overflow "boolean?" signed?))
  (check-terms (string->symbol (format "no_overflow_~a" symbol)) lhs rhs)
  (formula 'no_overflow (list symbol signed? lhs rhs)))

(define (smt_not value)
  (check-formula 'not value)
  (formula 'not (list value)))

(define (smt_ite test chosen otherwise)
  (check-formula 'ite test)
  (check-terms 'ite chosen otherwise)
  (term 'ite (list test chosen otherwise) (term-width chosen)))

(define (entries who values)
  (cond
    [(treelist? values) (treelist->list values)]
    [(list? values) values]
    [else (raise-argument-error who "list or treelist" values)]))

(define (connective who tag values)
  (define operands (entries who values))
  (when (null? operands)
    (builder-error who "expected at least one predicate"))
  (for ([operand (in-list operands)]) (check-formula who operand))
  (formula tag operands))

;; A name becomes an SMT-LIB quoted symbol, |name|, which may hold anything but
;; a bar or a backslash; a line break would break the scripts it is written in.
(define (smt_named value name)
  (check-formula 'precondition value)
  (unless (and (string? name) (non-empty-string? name) (not (regexp-match? #rx"[|\\\\\n\r]" name)))
    (builder-error 'precondition
                   "invalid precondition name ~s: use a nonempty string without bars, backslashes or line breaks"
                   name))
  (named (string->immutable-string name) value))

(define (assumption-formula value) (if (named? value) (named-formula value) value))
(define (assumption-name value) (and (named? value) (named-name value)))
(define (render-assumption value)
  (if (named? value)
      (format "~a: ~a" (named-name value) (render-formula (named-formula value)))
      (render-formula value)))

(define (smt_and values) (connective 'and 'and values))
(define (smt_or values) (connective 'or 'or values))

(define (render_term value)
  (unless (term? value) (raise-argument-error 'render_term "term" value))
  (string->immutable-string (render-term value)))

(define (render_formula value)
  (unless (formula? value) (raise-argument-error 'render_formula "formula" value))
  (string->immutable-string (render-formula value)))

(define (render-term value)
  (match value
    [(term 'input (list name) _) name]
    [(term 'result '() _) "result"]
    [(term 'result (list index) _) (format "result[~a]" index)]
    [(term 'ite (list test chosen otherwise) _)
     (format "(~a ? ~a : ~a)" (render-formula test) (render-term chosen) (render-term otherwise))]
    [(term 'const (list literal) 1) (format "0b~a:bv1" literal)]
    [(term 'const (list literal) width)
     (format "0x~a:bv~a"
             (let ([digits (number->string literal 16)])
               (string-append (make-string (- (quotient width 4) (string-length digits)) #\0) digits))
             width)]
    [(term tag (list lhs rhs) _)
     (format "(~a ~a ~a)" (render-term lhs)
             (case tag [(add) "+"] [(sub) "-"] [(mul) "*"])
             (render-term rhs))]))

(define (render-formula value)
  (match value
    [(formula 'eq (list lhs rhs)) (format "~a == ~a" (render-term lhs) (render-term rhs))]
    [(formula 'cmp (list predicate lhs rhs))
     (format "~a ~a ~a" (render-term lhs)
             (case predicate
               [(ult) "<u"] [(ule) "<=u"] [(ugt) ">u"] [(uge) ">=u"]
               [(slt) "<s"] [(sle) "<=s"] [(sgt) ">s"] [(sge) ">=s"])
             (render-term rhs))]
    [(formula 'no_overflow (list operation signed? lhs rhs))
     (format "no_overflow(~a ~a ~a, ~a)" (render-term lhs)
             (case operation [(add) "+"] [(sub) "-"] [(mul) "*"])
             (render-term rhs) (if signed? "signed" "unsigned"))]
    [(formula 'not (list operand)) (format "!(~a)" (render-formula operand))]
    [(formula tag operands)
     (define joined
       (string-join (map render-formula operands) (if (eq? tag 'and) " && " " || ")))
     (if (= (length operands) 1) joined (string-append "(" joined ")"))]))

;; Lowering to the manifest resolves every reference to an identity: an input
;; is its argument position, and the result is the selected return value.
(define (term->manifest value inputs)
  (match value
    [(term 'input (list name) width)
     (define position (index-of inputs value))
     (unless position
       (define declared
         (for/first ([input (in-list inputs)] #:when (equal? (car (term-args input)) name)) input))
       (if declared
           (builder-error 'smt_query "input ~a is declared with width ~a but referenced with width ~a"
                          name (term-width declared) width)
           (builder-error 'smt_query "the property refers to input ~a, which is not among the declared inputs"
                          name)))
     (list "input" position)]
    [(term 'result '() _) (list "result")]
    [(term 'result (list index) _) (list "result_at" index)]
    [(term 'ite (list test chosen otherwise) _)
     (list "ite" (formula->manifest test inputs) (term->manifest chosen inputs)
           (term->manifest otherwise inputs))]
    [(term 'const (list literal) width)
     (list "const" (number->string literal) (list "width" width))]
    [(term tag (list lhs rhs) _)
     (list (symbol->string tag) (term->manifest lhs inputs) (term->manifest rhs inputs))]))

(define (formula->manifest value inputs)
  (match value
    [(formula 'eq (list lhs rhs))
     (list "eq" (term->manifest lhs inputs) (term->manifest rhs inputs))]
    [(formula 'cmp (list predicate lhs rhs))
     (list "cmp" (symbol->string predicate) (term->manifest lhs inputs) (term->manifest rhs inputs))]
    [(formula 'no_overflow (list operation signed? lhs rhs))
     (list "no_overflow" (symbol->string operation) signed?
           (term->manifest lhs inputs) (term->manifest rhs inputs))]
    [(formula tag operands)
     (cons (symbol->string tag)
           (for/list ([operand (in-list operands)]) (formula->manifest operand inputs)))]))

;; Each reference to a returned value: (index . width), index #f for the result
;; of a one-result function.
(define (result-widths value)
  (define (node? part) (or (term? part) (formula? part)))
  (match value
    [(term 'result '() width) (list (cons #f width))]
    [(term 'result (list index) width) (list (cons index width))]
    [(term _ arguments _) (append-map result-widths (filter node? arguments))]
    [(formula _ operands) (append-map result-widths (filter node? operands))]))

(define (validate-inputs function inputs preconditions)
  (unless (and (string? function) (non-empty-string? function))
    (raise-argument-error 'smt_query "nonempty function symbol name" function))
  (define declared (entries 'smt_query inputs))
  (for ([input (in-list declared)])
    (unless (and (term? input) (eq? (term-tag input) 'input))
      (raise-argument-error 'smt_query "list of inputs" inputs)))
  (define duplicate (check-duplicates (map (lambda (input) (car (term-args input))) declared)))
  (when duplicate
    (builder-error 'smt_query "duplicate input name ~a; each argument needs a distinct display name" duplicate))
  (define given (entries 'smt_query preconditions))
  (define assumptions (map assumption-formula given))
  (for ([assumption (in-list assumptions)]) (check-formula 'smt_query assumption))
  (define repeated (check-duplicates (filter values (map assumption-name given))))
  (when repeated
    (builder-error 'smt_query "duplicate precondition name ~s; a name says which precondition is meant" repeated))
  (values declared assumptions))

;; Specs retain immutable property descriptors. Batch validation resolves their
;; references with an index in each error; the lowering checks signatures.
(define (make_spec function inputs property [preconditions '()])
  (spec (string->immutable-string function) (entries 'Spec inputs) property
        (entries 'Spec preconditions)))

(define (make_values_spec function inputs [preconditions '()])
  (values-spec (string->immutable-string function) (entries 'ValuesSpec inputs)
               (entries 'ValuesSpec preconditions)))

(define (spec-fields value)
  (if (spec? value)
      (values (spec-function value) (spec-inputs value) (spec-property value) (spec-preconditions value))
      (values (values-spec-function value) (values-spec-inputs value) #f (values-spec-preconditions value))))

(define (fresh-name initial inputs)
  (define names (map (lambda (input) (car (term-args input))) inputs))
  (let loop ([name initial])
    (if (member name names) (loop (string-append name "_")) name)))

(define (spec-manifest value [also '()])
  (define-values (function declared property given) (spec-fields value))
  (define-values (_declared assumptions) (validate-inputs function declared given))
  (when (spec? value) (check-formula 'smt_query property))
  ;; `also`: terms the query uses beside its property and preconditions
  (define references (remove-duplicates (append-map result-widths
                                                   (append also
                                                           (if property (cons property assumptions) assumptions)))))
  (define widths (for/list ([reference (in-list references)] #:unless (car reference)) (cdr reference)))
  (when (> (length widths) 1)
    (builder-error 'smt_query "the result is referenced with conflicting widths: ~a"
                   (string-join (map number->string widths) ", ")))
  (define indexed
    (sort (for/list ([reference (in-list references)] #:when (car reference)) reference) < #:key car))
  (define conflict (check-duplicates (map car indexed)))
  (when conflict
    (builder-error 'smt_query "result ~a is referenced with conflicting widths: ~a" conflict
                   (string-join (for/list ([reference (in-list indexed)] #:when (= (car reference) conflict))
                                  (number->string (cdr reference)))
                                ", ")))
  (define base
    (hasheq 'function function
            'inputs (for/list ([input (in-list declared)])
                      (hasheq 'name (car (term-args input)) 'width (term-width input)))
            'result_width (if (null? widths) (json-null) (car widths))
            'result_widths (for/list ([reference (in-list indexed)]) (list (car reference) (cdr reference)))
            'preconditions (for/list ([assumption (in-list assumptions)])
                             (formula->manifest assumption declared))
            'property (if property (formula->manifest property declared) (json-null))))
  (if property base
      (hash-set* base 'mode "values"
                 'result_symbol (fresh-name "pille_result" declared)
                 'defined_symbol (fresh-name "pille_defined" declared))))

;; Identical IRDL can describe different meanings: the supplied dialect owns
;; the model. Structural compatibility does not establish semantic identity.
(define (check-context who dialect module)
  (unless (is_dialect dialect) (raise-argument-error who "dialect" dialect))
  (unless (is_module module) (raise-argument-error who "module" module))
  (unless (equal? (module_irdl module) (dialect_irdl dialect))
    (builder-error who
                   "the module was not verified against dialect ~a's generated IRDL definitions; construct it with this dialect's module method"
                   (dialect_name dialect))))

(define (context-manifest dialect version)
  (hasheq 'format "pille-smt-query" 'version version
          'operations (for/hasheq ([model (in-list (operation_models dialect))])
                        (values (string->symbol (car model)) (cdr model)))
          'unmodeled (unmodeled_operation_names dialect)))

(define (expected-inputs declared)
  (for/list ([input (in-list declared)])
    (cons (car (term-args input)) (term-width input))))

;; The lowering is `lower.rhm`, over the module's generic form. It returns the
;; module of solvers and each solver as a module of its own.
(define (run-lowering module manifest)
  (define-values (text members)
    (if (string? manifest)
        (lower_text (module_generic module) manifest)
        (lower (module_generic module) manifest)))
  (values text (treelist->list members)))

;; Lowers a manifest given as JSON text, bypassing the manifest this module
;; derives from a dialect: for tests of what the lowering itself checks.
(define (smt_lower_text module manifest)
  (unless (is_module module) (raise-argument-error 'smt_lower_text "module" module))
  (unless (string? manifest) (raise-argument-error 'smt_lower_text "string?" manifest))
  (define-values (text _members) (run-lowering module manifest))
  text)

;; The lowering asserts a query's preconditions first, one assertion each, in
;; order. Gives the script with each named precondition's assertion named
;; (the same text where none is), and, where any is named, the script that
;; asks whether the preconditions can hold together and that script's
;; declarations and assertions alone.
(define (named-scripts who script preconditions)
  (define names (map assumption-name preconditions))
  (cond
    [(not (ormap values names)) (values script #f #f)]
    [else
     (define whole (open-output-string))
     (define body (open-output-string))
     (define previous 0)
     (define asserted 0)
     (for ([entry (in-list (smtlib-commands script))])
       (define end (cdr entry))
       (define original (substring script previous end))
       (set! previous end)
       (match (car entry)
         [(list "assert" _)
          (define name (and (< asserted (length names)) (list-ref names asserted)))
          (define text
            (cond
              [name
               (define trimmed (string-trim original))
               (define lead (substring original 0 (- (string-length original) (string-length (string-trim original #:right? #f)))))
               (string-append lead "(assert (! "
                              (string-trim (substring trimmed 7 (sub1 (string-length trimmed))))
                              " :named |" name "|))")]
              [else original]))
          (display text whole)
          (when (< asserted (length names)) (display (string-trim text) body) (newline body))
          (set! asserted (add1 asserted))]
         [(list (or "declare-const" "declare-fun") _ ...)
          (display original whole)
          (display (string-trim original) body) (newline body)]
         [_ (display original whole)]))
     (display (substring script previous) whole)
     (unless (>= asserted (length names))
       (builder-error who "internal error: the exported SMT-LIB asserts fewer preconditions than the query has"))
     (define assertions (get-output-string body))
     (values (string->immutable-string (get-output-string whole))
             (string->immutable-string
              (string-append core-options "(set-logic QF_BV)\n" assertions "(check-sat)\n(get-unsat-core)\n"))
             (string->immutable-string assertions))]))

(define (make_smt_query dialect module function inputs property preconditions)
  (check-context 'smt_query dialect module)
  (define description (make_spec function inputs property preconditions))
  (define manifest
    (for/fold ([manifest (context-manifest dialect 1)])
              ([(key value) (in-hash (spec-manifest description))])
      (hash-set manifest key value)))
  (define-values (lowered _members) (run-lowering module manifest))
  (define verified (parse_stock_module lowered module))
  (define-values (smtlib feasibility feasibility-body)
    (named-scripts 'smt_query (to_smtlib verified) (spec-preconditions description)))
  (unless (equal? (smtlib-declarations smtlib) (expected-inputs (spec-inputs description)))
    (builder-error 'smt_query "internal error: the exported SMT-LIB does not declare exactly the query's inputs:\n~a" smtlib))
  (query verified smtlib (dialect_name dialect) (spec-function description)
         (spec-inputs description) property (spec-preconditions description)
         feasibility feasibility-body))

;; Every smt.solver region exports a self-contained script ending in reset.
;; Split on parsed commands, never on text inside strings, comments, or terms.
(define (split-queries text)
  (define start 0)
  (define chunks
    (for/list ([command (in-list (smtlib-commands text))]
               #:when (equal? (car command) '("reset")))
      (define end (cdr command))
      (define part (string->immutable-string (string-append (substring text start end) "\n")))
      (set! start end)
      part))
  (unless (null? (smtlib-commands (substring text start)))
    (builder-error 'smt_batch "exported SMT batch has commands after the last query's reset"))
  chunks)

(define (make-batch dialect module specifications values?)
  (define who (if values? 'smt_values_batch 'smt_batch))
  (check-context who dialect module)
  (define specs (entries who specifications))
  (when (null? specs) (builder-error who "expected at least one query spec"))
  (define descriptions
    (for/list ([value (in-list specs)] [index (in-naturals)])
      (with-handlers ([exn:fail? (lambda (error)
                                 (builder-error who "spec ~a: ~a" index (exn-message error)))])
        (unless ((if values? values-spec? spec?) value)
          (raise-argument-error who (if values? "ValuesSpec" "Spec") value))
        (spec-manifest value))))
  (define manifest (hash-set (context-manifest dialect 2) 'queries descriptions))
  (define-values (lowered standalone) (run-lowering module manifest))
  (define verified (parse_stock_module lowered module))
  (define text (to_smtlib verified))
  (define chunks (split-queries text))
  (unless (and (= (length specs) (length chunks)) (= (length specs) (length standalone)))
    (builder-error who "internal error: lowered/exported query count does not match the specs"))
  (define queries
    (for/list ([value (in-list specs)] [description (in-list descriptions)]
               [script (in-list chunks)] [ir (in-list standalone)] [index (in-naturals)])
      (define-values (function inputs property assumptions) (spec-fields value))
      (define declarations (smtlib-declarations script))
      (define expected (expected-inputs inputs))
      ;; Construction checks the whole batch once. Accessing a member's module
      ;; verifies the lowering's isolated module lazily, without adding
      ;; processes to ordinary batch construction or solver execution.
      (define member-module (delay (parse_stock_module ir module)))
      (cond
        [values?
         (define result-name (hash-ref description 'result_symbol))
         (define defined-name (hash-ref description 'defined_symbol))
         (define result-entry (assoc result-name declarations))
         (unless (and result-entry (memv (cdr result-entry) supported-widths)
                      (equal? declarations (append expected (list result-entry (cons defined-name 1)))))
           (builder-error who "spec ~a: unexpected declarations in exported values query" index))
         (values-query member-module script (dialect_name dialect) function inputs assumptions
                       result-name (cdr result-entry) defined-name)]
        [else
         (unless (equal? declarations expected)
           (builder-error who "spec ~a: exported declarations do not match the inputs" index))
         (define-values (named feasibility feasibility-body) (named-scripts who script assumptions))
         (query member-module named (dialect_name dialect) function inputs property assumptions
                feasibility feasibility-body)])))
  ((if values? values-batch batch) verified text queries))

;; An objective is lowered as a query of its own mode: the preconditions, then
;; the term bound to a fresh symbol. The dialect has no objective, so Z3's
;; (minimize s) or (maximize s) is written into the exported SMT-LIB before
;; its (check-sat), and (get-value ...) after it, in place of the exporter's
;; closing (reset).
(define (make_smt_objective dialect module function inputs term direction signed? preconditions)
  (check-context 'smt_objective dialect module)
  (unless (term? term) (raise-argument-error 'smt_objective "term" term))
  (unless (memq direction '(minimize maximize))
    (raise-argument-error 'smt_objective "'minimize or 'maximize" direction))
  (unless (boolean? signed?) (raise-argument-error 'smt_objective "boolean?" signed?))
  (define description (make_values_spec function inputs preconditions))
  (define declared (values-spec-inputs description))
  (define symbol (fresh-name "pille_objective" declared))
  (define manifest
    (for/fold ([manifest (context-manifest dialect 1)])
              ([(key value) (in-hash (hash-set* (hash-remove (hash-remove (spec-manifest description (list term))
                                                                         'result_symbol)
                                                            'defined_symbol)
                                               'mode "objective"
                                               'objective (term->manifest term declared)
                                               'objective_symbol symbol
                                               'signed signed?))])
      (hash-set manifest key value)))
  (define-values (lowered _members) (run-lowering module manifest))
  (define verified (parse_stock_module lowered module))
  (define-values (exported feasibility feasibility-body)
    (named-scripts 'smt_objective (to_smtlib verified) (values-spec-preconditions description)))
  (define expected (append (expected-inputs declared) (list (cons symbol (term-width term)))))
  (unless (equal? (smtlib-declarations exported) expected)
    (builder-error 'smt_objective "internal error: the exported SMT-LIB does not declare exactly the inputs and the objective:\n~a" exported))
  (define checks
    (for/list ([command (in-list (smtlib-commands exported))] #:when (equal? (car command) '("check-sat")))
      (cdr command)))
  (unless (= (length checks) 1)
    (builder-error 'smt_objective "internal error: expected exactly one (check-sat) in the exported SMT-LIB"))
  (define before (substring exported 0 (- (car checks) (string-length "(check-sat)"))))
  (define script
    (string->immutable-string
     (string-append "(set-option :produce-models true)\n" before
                    (format "(~a ~a)\n(check-sat)\n(get-value (~a))\n" direction symbol
                            (string-join (cons symbol (map car (expected-inputs declared))) " ")))))
  (objective verified script (dialect_name dialect) (values-spec-function description) declared
             (values-spec-preconditions description) term direction signed? symbol feasibility
             (string-append (declarations-of exported) (assertions-of exported)) feasibility-body))

;; A script's declarations, and its assertions, each as the commands' own text.
(define (commands-of script wanted?)
  (define out (open-output-string))
  (define previous 0)
  (for ([entry (in-list (smtlib-commands script))])
    (define original (substring script previous (cdr entry)))
    (set! previous (cdr entry))
    (when (and (pair? (car entry)) (wanted? (caar entry)))
      (display (string-trim original) out) (newline out)))
  (string->immutable-string (get-output-string out)))
(define (declarations-of script) (commands-of script (lambda (head) (member head '("declare-const" "declare-fun")))))
(define (assertions-of script) (commands-of script (lambda (head) (equal? head "assert"))))

;; The objective, asked of a session's solver in place of a standalone one.
(define (objective_session_check session value [timeout 10])
  (unless (objective? value) (raise-argument-error 'check "objective query" value))
  (session_objective session (objective-body value) (objective-direction value) (objective-symbol value)
                     (cons (cons (objective-symbol value) (term-width (objective-term value)))
                           (expected-inputs (objective-inputs value)))
                     timeout (objective-feasibility-body value)))

;;==============================================================================
;; Scopes

;; The assertions the lowering makes of `preconditions` alone, over one
;; function: its exported SMT-LIB.
(define (assumed dialect module function inputs preconditions)
  (define manifest
    (for/fold ([manifest (context-manifest dialect 1)])
              ([(key value) (in-hash (hash-set (hash-remove (hash-remove (spec-manifest (make_values_spec function inputs preconditions))
                                                                        'result_symbol)
                                                           'defined_symbol)
                                              'mode "assume"))])
      (hash-set manifest key value)))
  (define-values (lowered _members) (run-lowering module manifest))
  (to_smtlib (parse_stock_module lowered module)))

;; Opens a scope on `session`: the function's inputs are declared in its
;; solver, once, and stay declared until the scope is closed.
(define (make_smt_scope session dialect module function inputs)
  (check-context 'smt_scope dialect module)
  (define description (make_values_spec function inputs '()))
  (define declared (values-spec-inputs description))
  (define script (assumed dialect module (values-spec-function description) declared '()))
  (unless (equal? (smtlib-declarations script) (expected-inputs declared))
    (builder-error 'smt_scope "internal error: the exported SMT-LIB does not declare exactly the scope's inputs:\n~a" script))
  (define declarations (declarations-of script))
  (define opened (session_scope_open session declarations))
  (unless (eq? (solver_result_status opened) 'ok)
    (builder-error 'smt_scope "cannot open a scope: ~a (~a)" (solver_result_status opened) (solver_result_diagnostics opened)))
  (scope session dialect module (values-spec-function description) declared declarations (list '())))

(define (scope-result who answer)
  (unless (eq? (solver_result_status answer) 'ok)
    (builder-error who "the scope's solver failed: ~a (~a)" (solver_result_status answer) (solver_result_diagnostics answer))))

(define (scope_is_open value) (and (session_scope_depth (scope-session value)) #t))

;; Adds an assumption: it holds for every question asked until the frame it is
;; in is popped.
(define (scope_assert value assumption)
  (check-formula 'assert assumption)
  (define script (assumed (scope-dialect value) (scope-module value) (scope-function value) (scope-inputs value)
                          (list assumption)))
  (define assertions (assertions-of script))
  (scope-result 'assert (session_scope_assert (scope-session value) assertions))
  (define frames (scope-frames value))
  (set-scope-frames! value (cons (cons (cons assumption assertions) (car frames)) (cdr frames))))

(define (scope_push value)
  (scope-result 'push (session_scope_push (scope-session value)))
  (set-scope-frames! value (cons '() (scope-frames value))))

(define (scope_pop value)
  (scope-result 'pop (session_scope_pop (scope-session value)))
  (set-scope-frames! value (cdr (scope-frames value))))

(define (scope_close value)
  (session_scope_close (scope-session value))
  (set-scope-frames! value (list '())))

;; What is assumed now, outermost and earliest first.
(define (scope-assumed value)
  (append* (reverse (map reverse (scope-frames value)))))

;; The goal's assertion: the negation of the property and of every
;; operation's requirements, as a query's is.
(define (scope-goal value property)
  (check-formula 'check property)
  (assertions-of (query-smtlib (make_smt_query (scope-dialect value) (scope-module value) (scope-function value)
                                               (scope-inputs value) property '()))))

;; The question as one script: what the solver holds, and the goal. Run by
;; itself it gives the answer the scope gives.
(define (scope_goal_script value property)
  (string->immutable-string
   (string-append "(set-logic QF_BV)\n" (scope-declarations value)
                  (apply string-append (map cdr (scope-assumed value)))
                  (scope-goal value property) "(check-sat)\n")))

;; Whether `property` holds for every input that satisfies what the scope
;; assumes: 'unsat where it does, 'sat with a counterexample's inputs.
(define (scope_check value property [timeout 10])
  (session_scope_check (scope-session value) (scope-goal value property)
                       (expected-inputs (scope-inputs value)) timeout))

;; Several questions, each as `scope_check` asks one, their formulas lowered
;; together: one pass of the tools for all of them, where asking them one at a
;; time takes a pass each. Gives each question's script and answer, in order.
;; A question the scope did not live to be asked (an earlier one ended its
;; solver) is answered 'closed-session.
(define (scope_check_all value properties [timeout 10])
  (define claims (entries 'check_all properties))
  (for ([claim (in-list claims)]) (check-formula 'check_all claim))
  (define goals
    (if (null? claims)
        '()
        (for/list ([member (in-list (batch-queries
                                     (make-batch (scope-dialect value) (scope-module value)
                                                 (for/list ([claim (in-list claims)])
                                                   (make_spec (scope-function value) (scope-inputs value) claim '()))
                                                 #f)))])
          (assertions-of (query-smtlib member)))))
  (define held
    (string-append "(set-logic QF_BV)\n" (scope-declarations value)
                   (apply string-append (map cdr (scope-assumed value)))))
  (define expected (expected-inputs (scope-inputs value)))
  (list->treelist
   (for/list ([goal (in-list goals)])
     (treelist (string->immutable-string (string-append held goal "(check-sat)\n"))
               (if (scope_is_open value)
                   (session_scope_check (scope-session value) goal expected timeout)
                   (solver-result 'closed-session '()
                                  "the scope's solver ended on an earlier question of this list"
                                  '() 0.0))))))

(define (scope_inputs value)
  (list->treelist (for/list ([input (in-list (scope-inputs value))])
                   (treelist (car (term-args input)) (term-width input)))))
(define (scope_assumptions value)
  (list->treelist (for/list ([entry (in-list (scope-assumed value))])
                   (string->immutable-string (render-formula (car entry))))))

;; 'optimum with the symbol's value first, then the inputs'; 'infeasible with a
;; core where named preconditions cannot hold together, or with none where no
;; input satisfies the preconditions and nothing says which.
(define (objective_check value [executable #f] [timeout 10] [arguments '()])
  (unless (objective? value) (raise-argument-error 'check "objective query" value))
  (define core
    (and (objective-feasibility value)
         (run_solver_core (objective-feasibility value) executable timeout arguments)))
  (cond
    [(and core (not (memq (solver_result_status core) '(feasible unknown timeout)))) core]
    [else
     (define answer
       (run_solver_objective (objective-smtlib value)
                             (cons (cons (objective-symbol value) (term-width (objective-term value)))
                                   (expected-inputs (objective-inputs value)))
                             executable timeout arguments))
     (if (eq? (solver_result_status answer) 'unsat)
         (solver-result 'infeasible '() (solver_result_diagnostics answer) (solver_result_command answer)
                        (solver_result_seconds answer))
         answer)]))

;; The optimum as the number asked for: the symbol's residue with the sign bit
;; flipped back and read as two's complement where the objective is signed.
(define (objective_value value residue)
  (define width (term-width (objective-term value)))
  (cond
    [(objective-signed? value)
     (define plain (bitwise-xor residue (expt 2 (sub1 width))))
     (if (>= plain (expt 2 (sub1 width))) (- plain (expt 2 width)) plain)]
    [else residue]))

(define (objective_inputs value)
  (list->treelist (for/list ([input (in-list (objective-inputs value))])
                   (treelist (car (term-args input)) (term-width input)))))
(define (objective_assumptions value)
  (list->treelist (map (compose string->immutable-string render-assumption) (objective-preconditions value))))

(define (make_smt_batch dialect module specs)
  (make-batch dialect module specs #f))
(define (make_smt_values_batch dialect module specs)
  (make-batch dialect module specs #t))
(define (make_smt_values_query dialect module function inputs preconditions)
  (car (values-batch-queries
        (make_smt_values_batch dialect module
                              (list (make_values_spec function inputs preconditions))))))

(define (batch-requests value)
  (for/list ([member (in-list (batch-queries value))])
    (list (query-smtlib member) (expected-inputs (query-inputs member)) (query-feasibility-body member))))

(define (batch_check value [executable #f] [timeout 10] [arguments '()] [overall-timeout #f])
  (list->treelist (run_solver_batch (batch-requests value) executable timeout arguments overall-timeout)))
(define (batch_session_check session value [timeout 10] [overall-timeout #f])
  (list->treelist (session_check_batch session (batch-requests value) timeout overall-timeout)))
(define (query_session_check session value [timeout 10] [overall-timeout #f])
  (session_check session (query-smtlib value) (expected-inputs (query-inputs value))
                 (if overall-timeout (min timeout overall-timeout) timeout)
                 (query-feasibility-body value)))
(define (values_query_check session value limit [timeout 10])
  (session_values session (values-query-smtlib value) (values-query-result-name value)
                  (values-query-result-width value) limit timeout (values-query-defined-name value)))
(define (values_query_inputs value)
  (list->treelist (for/list ([input (in-list (values-query-inputs value))])
                   (treelist (car (term-args input)) (term-width input)))))
(define (values_query_assumptions value)
  (list->treelist (map (compose string->immutable-string render-assumption) (values-query-preconditions value))))

(define (query_inputs value)
  (list->treelist
   (for/list ([input (in-list (query-inputs value))])
     (treelist (car (term-args input)) (term-width input)))))

;; The assumptions under which an `unsat` answer holds, as readable text.
(define (query_assumptions value)
  (list->treelist (map (compose string->immutable-string render-assumption) (query-preconditions value))))

(define (query_check value [executable #f] [timeout 10] [arguments '()])
  (unless (query? value) (raise-argument-error 'check "query" value))
  ;; Named preconditions are asked first whether they can hold together; where
  ;; they cannot, that is the answer, and its names say which.
  (define core
    (and (query-feasibility value) (run_solver_core (query-feasibility value) executable timeout arguments)))
  (if (and core (not (memq (solver_result_status core) '(feasible unknown timeout))))
      core
      (run-query value executable timeout arguments)))

(define (run-query value executable timeout arguments)
  (run_solver (query-smtlib value)
              (for/list ([input (in-list (query-inputs value))])
                (cons (car (term-args input)) (term-width input)))
              executable timeout arguments))
