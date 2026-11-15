#lang racket/base

(require json
         racket/file
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

(provide smt_input smt_result smt_const smt_binary
         smt_eq smt_not smt_and smt_or
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
                     [query? is_query]
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
;;   (term 'result () width)      the value returned by the selected function
;;   (term 'const (value) width)  a typed literal
;;   (term 'add|'sub|'mul (a b) width)
;;   (formula 'eq (a b)) (formula 'not (f)) (formula 'and fs) (formula 'or fs)
(struct term (tag args width) #:transparent)
(struct formula (tag args) #:transparent)

(struct query (module smtlib dialect function inputs property preconditions))
(struct spec (function inputs property preconditions) #:transparent)
(struct values-spec (function inputs preconditions) #:transparent)
(struct batch (module smtlib queries))
(struct values-batch (module smtlib queries))
(struct values-query (module smtlib dialect function inputs preconditions result-name result-width defined-name))

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

(define (check-formula who value)
  (unless (formula? value)
    (builder-error who "expected a Boolean predicate, received ~a; Boolean predicates and bitvectors are distinct sorts"
                   (describe-sort value))))

(define (smt_not value)
  (check-formula 'not value)
  (formula 'not (list value)))

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
    [(term 'result _ _) "result"]
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
    [(term 'result _ _) (list "result")]
    [(term 'const (list literal) width)
     (list "const" (number->string literal) (list "width" width))]
    [(term tag (list lhs rhs) _)
     (list (symbol->string tag) (term->manifest lhs inputs) (term->manifest rhs inputs))]))

(define (formula->manifest value inputs)
  (match value
    [(formula 'eq (list lhs rhs))
     (list "eq" (term->manifest lhs inputs) (term->manifest rhs inputs))]
    [(formula tag operands)
     (cons (symbol->string tag)
           (for/list ([operand (in-list operands)]) (formula->manifest operand inputs)))]))

(define (result-widths value)
  (match value
    [(term 'result _ width) (list width)]
    [(term _ arguments _) (append-map result-widths (filter term? arguments))]
    [(formula _ operands) (append-map result-widths operands)]))

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
  (define assumptions (entries 'smt_query preconditions))
  (for ([assumption (in-list assumptions)]) (check-formula 'smt_query assumption))
  (values declared assumptions))

;; Specs retain immutable property descriptors. Batch validation resolves their
;; references with an index in each error; native lowering checks signatures.
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

(define (spec-manifest value)
  (define-values (function declared property assumptions) (spec-fields value))
  (validate-inputs function declared assumptions)
  (when (spec? value) (check-formula 'smt_query property))
  (define widths (remove-duplicates (append-map result-widths
                                               (if property (cons property assumptions) assumptions))))
  (when (> (length widths) 1)
    (builder-error 'smt_query "the result is referenced with conflicting widths: ~a"
                   (string-join (map number->string widths) ", ")))
  (define base
    (hasheq 'function function
            'inputs (for/list ([input (in-list declared)])
                      (hasheq 'name (car (term-args input)) 'width (term-width input)))
            'result_width (if (null? widths) (json-null) (car widths))
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

;; TEMPORARY, for the acceptance comparison only, and removed with the native
;; plugin: with PILLE_MLIR_SMT_COMPARE naming a directory, every lowering is
;; also run through the plugin (PILLE_MLIR_SMT_PLUGIN), and both results, or
;; refusals, are recorded there with their inputs. The Rhombus result is the
;; one used either way.
(define compare-directory (getenv "PILLE_MLIR_SMT_COMPARE"))
(define compare-count 0)

;; TEMPORARY, with the same life: PILLE_MLIR_SMT_LOWERING=plugin answers with the
;; plugin's lowering alone, so that each can be timed and tested in turn.
(define (run-plugin module manifest)
  (define plugin (resolve_smt_plugin #f))
  (cond
    [(string? manifest) (values (run_smt_query_pass module plugin manifest) '())]
    [(eqv? (hash-ref manifest 'version #f) 2) (run_smt_batch_pass module plugin manifest)]
    [else (values (run_smt_query_pass module plugin (jsexpr->string manifest)) '())]))

(define (lower-manifest module manifest)
  (cond
    [compare-directory (compare-lowerings module manifest)]
    [(equal? (getenv "PILLE_MLIR_SMT_LOWERING") "plugin") (run-plugin module manifest)]
    [else (run-lowering module manifest)]))

(define (compare-lowerings module manifest)
  (define (attempt run)
    (with-handlers ([exn:fail? (lambda (error) (list 'error error))])
      (call-with-values run (lambda (text members) (list 'ok text members)))))
  (define (side result)
    (cond
      [(eq? (car result) 'error) (hasheq 'error (exn-message (cadr result)))]
      [else
       (with-handlers ([exn:fail? (lambda (error) (hasheq 'verify_error (exn-message error)))])
         (define verified (parse_stock_module (cadr result) module))
         (hasheq 'verified (module_ir verified)
                 'smtlib (to_smtlib verified)
                 'members (if (<= (length (caddr result)) 4)
                              (for/list ([member (in-list (caddr result))])
                                (module_ir (parse_stock_module member module)))
                              (length (caddr result)))))]))
  (define by-plugin (attempt (lambda () (run-plugin module manifest))))
  (define by-rhombus (attempt (lambda () (run-lowering module manifest))))
  (set! compare-count (add1 compare-count))
  (make-directory* compare-directory)
  (call-with-output-file
    (build-path compare-directory
                (format "~a-~a.json" (current-inexact-milliseconds) compare-count))
    (lambda (out)
      (write-json (hasheq 'ir (module_ir module) 'irdl (module_irdl module)
                          'manifest (if (string? manifest) manifest (jsexpr->string manifest))
                          'plugin (side by-plugin) 'rhombus (side by-rhombus))
                  out)))
  (if (eq? (car by-rhombus) 'error)
      (raise (cadr by-rhombus))
      (values (cadr by-rhombus) (caddr by-rhombus))))

;; Lowers a manifest given as JSON text, bypassing the manifest this module
;; derives from a dialect: for tests of what the lowering itself checks.
(define (smt_lower_text module manifest)
  (unless (is_module module) (raise-argument-error 'smt_lower_text "module" module))
  (unless (string? manifest) (raise-argument-error 'smt_lower_text "string?" manifest))
  (define-values (text _members) (lower-manifest module manifest))
  text)

(define (make_smt_query dialect module function inputs property preconditions [plugin #f])
  (check-context 'smt_query dialect module)
  (define description (make_spec function inputs property preconditions))
  (define manifest
    (for/fold ([manifest (context-manifest dialect 1)])
              ([(key value) (in-hash (spec-manifest description))])
      (hash-set manifest key value)))
  (define-values (lowered _members) (lower-manifest module manifest))
  (define verified (parse_stock_module lowered module))
  (define smtlib (to_smtlib verified))
  (unless (equal? (smtlib-declarations smtlib) (expected-inputs (spec-inputs description)))
    (builder-error 'smt_query "internal error: the exported SMT-LIB does not declare exactly the query's inputs:\n~a" smtlib))
  (query verified smtlib (dialect_name dialect) (spec-function description)
         (spec-inputs description) property (spec-preconditions description)))

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

(define (make-batch dialect module specifications plugin values?)
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
  (define-values (lowered standalone) (lower-manifest module manifest))
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
      ;; can verify the native printer's isolated module lazily, without adding
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
         (query member-module script (dialect_name dialect) function inputs property assumptions)])))
  ((if values? values-batch batch) verified text queries))

(define (make_smt_batch dialect module specs [plugin #f])
  (make-batch dialect module specs plugin #f))
(define (make_smt_values_batch dialect module specs [plugin #f])
  (make-batch dialect module specs plugin #t))
(define (make_smt_values_query dialect module function inputs preconditions [plugin #f])
  (car (values-batch-queries
        (make_smt_values_batch dialect module
                              (list (make_values_spec function inputs preconditions)) plugin))))

(define (batch-requests value)
  (for/list ([member (in-list (batch-queries value))])
    (list (query-smtlib member) (expected-inputs (query-inputs member)))))

(define (batch_check value [executable #f] [timeout 10] [arguments '()] [overall-timeout #f])
  (list->treelist (run_solver_batch (batch-requests value) executable timeout arguments overall-timeout)))
(define (batch_session_check session value [timeout 10] [overall-timeout #f])
  (list->treelist (session_check_batch session (batch-requests value) timeout overall-timeout)))
(define (query_session_check session value [timeout 10] [overall-timeout #f])
  (session_check session (query-smtlib value) (expected-inputs (query-inputs value))
                 (if overall-timeout (min timeout overall-timeout) timeout)))
(define (values_query_check session value limit [timeout 10])
  (session_values session (values-query-smtlib value) (values-query-result-name value)
                  (values-query-result-width value) limit timeout (values-query-defined-name value)))
(define (values_query_inputs value)
  (list->treelist (for/list ([input (in-list (values-query-inputs value))])
                   (treelist (car (term-args input)) (term-width input)))))
(define (values_query_assumptions value)
  (list->treelist (map render_formula (values-query-preconditions value))))

(define (query_inputs value)
  (list->treelist
   (for/list ([input (in-list (query-inputs value))])
     (treelist (car (term-args input)) (term-width input)))))

;; The assumptions under which an `unsat` answer holds, as readable text.
(define (query_assumptions value)
  (list->treelist (map render_formula (query-preconditions value))))

(define (query_check value [executable #f] [timeout 10] [arguments '()])
  (unless (query? value) (raise-argument-error 'check "query" value))
  (run_solver (query-smtlib value)
              (for/list ([input (in-list (query-inputs value))])
                (cons (car (term-args input)) (term-width input)))
              executable timeout arguments))
