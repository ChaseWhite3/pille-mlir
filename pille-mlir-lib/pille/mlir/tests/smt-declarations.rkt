#lang racket/base

(require json
         rackunit
         racket/file
         racket/list
         racket/runtime-path
         racket/string
         racket/treelist
         "../../private/mlir/schema.rkt")

;; Expansion tests for the `smt:` clause. Nothing here needs MLIR or a solver:
;; the environment is cleared to prove it.
(define-runtime-path fixtures "semantics")
(define (fixture name) (build-path fixtures name))

(define (without-tools thunk)
  (parameterize ([current-environment-variables
                  (environment-variables-copy (current-environment-variables))])
    (for ([name '(#"PILLE_MLIR_PREFIX" #"PILLE_LLVM_PREFIX" #"PILLE_Z3")])
      (environment-variables-set! (current-environment-variables) name #f))
    (environment-variables-set! (current-environment-variables) #"PATH" #"")
    (thunk)))

(define (expand-fixture filename)
  (define path (fixture filename))
  (parameterize ([current-namespace (make-base-namespace)]
                 [current-load-relative-directory fixtures]
                 [read-accept-reader #t])
    (expand (call-with-input-file path
              (lambda (input)
                (port-count-lines! input)
                (read-syntax path input))))))

;; Fixtures mark the line where the error must be reported.
(define (marked-line filename)
  (for/first ([line (in-list (file->lines (fixture filename)))]
              [number (in-naturals 1)]
              #:when (string-contains? line "// <- error"))
    number))

;; The serialized semantics of one operation: (list locals results).
(define (semantics-of dialect operation)
  (define members (cadr (cadddr (string->jsexpr (dialect_serialize dialect)))))
  (last (for/first ([definition (in-list members)]
                    #:when (equal? (cadr definition) operation))
          definition)))

(define (value-of dialect operation)
  (cadr (car (cadr (semantics-of dialect operation)))))

(define (operand-type dialect operation)
  (define members (cadr (cadddr (string->jsexpr (dialect_serialize dialect)))))
  (cadr (car (caddr (for/first ([definition (in-list members)]
                                #:when (equal? (cadr definition) operation))
                      definition)))))

(test-case "declaring semantics and reading descriptors needs no MLIR or solver"
  (without-tools
   (lambda ()
     (check-not-exn (lambda () (expand-fixture "valid.rhm")))
     (define arithmetic (dynamic-require (fixture "valid.rhm") 'arithmetic))
     (check-regexp-match #rx"irdl.operation @add" (dialect_irdl arithmetic))
     (check-equal? (treelist->list (smt_operation_names arithmetic))
                   '("arithmetic.add" "arithmetic.sub" "arithmetic.mul" "arithmetic.increment"
                     "arithmetic.minus_one" "arithmetic.square_of_sum" "arithmetic.forty_two"
                     "arithmetic.loose" "arithmetic.anything"))
     (check-equal? (unmodeled_operation_names arithmetic) '("arithmetic.opaque"))
     (check-equal? (value-of arithmetic "add") '("add" ("operand" "lhs") ("operand" "rhs")))
     (check-equal? (value-of arithmetic "sub") '("sub" ("operand" "lhs") ("operand" "rhs")))
     (check-equal? (value-of arithmetic "increment")
                   '("add" ("operand" "value") ("const" "1" ("like" ("operand" "value")))))
     (check-equal? (value-of arithmetic "minus_one") '("const" "-1" ("like" ("result" "out"))))
     ;; An explicit-width literal is stored as its canonical residue.
     (check-equal? (value-of arithmetic "forty_two") '("const" "42" ("width" 8)))
     (check-equal? (semantics-of arithmetic "square_of_sum")
                   '((("sum" ("add" ("operand" "lhs") ("operand" "rhs"))))
                     (("out" ("mul" ("local" 0) ("local" 0))))))
     (check-equal? (semantics-of arithmetic "opaque") (json-null))
     ;; The embedded descriptor reconstructs to the same value.
     (check-equal? (dialect_serialize (dialect_deserialize (dialect_serialize arithmetic)))
                   (dialect_serialize arithmetic)))))

(test-case "semantics do not change the generated structural schema"
  (define arithmetic (dynamic-require (fixture "valid.rhm") 'arithmetic))
  (define twin-add (dynamic-require (fixture "valid.rhm") 'twin_add))
  (define twin-sub (dynamic-require (fixture "valid.rhm") 'twin_sub))
  (check-false (regexp-match? #rx"smt|bv\\." (dialect_irdl arithmetic)))
  ;; Identical IRDL, different declared meanings.
  (check-equal? (dialect_irdl twin-add) (dialect_irdl twin-sub))
  (check-equal? (value-of twin-add "combine") '("add" ("operand" "lhs") ("operand" "rhs")))
  (check-equal? (value-of twin-sub "combine") '("sub" ("operand" "lhs") ("operand" "rhs"))))

(test-case "imported semantic macros keep their definition-site bindings"
  (define hygienic (dynamic-require (fixture "hygiene.rhm") 'hygienic))
  (define one '("const" "1" ("like" ("operand" "value"))))
  (define value '("operand" "value"))
  ;; macros.advance uses macros.step (1), not the consumer's step (2) or its
  ;; advance (a subtraction); the constraint alias is the definition site's too.
  (check-equal? (value-of hygienic "imported") `("add" ,value ,one))
  (check-equal? (car (operand-type hygienic "imported")) "same")
  ;; Nested expansion: advance(advance(value)), each through step.
  (check-equal? (value-of hygienic "nested")
                `("add" ("add" ,value ,one) ("const" "1" ("like" ("add" ,value ,one)))))
  ;; Macro-introduced locals and operands resolve to each other.
  (check-equal? (semantics-of hygienic "counted")
                `((("next" ("add" ,value ,one)))
                  (("out" ("add" ("local" 0) ("const" "1" ("like" ("local" 0))))))))
  ;; The consumer's own declarations use the consumer's bindings.
  (check-equal? (value-of hygienic "local")
                `("sub" ,value ("const" "2" ("like" ,value))))
  (check-equal? (operand-type hygienic "local") '("type-is" "i8"))
  ;; Use-site operand names reach a use-site expression through a macro.
  (check-equal? (value-of hygienic "supplied")
                '("sub" ("operand" "second") ("operand" "first")))
  ;; An operand shadows a same-spelled semantic macro in its own model.
  (check-equal? (value-of hygienic "shadowed")
                '("mul" ("operand" "step") ("operand" "advance"))))

(test-case "malformed semantics fail during expansion at the offending source line"
  (for ([case (in-list
               '(("unknown-reference.rhm.fail" #rx"unknown operand, result, or local reference")
                 ("local-before-definition.rhm.fail" #rx"unknown operand, result, or local reference")
                 ("capture.rhm.fail" #rx"unknown operand, result, or local reference")
                 ("arity.rhm.fail" #rx"bv.add: expected 2 arguments, received 3")
                 ("assign-operand.rhm.fail" #rx"cannot assign to operand lhs; assign to a result")
                 ("unassigned.rhm.fail" #rx"result out is never assigned")
                 ("duplicate-assignment.rhm.fail" #rx"duplicate assignment to result out")
                 ("multiple-results.rhm.fail" #rx"exactly one result is supported")
                 ("read-result.rhm.fail" #rx"result out cannot be read by its own definition")
                 ("width-mismatch.rhm.fail"
                  #rx"bv.mul combines operand lhs \\(i32\\) with operand rhs \\(i64\\); widths must be equal")
                 ("result-width.rhm.fail"
                  #rx"the assignment to out combines result out \\(i64\\) with operand lhs \\(i32\\)")
                 ("unsupported-sort.rhm.fail" #rx"lhs admits no supported bitvector type")
                 ("literal-width.rhm.fail" #rx"unsupported bitvector width 12")
                 ("literal-range.rhm.fail" #rx"literal 256 does not fit in 8 bits")
                 ("relative-literal-range.rhm.fail"
                  #rx"literal -129 does not fit any width of operand lhs \\(i8\\)")
                 ("bare-literal.rhm.fail" #rx"a bare literal has no width")
                 ("if-width-mismatch.rhm.fail"
                  #rx"bv.if combines operand lhs \\(i32\\) with operand rhs \\(i64\\); widths must be equal")
                 ("if-comparison-width.rhm.fail"
                  #rx"the comparison of bv.if combines operand lhs \\(i32\\) with operand rhs \\(i64\\)")
                 ("requires-shape.rhm.fail" #rx"expected `requires left == right \\|\\| ...`")
                 ("requires-width.rhm.fail"
                  #rx"a comparison of `requires` combines operand lhs \\(i32\\) with operand rhs \\(i64\\)")
                 ("if-shape.rhm.fail" #rx"bv.if: expected \\(left == right, then, else\\)")
                 ("duplicate-clause.rhm.fail" #rx"duplicate smt clause")
                 ("duplicate-attributes.rhm.fail" #rx"duplicate attributes clause")
                 ("attributes-conflict.rhm.fail"
                  #rx"conflicting clauses: SMT semantics cannot be attached to an operation with required attributes")
                 ("unknown-clause.rhm.fail" #rx"expected an attributes\\(...\\) clause or an smt: clause")
                 ("local-redefinition.rhm.fail" #rx"local name is already an operand, result, or local")
                 ("mixed-statement.rhm.fail"
                  #rx"expected `let name = expression`, `requires left == right`, or `result = expression`")))])
    (define filename (car case))
    (define line (marked-line filename))
    (check-not-false line filename)
    (define error
      (with-handlers ([exn:fail:syntax? values])
        (without-tools (lambda () (expand-fixture filename)))
        #f))
    (check-not-false error (format "~a expanded without an error" filename))
    (when error
      (check-regexp-match (cadr case) (exn-message error) filename)
      ;; The reported location is the marked line of the fixture itself.
      (check-regexp-match (regexp (string-append (regexp-quote filename) ":"
                                                 (number->string line) ":"))
                          (exn-message error)
                          filename))))
