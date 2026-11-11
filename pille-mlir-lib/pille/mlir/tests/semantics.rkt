#lang racket/base

(require json
         rackunit
         racket/list
         racket/treelist
         "../../private/mlir/schema.rkt"
         "../../private/mlir/semantics.rkt")

;; Pure descriptor tests: nothing here may need MLIR, the plugin, or a solver.
(define (without-tools thunk)
  (parameterize ([current-environment-variables
                  (environment-variables-copy (current-environment-variables))])
    (for ([name '(#"PATH" #"PILLE_MLIR_PREFIX" #"PILLE_LLVM_PREFIX" #"PILLE_MLIR_SMT_PLUGIN" #"PILLE_Z3")])
      (environment-variables-set! (current-environment-variables) name #f))
    (environment-variables-set! (current-environment-variables) #"PATH" #"")
    (thunk)))

(define i32 (type_is "i32"))
(define i64 (type_is "i64"))
(define either (any_of (list i32 i64)))
(define shared (same "T" either))

(define (binary tag) (sem_binary tag (sem_operand "lhs") (sem_operand "rhs")))
(define (model value) (make_semantics '() (list (list "out" value))))
(define (operation semantics #:lhs [lhs shared] #:rhs [rhs shared] #:out [out shared])
  (operation_def "op" (list (list "lhs" lhs) (list "rhs" rhs)) (list (list "out" out)) '()
                 semantics))

(define (semantic-failure? pattern)
  (lambda (error)
    (and (exn:fail? error) (regexp-match? pattern (exn-message error)))))

(test-case "semantics round-trip deterministically without MLIR or a solver"
  (without-tools
   (lambda ()
     (define semantics
       (make_semantics
        (list (list "scaled" (sem_binary 'mul (sem_operand "lhs")
                                         (sem_const_like 3 (sem_operand "lhs"))))
              (list "biased" (sem_binary "sub" (sem_local 0) (sem_const_width -1 32))))
        (list (list "out" (sem_binary 'add (sem_local 1) (sem_operand "rhs"))))))
     (define original
       (make_dialect "sample"
                     (list (operation semantics #:lhs i32 #:rhs i32 #:out i32)
                           (operation_def "plain" '() '()))))
     (define serialized (dialect_serialize original))
     (define restored (dialect_deserialize serialized))
     (check-true (immutable? serialized))
     (check-equal? (dialect_serialize restored) serialized)
     (check-equal? (dialect_irdl restored) (dialect_irdl original))
     (check-equal? (treelist->list (smt_operation_names restored)) '("sample.op"))
     (check-equal? (unmodeled_operation_names restored) '("sample.plain"))
     (check-equal? (operation_models restored) (operation_models original))
     ;; Semantics do not affect the structural schema.
     (check-equal? (dialect_irdl original)
                   (dialect_irdl
                    (make_dialect "sample"
                                  (list (operation #f #:lhs i32 #:rhs i32 #:out i32)
                                        (operation_def "plain" '() '())))))
     (for ([definition (list (operation semantics #:lhs i32 #:rhs i32 #:out i32)
                             (operation #f))])
       (define text (member_serialize definition))
       (check-equal? (member_serialize (member_deserialize text)) text)))))

(test-case "the serialized form is versioned and version 1 stays readable"
  (define written (string->jsexpr (dialect_serialize (make_dialect "sample" (list (operation #f))))))
  (check-equal? (cadr written) 2)
  ;; Schema-only operations carry an explicit null in version 2.
  (check-equal? (last (car (cadr (cadddr written)))) (json-null))
  (define version-1
    "[\"pille-irdl\",1,\"dialect\",[\"sample\",[[\"operation\",\"op\",[[\"value\",[\"type-is\",\"i32\"]]],[[\"out\",[\"type-is\",\"i32\"]]],[]]]]]")
  (define restored (dialect_deserialize version-1))
  (check-equal? (treelist->list (operation_names restored)) '("sample.op"))
  (check-equal? (treelist->list (smt_operation_names restored)) '())
  (check-equal? (unmodeled_operation_names restored) '("sample.op"))
  ;; Reading version 1 and writing it back upgrades the envelope only.
  (check-equal? (cadr (string->jsexpr (dialect_serialize restored))) 2)
  (check-equal? (dialect_irdl restored)
                (dialect_irdl (dialect_deserialize (dialect_serialize restored))))
  ;; The field count is tied to the version in both directions.
  (check-exn #rx"invalid serialized dialect member"
             (lambda ()
               (member_deserialize "[\"pille-irdl\",1,\"member\",[\"operation\",\"op\",[],[],[],null]]")))
  (check-exn #rx"invalid serialized dialect member"
             (lambda ()
               (member_deserialize "[\"pille-irdl\",2,\"member\",[\"operation\",\"op\",[],[],[]]]")))
  (check-not-exn
   (lambda ()
     (member_deserialize "[\"pille-irdl\",2,\"member\",[\"operation\",\"op\",[],[],[],null]]"))))

(test-case "deserialization validates semantics instead of trusting JSON"
  (define (member-text semantics)
    (format "[\"pille-irdl\",2,\"member\",[\"operation\",\"op\",[[\"value\",[\"type-is\",\"i32\"]]],[[\"out\",[\"type-is\",\"i32\"]]],[],~a]]"
            semantics))
  (check-not-exn
   (lambda () (member_deserialize (member-text "[[],[[\"out\",[\"operand\",\"value\"]]]]"))))
  (for ([semantics '("[[],[[\"out\",[\"shift\",[\"operand\",\"value\"]]]]]"
                     "[[],[[\"out\",[\"const\",\"1.5\",[\"width\",32]]]]]"
                     "[[],[[\"out\",[\"const\",1,[\"width\",32]]]]]"
                     "[[],[[\"out\",[\"const\",\"1\",[\"like\",\"value\"]]]]]"
                     "[[],[[\"out\",[\"const\",\"1\",[\"wide\",32]]]]]"
                     "[[]]"
                     "\"text\"")])
    (check-exn #rx"invalid serialized SMT semantics"
               (lambda () (member_deserialize (member-text semantics))) semantics))
  ;; A literal may take the width of any expression, or of the result.
  (for ([target '("[\"add\",[\"operand\",\"value\"],[\"operand\",\"value\"]]"
                  "[\"result\",\"out\"]")])
    (define text
      (member-text (format "[[],[[\"out\",[\"const\",\"-1\",[\"like\",~a]]]]]" target)))
    (check-equal? (member_serialize (member_deserialize text)) text))
  (check-exn #rx"unknown operand reference missing"
             (lambda () (member_deserialize (member-text "[[],[[\"out\",[\"operand\",\"missing\"]]]]"))))
  (check-exn #rx"unknown operand reference missing"
             (lambda ()
               (member_deserialize
                (member-text "[[],[[\"out\",[\"const\",\"1\",[\"like\",[\"operand\",\"missing\"]]]]]]"))))
  (check-exn #rx"unsupported bitvector width 12"
             (lambda ()
               (member_deserialize (member-text "[[],[[\"out\",[\"const\",\"1\",[\"width\",12]]]]]"))))
  (check-exn #rx"local 0 is used before its definition"
             (lambda () (member_deserialize (member-text "[[],[[\"out\",[\"local\",0]]]]")))))

(test-case "literals have an explicit range and a canonical value"
  (for ([width supported-widths])
    (check-equal? (normalize-literal -1 width) (sub1 (expt 2 width)))
    (check-equal? (normalize-literal (sub1 (expt 2 width)) width) (sub1 (expt 2 width)))
    (check-equal? (normalize-literal (- (expt 2 (sub1 width))) width) (expt 2 (sub1 width)))
    (check-false (normalize-literal (expt 2 width) width))
    (check-false (normalize-literal (- (add1 (expt 2 (sub1 width)))) width)))
  (check-false (normalize-literal 1/2 8))
  ;; Equal residues are equal descriptors.
  (check-equal? (sem_const_width -1 8) (sem_const_width 255 8))
  (check-exn #rx"literal 256 does not fit in 8 bits" (lambda () (sem_const_width 256 8)))
  (check-exn #rx"literal -129 does not fit in 8 bits" (lambda () (sem_const_width -129 8)))
  (check-exn #rx"unsupported bitvector width 7" (lambda () (sem_const_width 1 7)))
  (check-exn #rx"does not fit in any supported width"
             (lambda () (sem_const_like (expt 2 64) (sem_operand "lhs"))))
  ;; A width-relative literal keeps its written value until instantiation.
  (check-equal? (cdr (assq 'value
                           (hash->list
                            (cdar (operation_models
                                   (make_dialect "sample"
                                                 (list (operation (model (sem_const_like -1 (sem_result "out")))))))))))
                '("const" "-1" ("like" ("result")))))

(test-case "references, assignments, and coverage are validated"
  (check-exn (semantic-failure? #rx"unknown operand reference other")
             (lambda () (operation (model (sem_operand "other")))))
  (check-exn (semantic-failure? #rx"assignment to unknown result other")
             (lambda () (operation (make_semantics '() (list (list "other" (binary 'add)))))))
  (check-exn (semantic-failure? #rx"cannot assign to operand lhs")
             (lambda () (operation (make_semantics '() (list (list "lhs" (binary 'add)))))))
  (check-exn (semantic-failure? #rx"duplicate assignment to result out")
             (lambda ()
               (operation (make_semantics '() (list (list "out" (binary 'add))
                                                    (list "out" (binary 'sub)))))))
  (check-exn (semantic-failure? #rx"result out is never assigned")
             (lambda () (operation (make_semantics '() '()))))
  (check-exn (semantic-failure? #rx"result out cannot be read by its own definition")
             (lambda () (operation (model (sem_binary 'add (sem_result "out") (sem_operand "lhs"))))))
  (check-exn (semantic-failure? #rx"local 1 is used before its definition")
             (lambda ()
               (operation (make_semantics (list (list "first" (sem_local 1))
                                                (list "second" (sem_operand "lhs")))
                                          (list (list "out" (sem_local 0)))))))
  ;; Failures identify the node at fault, for source locations during expansion.
  (define culprit (sem_operand "other"))
  (check-eq? (with-handlers ([exn:fail? semantic_error_node])
               (operation (model (sem_binary 'add (sem_operand "lhs") culprit))))
             culprit))

(test-case "the supported fragment has exactly one result and no attributes"
  (define value (list (list "value" i32)))
  (check-exn (semantic-failure? #rx"exactly one result is supported, but the operation declares 0")
             (lambda () (operation_def "op" value '() '() (make_semantics '() '()))))
  (check-exn (semantic-failure? #rx"exactly one result is supported, but the operation declares 2")
             (lambda ()
               (operation_def "op" value (list (list "first" i32) (list "second" i32)) '()
                              (make_semantics '() (list (list "first" (sem_operand "value"))
                                                        (list "second" (sem_operand "value")))))))
  (check-exn #rx"conflicting clauses.*attribute-dependent semantics are unsupported"
             (lambda ()
               (operation_def "op" value (list (list "out" i32))
                              (list (list "mode" (attribute_is "\"checked\"")))
                              (make_semantics '() (list (list "out" (sem_operand "value")))))))
  ;; A schema-only declaration with attributes is unaffected.
  (check-not-exn
   (lambda ()
     (operation_def "op" value (list (list "out" i32))
                    (list (list "mode" (attribute_is "\"checked\"")))))))

(test-case "a choice round-trips and its comparison and arms are width-checked"
  (define choice
    (sem_select (sem_operand "lhs") (sem_const_like 0 (sem_operand "lhs"))
                (sem_operand "rhs") (sem_operand "lhs")))
  (define original (make_dialect "sample" (list (operation (model choice)))))
  (check-equal? (dialect_serialize (dialect_deserialize (dialect_serialize original)))
                (dialect_serialize original))
  (check-exn (semantic-failure? #rx"the comparison of bv.if combines operand lhs \\(i32\\) with operand rhs \\(i64\\)")
             (lambda ()
               (operation (model (sem_select (sem_operand "lhs") (sem_operand "rhs")
                                             (sem_operand "lhs") (sem_operand "lhs")))
                          #:lhs i32 #:rhs i64 #:out i32)))
  (check-exn (semantic-failure? #rx"bv.if combines operand lhs \\(i32\\) with operand rhs \\(i64\\)")
             (lambda ()
               (operation (model (sem_select (sem_operand "lhs") (sem_operand "lhs")
                                             (sem_operand "lhs") (sem_operand "rhs")))
                          #:lhs i32 #:rhs i64 #:out i32))))

(test-case "requirements round-trip, and a model without any serializes as before"
  (define plain (model (sem_operand "lhs")))
  (define required
    (make_semantics '() (list (list "out" (sem_operand "lhs")))
                    (list (list (list (sem_operand "lhs") (sem_const_like 1 (sem_operand "lhs")))
                                (list (sem_operand "lhs") (sem_operand "rhs"))))))
  (define original (make_dialect "sample" (list (operation required))))
  (check-equal? (dialect_serialize (dialect_deserialize (dialect_serialize original)))
                (dialect_serialize original))
  (check-false (equal? (dialect_serialize original)
                       (dialect_serialize (make_dialect "sample" (list (operation plain))))))
  (check-exn (semantic-failure? #rx"a comparison of `requires` combines operand lhs \\(i32\\) with operand rhs \\(i64\\)")
             (lambda ()
               (operation (make_semantics '() (list (list "out" (sem_operand "lhs")))
                                          (list (list (list (sem_operand "lhs") (sem_operand "rhs")))))
                          #:lhs i32 #:rhs i64 #:out i32))))

(test-case "provably unequal widths and unsupported sorts fail during validation"
  (check-exn (semantic-failure? #rx"bv.add combines operand lhs \\(i32\\) with operand rhs \\(i64\\)")
             (lambda () (operation (model (binary 'add)) #:lhs i32 #:rhs i64 #:out i32)))
  (check-exn (semantic-failure? #rx"the assignment to out combines result out \\(i64\\) with operand lhs \\(i32\\)")
             (lambda () (operation (model (sem_operand "lhs")) #:lhs i32 #:rhs i32 #:out i64)))
  (check-exn (semantic-failure? #rx"bv.mul combines operand lhs \\(i32\\) with a 64-bit value")
             (lambda ()
               (operation (model (sem_binary 'mul (sem_operand "lhs") (sem_const_width 2 64)))
                          #:lhs i32 #:rhs i32 #:out i32)))
  (check-exn (semantic-failure? #rx"literal 300 does not fit any width of operand lhs \\(i8\\)")
             (lambda ()
               (operation (model (sem_const_like 300 (sem_operand "lhs")))
                          #:lhs (type_is "i8") #:rhs (type_is "i8") #:out (type_is "i8"))))
  (for ([unsupported (list (type_is "f32") (type_is "index") (type_is "i7")
                           (any_of (list (type_is "f32") (type_is "f64"))))])
    (check-exn (semantic-failure? #rx"rhs admits no supported bitvector type")
               (lambda () (operation (model (sem_operand "lhs")) #:lhs i32 #:rhs unsupported #:out i32))))
  (define word (type_def "word" (list (list "element" i32))))
  (check-exn (semantic-failure? #rx"lhs admits no supported bitvector type")
             (lambda ()
               (operation (model (sem_operand "lhs"))
                          #:lhs (parametric 'type #f "word" (list i32)) #:rhs i32 #:out i32)))
  (check-not-exn (lambda () word)))

(test-case "widths that only an instance can decide are deferred, not assumed equal"
  ;; Independent unions may choose different widths. The model is accepted,
  ;; and each concrete instance is checked by the lowering pass.
  (check-not-exn (lambda () (operation (model (binary 'add)) #:lhs either #:rhs either #:out either)))
  (check-not-exn (lambda () (operation (model (binary 'add))
                                       #:lhs (any_constraint) #:rhs (any_constraint)
                                       #:out (any_constraint))))
  ;; A union containing an unsupported type is fine while a supported one remains.
  (check-not-exn (lambda ()
                   (operation (model (sem_operand "lhs"))
                              #:lhs (any_of (list i32 (type_is "f32"))) #:rhs i32 #:out i32)))
  ;; The same shared variable is known equal for every instance.
  (check-not-exn (lambda () (operation (model (binary 'mul)))))
  ;; Disjoint unions can never agree, even though neither is a single type.
  (check-exn (semantic-failure? #rx"widths must be equal and are never coerced")
             (lambda ()
               (operation (model (binary 'add))
                          #:lhs (any_of (list (type_is "i8") (type_is "i16")))
                          #:rhs either #:out either))))

(test-case "the lowering manifest refers to operands by position"
  (define semantics
    (make_semantics (list (list "twice" (sem_binary 'add (sem_operand "rhs") (sem_operand "rhs"))))
                    (list (list "out" (sem_binary 'sub (sem_local 0) (sem_operand "lhs"))))))
  (define manifest (cdar (operation_models (make_dialect "sample" (list (operation semantics))))))
  (check-equal? (hash-ref manifest 'operands) '("lhs" "rhs"))
  (check-equal? (hash-ref manifest 'result) "out")
  (check-equal? (hash-ref manifest 'locals) '(("twice" ("add" ("operand" 1) ("operand" 1)))))
  (check-equal? (hash-ref manifest 'value) '("sub" ("local" 0) ("operand" 0)))
  (check-true (jsexpr? manifest)))
