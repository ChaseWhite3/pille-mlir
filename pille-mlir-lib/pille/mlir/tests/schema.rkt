#lang racket/base

(require rackunit
         racket/treelist
         "../../private/mlir/schema.rkt")

(define integer (any_of (list (type_is "i32") (type_is "i64"))))
(define shared-integer (same "T" integer))
(define word (type_def "word" (list (list "element" integer))))
(define mode (attribute_def "mode" (list (list "value" (attribute_is "\"checked\"")))))
(define (result-operation value)
  (operation_def "produce" '() (list (list "result" value))))

(test-case "descriptions round-trip deterministically without an installed toolchain"
  (parameterize ([current-environment-variables
                  (environment-variables-copy (current-environment-variables))])
    (environment-variables-set! (current-environment-variables) #"PATH" #"")
    (environment-variables-set! (current-environment-variables) #"PILLE_MLIR_PREFIX" #f)
    (environment-variables-set! (current-environment-variables) #"PILLE_LLVM_PREFIX" #f)
    (define operation
      (operation_def "add"
                     (treelist (treelist "lhs" shared-integer) (treelist "rhs" shared-integer))
                     (treelist (treelist "sum" shared-integer))))
    (define original (make_dialect "sample" (treelist word mode operation)))
    (define serialized (dialect_serialize original))
    (define restored (dialect_deserialize serialized))
    (check-equal? (dialect_serialize restored) serialized)
    (check-equal? (dialect_irdl restored) (dialect_irdl original))
    (check-equal? (dialect_name restored) "sample")
    (check-true (immutable? serialized))
    (check-true (immutable? (dialect_irdl original)))
    (for ([value (list shared-integer
                       (all_of (list integer (type_is "i32")))
                       (parametric 'type #f "word" (list (any_constraint)))
                       (parametric "attribute" "sample" "mode" (list (attribute_is "\"checked\""))))])
      (define serialized-constraint (constraint_serialize value))
      (check-equal? (constraint_serialize (constraint_deserialize serialized-constraint))
                    serialized-constraint))
    (for ([value (list word mode operation)])
      (define serialized-member (member_serialize value))
      (check-equal? (member_serialize (member_deserialize serialized-member))
                    serialized-member))))

(test-case "caller-owned mutable strings cannot change a constructed description"
  (define name (string-copy "sample"))
  (define literal (string-copy "i32"))
  (define original (make_dialect name (list (result-operation (type_is literal)))))
  (define serialized (dialect_serialize original))
  (string-set! name 0 #\z)
  (string-set! literal 2 #\4)
  (check-equal? (dialect_name original) "sample")
  (check-equal? (dialect_serialize original) serialized)
  (check-equal? (dialect_irdl (dialect_deserialize serialized)) (dialect_irdl original)))

(test-case "operation metadata excludes type and attribute declarations"
  (define dialect
    (make_dialect "sample" (list word mode (result-operation integer)
                                  (operation_def "empty" '() '()))))
  (check-equal? (operation_name dialect "produce") "sample.produce")
  (check-equal? (treelist->list (operation_names dialect)) '("sample.produce" "sample.empty"))
  (check-exn #rx"unknown operation" (lambda () (operation_name dialect "word")))
  (check-exn #rx"unknown operation" (lambda () (operation_name dialect "missing"))))

(test-case "parametric references resolve forward and validate namespace, kind, and arity"
  (for ([namespace '(#f "sample")])
    (check-not-exn
     (lambda ()
       (make_dialect "sample"
                     (list (result-operation (parametric 'type namespace "word" (list integer)))
                           word)))))
  (check-exn #rx"unknown type reference: sample.missing"
             (lambda ()
               (make_dialect "sample"
                             (list (result-operation (parametric 'type #f "missing" '()))))))
  (check-exn #rx"outside this dialect"
             (lambda ()
               (make_dialect "sample"
                             (list word (result-operation (parametric 'type "other" "word" (list integer)))))))
  (check-exn #rx"is a attribute, expected a type"
             (lambda ()
               (make_dialect "sample"
                             (list mode (result-operation (parametric 'type #f "mode" (list integer)))))))
  (check-exn #rx"expects 1 parameters, received 0"
             (lambda ()
               (make_dialect "sample"
                             (list word (result-operation (parametric 'type #f "word" '()))))))
  (check-exn #rx"expects 1 parameters, received 2"
             (lambda ()
               (make_dialect "sample"
                             (list word (result-operation (parametric 'type #f "word" (list integer integer))))))))

(test-case "schema names and ports satisfy IRDL naming and uniqueness rules"
  (for ([invalid '("Upper" "_leading" "double__underscore")])
    (check-exn #rx"invalid IRDL name" (lambda () (make_dialect invalid '())))
    (check-exn #rx"invalid IRDL name" (lambda () (type_def invalid '())))
    (check-exn #rx"invalid IRDL name" (lambda () (attribute_def invalid '())))
    (check-exn #rx"invalid IRDL name" (lambda () (operation_def invalid '() '())))
    (check-exn #rx"invalid IRDL name"
               (lambda () (type_def "word" (list (list invalid integer))))))
  (check-exn #rx"duplicate dialect member"
             (lambda () (make_dialect "sample" (list (type_def "word" '()) (attribute_def "word" '())))))
  (check-exn #rx"duplicate parameter or port name"
             (lambda () (type_def "word" (list (list "element" integer) (list "element" integer)))))
  (check-exn #rx"duplicate operand/result name"
             (lambda () (operation_def "op" (list (list "value" integer)) (list (list "value" integer)))))
  (check-exn #rx"requires a type constraint"
             (lambda () (result-operation (same "T" (any_of (list integer (attribute_is "\"attribute\""))))))))

(test-case "shared keys are scoped to members and reject conflicting or nested self references"
  (check-not-exn
   (lambda ()
     (make_dialect "sample"
                   (list (type_def "first" (list (list "value" (same "T" (type_is "i32")))))
                         (type_def "second" (list (list "value" (same "T" (type_is "i64")))))))))
  (check-exn #rx"equality variable T has conflicting constraints"
             (lambda ()
               (make_dialect "sample"
                             (list (operation_def "conflicting"
                                                  (list (list "input" (same "T" (type_is "i32"))))
                                                  (list (list "output" (same "T" (type_is "i64")))))))))
  ;; Descriptor trees are immutable and finite. A same-key descendant cannot
  ;; equal its ancestor's constraint, so validation rejects it before emission.
  (for ([nested (list (same "T" (same "T" (any_constraint)))
                      (same "T" (any_of (list (type_is "i32") (same "T" (type_is "i64"))))))])
    (check-exn #rx"equality variable T has conflicting constraints"
               (lambda () (make_dialect "sample" (list (result-operation nested))))))
  (check-not-exn
   (lambda ()
     (make_dialect "sample"
                   (list (operation_def "aliases"
                                        (list (list "input" (same "T" (same "U" integer))))
                                        (list (list "output" (same "U" integer)))))))))

(test-case "serialized descriptors reject unknown versions, tags, and trailing data"
  ;; Versions 1 and 2 are readable; see semantics.rkt for their differences.
  (check-exn #rx"unsupported schema version"
             (lambda () (dialect_deserialize "[\"pille-irdl\",3,\"dialect\",[\"sample\",[]]]")))
  (check-exn #rx"unsupported schema version"
             (lambda () (dialect_deserialize "[\"pille-irdl\",0,\"dialect\",[\"sample\",[]]]")))
  (check-exn #rx"invalid serialized constraint"
             (lambda () (constraint_deserialize "[\"pille-irdl\",1,\"constraint\",[\"unknown\"]]")))
  (check-exn #rx"invalid serialized dialect member"
             (lambda () (member_deserialize "[\"pille-irdl\",1,\"member\",[\"unknown\",\"sample\"]]")))
  (check-exn #rx"invalid serialized JSON"
             (lambda () (dialect_deserialize "[not-json]")))
  (check-exn #rx"unexpected trailing content"
             (lambda ()
               (dialect_deserialize (string-append (dialect_serialize (make_dialect "sample" '())) " {}"))))
  ;; Decoding re-runs constructors and reference checks instead of trusting JSON.
  (check-exn #rx"invalid IRDL name"
             (lambda () (member_deserialize "[\"pille-irdl\",1,\"member\",[\"type\",\"Upper\",[]]]")))
  (check-exn #rx"unknown type reference"
             (lambda ()
               (dialect_deserialize
                "[\"pille-irdl\",1,\"dialect\",[\"sample\",[[\"operation\",\"op\",[],[[\"result\",[\"parametric\",\"type\",false,\"missing\",[]]]],[]]]]]"))))

(test-case "unbounded union alternatives fail even when wrapped or nested"
  (define i32 (type_is "i32"))
  (define i64 (type_is "i64"))
  (define any (any_constraint))
  (define unbounded-union (any_of (list any i32)))
  (define invalid
    (list unbounded-union
          (any_of (list any))
          (any_of (list (same "T" any) i32))
          (any_of (list (all_of (list any i32)) i64))
          ;; The outer all_of/ref can be bounded, but the nested union still
          ;; becomes an instruction that must satisfy the loader's restrictions.
          (all_of (list i32 unbounded-union))
          (parametric 'type #f "word" (list unbounded-union))))
  (for ([value (in-list invalid)])
    (check-exn #rx"any_of alternative has an unbounded any constraint"
               (lambda () (make_dialect "sample" (list word (result-operation value)))))))

(test-case "union alternatives cannot share a parametric base"
  (define word32 (parametric 'type #f "word" (list (type_is "i32"))))
  ;; An explicit reference to this namespace denotes the same base as #f.
  (define word64 (parametric 'type "sample" "word" (list (type_is "i64"))))
  (define invalid
    (list (any_of (list word32 word64))
          (any_of (list (same "T" word32) word64))
          (any_of (list (any_of (list word32 (type_is "i32"))) word64))
          (any_of (list (all_of (list word32 (any_constraint))) word64))))
  (for ([value (in-list invalid)])
    (check-exn #rx"any_of alternatives share parametric base sample.word"
               (lambda () (make_dialect "sample" (list word (result-operation value))))))
  (define mode-choice
    (any_of (list (parametric 'attribute #f "mode" (list (attribute_is "\"checked\"")))
                  (parametric 'attribute "sample" "mode" (list (any_constraint))))))
  (check-exn #rx"any_of alternatives share parametric base sample.mode"
             (lambda ()
               (make_dialect "sample"
                             (list mode (type_def "subject" (list (list "value" mode-choice))))))))

(test-case "bounded first intersections and distinct parametric bases remain loadable"
  (define i32 (type_is "i32"))
  (define i64 (type_is "i64"))
  (define any (any_constraint))
  (define other (type_def "other" (list (list "element" any))))
  (define word-any (parametric 'type #f "word" (list any)))
  (define valid
    (list any
          (all_of (list any i32)) ; unrestricted outside a union
          (any_of (list (all_of (list i32 any)) i64))
          (any_of (list word-any (parametric 'type #f "other" (list any))))
          ;; Parameters do not contribute bases to the surrounding union.
          (any_of (list word-any (parametric 'type #f "other" (list word-any))))
          ;; Put the union in the parameter rather than repeating its base.
          (parametric 'type #f "word" (list (any_of (list i32 i64))))))
  (for ([value (in-list valid)])
    (check-not-exn
     (lambda () (make_dialect "sample" (list word other (result-operation value)))))))
