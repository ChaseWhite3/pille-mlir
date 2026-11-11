#lang racket/base

(require rackunit
         racket/file
         racket/runtime-path
         racket/string
         "../../private/mlir/tools.rkt")

(define-runtime-path fixtures "declarations")
(define (fixture name) (build-path fixtures name))
(define (load-export filename name)
  (dynamic-require (fixture filename) name))

(define ((syntax-error-matching? pattern) error)
  (and (exn:fail:syntax? error) (regexp-match? pattern (exn-message error))))

(define (expand-fixture filename)
  (define path (fixture filename))
  (parameterize ([current-namespace (make-base-namespace)]
                 [current-load-relative-directory fixtures]
                 [read-accept-reader #t])
    (expand (call-with-input-file path
              (lambda (input) (read-syntax path input))))))

(define (operation-source name input-types result-types)
  (define arguments
    (for/list ([type (in-list input-types)] [index (in-naturals)])
      (format "%arg~a: ~a" index type)))
  (define operands
    (for/list ([index (in-range (length input-types))])
      (format "%arg~a" index)))
  (format "module { func.func @test(~a) { ~a\"~a\"(~a) : (~a) -> (~a) return } }"
          (string-join arguments ", ")
          (if (null? result-types) "" "%result = ")
          name
          (string-join operands ", ")
          (string-join input-types ", ")
          (string-join result-types ", ")))

(define (annotate-source type attribute)
  (format #<<MLIR
module {
  func.func @test(%value: ~a) {
    %result = "rhombus.annotate"(%value) {mode = ~a} : (~a) -> ~a
    return
  }
}
MLIR
          type attribute type type))

(test-case "declaration expansion and schema generation do not need MLIR"
  (parameterize ([current-environment-variables
                  (environment-variables-copy (current-environment-variables))]
                 [current-namespace (make-base-namespace)])
    (environment-variables-set! (current-environment-variables)
                                #"PILLE_MLIR_PREFIX" #"/pille-test/no-mlir-installed")
    (check-not-exn (lambda () (expand-fixture "valid.rhm")))
    (define generated (load-export "valid.rhm" 'generated))
    (check-regexp-match #rx"irdl.dialect @rhombus" generated)
    (check-regexp-match #rx"irdl.operation @add" generated)
    (check-equal? (load-export "valid.rhm" 'dialect_name) "rhombus")
    (check-equal? (load-export "valid.rhm" 'add_name) "rhombus.add")))

(test-case "unknown declaration and constraint bindings fail during expansion"
  (check-exn (syntax-error-matching? #rx"undeclared")
             (lambda () (expand-fixture "unknown-declaration.rhm.fail")))
  (check-exn (syntax-error-matching? #rx"MissingConstraint")
             (lambda () (expand-fixture "unknown-constraint.rhm.fail"))))

(test-case "invalid schemas fail during expansion, before executing module code"
  (for ([filename '("duplicate.rhm.fail" "invalid-reference.rhm.fail" "conflicting-share.rhm.fail"
                    "uppercase-type.rhm.fail" "unbounded-union.rhm.fail"
                    "overlapping-union.rhm.fail")]
        [pattern '(#rx"duplicate dialect member" #rx"unknown type reference"
                   #rx"equality variable T has conflicting constraints" #rx"invalid IRDL name"
                   #rx"unbounded any constraint" #rx"share parametric base")])
    (check-exn (syntax-error-matching? pattern) (lambda () (expand-fixture filename)) filename)))

;; These tests intentionally require MLIR: schema strings must load as real
;; runtime dialects and enforce the meaning of expansion's declarations.
(test-case "generated operation schema enforces both type sets and shared variables"
  (define chain (make_toolchain))
  (define definitions (load-export "valid.rhm" 'generated))
  (for ([type '("i32" "i64")])
    (check-not-exn
     (lambda ()
       (parse_module (operation-source "rhombus.add" (list type type) (list type))
                     definitions chain))))
  (for ([source (list (operation-source "rhombus.add" '("f32" "f32") '("f32"))
                      (operation-source "rhombus.add" '("i32" "i64") '("i32"))
                      (operation-source "rhombus.add" '("i32" "i32") '("i64")))])
    (check-exn #rx"mlir-opt failed" (lambda () (parse_module source definitions chain))))
  ;; Equal-looking constraints remain independent unless `same` requests sharing.
  (check-not-exn
   (lambda ()
     (parse_module (operation-source "rhombus.independent" '("i32" "i64") '())
                   definitions chain)))
  (check-not-exn
   (lambda ()
     (parse_module (operation-source "rhombus.narrow" '("i32") '("i32"))
                   definitions chain)))
  (check-exn #rx"mlir-opt failed"
             (lambda ()
               (parse_module (operation-source "rhombus.narrow" '("i64") '("i32"))
                             definitions chain))))

(test-case "generated custom types and attributes register and validate parameters"
  (define chain (make_toolchain))
  (define definitions (load-export "valid.rhm" 'generated))
  (define source (annotate-source "!rhombus.word<i32>" "#rhombus.mode<\"checked\">"))
  ;; Exercise the public dialect.module method as well as the low-level tools.
  (define printed ((load-export "valid.rhm" 'parse_program) source))
  (check-regexp-match #rx"!rhombus.word<i32>" printed)
  (check-regexp-match #rx"#rhombus.mode<\"checked\">" printed)
  (define module (parse_module source definitions chain))
  (check-regexp-match #rx"rhombus.annotate"
                      (module_ir (run_passes module "builtin.module(canonicalize)")))
  (for ([invalid (list (annotate-source "!rhombus.word<f32>" "#rhombus.mode<\"checked\">")
                       (annotate-source "!rhombus.word<i32>" "#rhombus.mode<\"unchecked\">")
                       (annotate-source "!rhombus.word<i64>" "#rhombus.mode<\"checked\">"))])
    (check-exn #rx"mlir-opt failed" (lambda () (parse_module invalid definitions chain)))))

(test-case "constraint enforestation applies operator precedence and explicit grouping"
  (define chain (make_toolchain))
  (define definitions (load-export "valid.rhm" 'generated))
  (for ([operation '("precedence" "grouped")]
        [accepted '("i32" "i64")]
        [rejected '("i64" "i32")])
    (define name (string-append "rhombus." operation))
    (check-not-exn
     (lambda ()
       (parse_module (operation-source name (list accepted) '()) definitions chain)))
    (check-exn #rx"mlir-opt failed"
               (lambda ()
                 (parse_module (operation-source name (list rejected) '()) definitions chain)))))

(test-case "imported declaration macros preserve definition-site constraint bindings"
  (define chain (make_toolchain))
  (define definitions (load-export "hygiene.rhm" 'generated))
  (check-not-exn
   (lambda ()
     (parse_module (operation-source "hygienic.add" '("i32" "i32") '("i32"))
                   definitions chain)))
  (check-exn #rx"mlir-opt failed"
             (lambda ()
               (parse_module (operation-source "hygienic.add" '("f64" "f64") '("f64"))
                             definitions chain)))
  (check-not-exn
   (lambda ()
     (parse_module (operation-source "hygienic.local" '("f64") '("f64"))
                   definitions chain)))
  (check-exn #rx"mlir-opt failed"
             (lambda ()
               (parse_module (operation-source "hygienic.local" '("i32") '("i32"))
                             definitions chain))))
