#lang racket/base

(require rackunit
         racket/file
         racket/runtime-path
         "../../private/mlir/tools.rkt")

(define-runtime-path public-api "../../mlir.rhm")

(define (without-tools thunk)
  (parameterize ([current-environment-variables
                  (environment-variables-copy (current-environment-variables))])
    (environment-variables-set! (current-environment-variables) #"PILLE_MLIR_PREFIX" #f)
    (environment-variables-set! (current-environment-variables) #"PILLE_LLVM_PREFIX" #f)
    (environment-variables-set! (current-environment-variables) #"PATH" #"")
    ;; and none of the usual places either
    (parameterize ([llvm-search-prefixes '()])
      (thunk))))

(test-case "import is independent of an installed toolchain"
  (without-tools
   (lambda ()
     (parameterize ([current-namespace (make-base-namespace)])
       (check-not-exn (lambda () (dynamic-require public-api #f))))
     (check-exn #rx"cannot find mlir-opt" make_toolchain))))

(test-case "an explicit prefix takes precedence and cannot fall back to PATH"
  (define missing (make-temporary-file "pille-mlir-missing-~a" 'directory))
  (dynamic-wind
    void
    (lambda ()
      (check-exn (lambda (exn)
                   (and (exn:fail? exn)
                        (regexp-match? #rx"cannot find" (exn-message exn))
                        (regexp-match? (regexp-quote (path->string missing))
                                       (exn-message exn))))
                 (lambda () (make_toolchain missing))))
    (lambda () (delete-directory/files missing))))

(test-case "MLIR prefix takes precedence over the LLVM fallback"
  (define missing (make-temporary-file "pille-mlir-prefix-~a" 'directory))
  (dynamic-wind
    void
    (lambda ()
      (parameterize ([current-environment-variables
                      (environment-variables-copy (current-environment-variables))])
        (environment-variables-set! (current-environment-variables) #"PILLE_MLIR_PREFIX"
                                    (path->bytes missing))
        (check-exn (regexp (regexp-quote (path->string missing))) make_toolchain)))
    (lambda () (delete-directory/files missing))))
