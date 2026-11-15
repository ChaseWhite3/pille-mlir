#lang racket/base
;; The lowering's own text (MLIR's generic form) for one recorded request: MODULE IRDL MANIFEST.
(require racket/file pille/private/mlir/tools)
(define lower_text (dynamic-require '(lib "pille/private/mlir/lower.rhm") 'lower_text))
(define arguments (current-command-line-arguments))
(define module (parse_module (file->string (vector-ref arguments 0)) (file->string (vector-ref arguments 1)) (make_toolchain)))
(define-values (text _members) (lower_text (module_generic module) (file->string (vector-ref arguments 2))))
(display text)
