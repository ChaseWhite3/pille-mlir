#lang racket/base

(require racket/file
         "../../private/mlir/tools.rkt")

(provide smt_plugin)

;; The SMT tests need the native query plugin. PILLE_MLIR_SMT_PLUGIN selects an
;; existing build; otherwise the plugin is built once per test process, from
;; the package's sources and against the toolchain under test, into a
;; temporary directory that is removed when the process exits. Nothing is
;; reused from an earlier session, and a failed build is a test failure.
(define built #f)

(define (smt_plugin)
  (cond
    [(getenv "PILLE_MLIR_SMT_PLUGIN") (resolve_smt_plugin)]
    [built built]
    [else
     (define directory (make-temporary-file "pille-smt-plugin-~a" 'directory))
     (plumber-add-flush! (current-plumber)
                         (lambda (_handle) (delete-directory/files directory #:must-exist? #f)))
     (set! built (build_smt_plugin directory (make_toolchain)))
     built]))
