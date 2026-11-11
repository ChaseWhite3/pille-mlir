#lang racket/base

(require racket/file racket/path racket/runtime-path racket/string racket/system
         racket/treelist
         "temporary.rkt")

(provide (rename-out [toolchain? is_toolchain]
                     [make-toolchain make_toolchain]
                     [mlir-module? is_module]
                     [parse-module parse_module]
                     [mlir-module-ir module_ir]
                     [mlir-module-irdl module_irdl]
                     [run-smt-query-pass run_smt_query_pass]
                     [parse-stock-module parse_stock_module]
                     [resolve-smt-plugin resolve_smt_plugin]
                     [build-smt-plugin build_smt_plugin]
                     [run-passes run_passes]
                     [to-llvm-ir to_llvm_ir]
                     [to-bitcode to_bitcode]
                     [to-smtlib to_smtlib]))

;; The toolchain is captured when a module is created: subsequent environment
;; changes cannot silently switch compiler installations halfway through lowering.
(struct toolchain (bin dialect-plugins pass-plugins))
(struct mlir-module (ir irdl toolchain))

(define (executable-name name)
  (if (eq? (system-type) 'windows) (string-append name ".exe") name))

(define (check-tool path name)
  (unless (and path (file-exists? path))
    (raise-user-error 'pille/mlir
                     "cannot find ~a; set PILLE_MLIR_PREFIX (or PILLE_LLVM_PREFIX) to an LLVM installation containing MLIR tools"
                     (or path name)))
  path)

(define (plugin-paths paths)
  (define entries (if (treelist? paths) (treelist->list paths) paths))
  (unless (and (list? entries) (andmap path-string? entries))
    (raise-argument-error 'make_toolchain "list or treelist of paths" paths))
  (for/list ([entry (in-list entries)])
    (define path (path->complete-path entry))
    (unless (file-exists? path)
      (raise-user-error 'pille/mlir "cannot find plugin: ~a" path))
    path))

(define (make-toolchain [prefix #f] [dialect-plugins '()] [pass-plugins '()])
  (unless (or (not prefix) (path-string? prefix))
    (raise-argument-error 'make_toolchain "path-string? or #f" prefix))
  (define selected-prefix
    (or prefix (getenv "PILLE_MLIR_PREFIX") (getenv "PILLE_LLVM_PREFIX")))
  (define executable (executable-name "mlir-opt"))
  (define opt
    (check-tool
     (if selected-prefix
         (build-path selected-prefix "bin" executable)
         (find-executable-path executable))
     executable))
  (toolchain (path-only (path->complete-path opt))
             (plugin-paths dialect-plugins) (plugin-paths pass-plugins)))

(define (tool-path chain name)
  (define executable (executable-name name))
  (check-tool (build-path (toolchain-bin chain) executable) executable))

(define (run-tool chain name input arguments #:irdl [irdl ""] #:binary? [binary? #f]
                  #:pass-plugins [extra-plugins '()]
                  #:in-directory [extra-arguments (lambda (_directory) '())])
  ;; Files avoid pipe-buffer deadlocks for large modules and diagnostics. Run
  ;; directly, without a shell, so paths and pipelines remain literal arguments.
  (define executable (tool-path chain name))
  (define directory (make-work-directory "pille-mlir-~a"))
  (dynamic-wind
    void
    (lambda ()
      (define source (build-path directory "input.mlir"))
      (define output (build-path directory "output"))
      (define diagnostics (build-path directory "diagnostics"))
      (define definitions (build-path directory "dialects.mlir"))
      (display-to-file input source #:exists 'truncate)
      (unless (equal? irdl "")
        (display-to-file irdl definitions #:exists 'truncate))
      (define registration-args
        (if (equal? name "mlir-opt")
            (append
             (for/list ([path (in-list (toolchain-dialect-plugins chain))])
               (string-append "--load-dialect-plugin=" (path->string path)))
             (for/list ([path (in-list (append (toolchain-pass-plugins chain) extra-plugins))])
               (string-append "--load-pass-plugin=" (path->string path)))
             (if (equal? irdl "") '()
                 (list (string-append "--irdl-file=" (path->string definitions)))))
            '()))
      (define ok?
        ;; File-backed stdin gives stable <stdin> locations without changing the
        ;; working directory: relative paths in pass options belong to the caller.
        (call-with-input-file source
          (lambda (input-port)
            (call-with-output-file diagnostics
              (lambda (output-port)
                (parameterize ([current-input-port input-port]
                               [current-output-port output-port]
                               [current-error-port output-port])
                  (apply system* executable
                         (append registration-args arguments (extra-arguments directory)
                                 (list "-" "-o" (path->string output))))))))))
      (unless ok?
        (raise-user-error 'pille/mlir "~a failed:\n~a" name (file->string diagnostics)))
      (if binary?
          (bytes->immutable-bytes (file->bytes output))
          (string->immutable-string (file->string output))))
    (lambda () (delete-directory/files directory))))

(define (parse-module source [irdl ""] [chain (make-toolchain)])
  (unless (string? source) (raise-argument-error 'parse-module "string?" source))
  (unless (string? irdl) (raise-argument-error 'parse-module "string?" irdl))
  (unless (toolchain? chain) (raise-argument-error 'parse-module "toolchain?" chain))
  (define definitions (string->immutable-string irdl))
  (mlir-module (run-tool chain "mlir-opt" source '("--verify-each" "--mlir-print-debuginfo") #:irdl definitions)
               definitions chain))

(define (run-passes module pipeline)
  (unless (mlir-module? module) (raise-argument-error 'run-passes "mlir-module?" module))
  (unless (string? pipeline) (raise-argument-error 'run-passes "string?" pipeline))
  (mlir-module
   (run-tool (mlir-module-toolchain module) "mlir-opt" (mlir-module-ir module)
             (list "--verify-each" "--mlir-print-debuginfo"
                   (string-append "--pass-pipeline=" pipeline))
             #:irdl (mlir-module-irdl module))
   (mlir-module-irdl module) (mlir-module-toolchain module)))

;; Translation requires LLVM-translatable dialects. Lowering is deliberately
;; explicit: tensor, memref, vector, GPU, etc. need different pipelines.
(define (to-llvm-ir module)
  (unless (mlir-module? module) (raise-argument-error 'to-llvm-ir "mlir-module?" module))
  (run-tool (mlir-module-toolchain module) "mlir-translate" (mlir-module-ir module)
            '("--mlir-to-llvmir")))

(define (to-bitcode module)
  (define ir (to-llvm-ir module))
  (run-tool (mlir-module-toolchain module) "llvm-as" ir '() #:binary? #t))

(define (to-smtlib module)
  (unless (mlir-module? module) (raise-argument-error 'to-smtlib "mlir-module?" module))
  (run-tool (mlir-module-toolchain module) "mlir-translate" (mlir-module-ir module)
            '("--export-smtlib")))

;; SMT queries. The lowering itself is a native pass that reads a declarative
;; manifest, so this layer only supplies files and arguments. The plugin is
;; never built or located implicitly.
(define-runtime-path native-source "../../mlir/native")

(define plugin-instructions
  (string-append
   "build pille/mlir/native with the MLIR installation that supplies mlir-opt "
   "(see the package README, or use build_plugin), then pass its path explicitly "
   "or set PILLE_MLIR_SMT_PLUGIN"))

(define (resolve-smt-plugin [explicit #f])
  (unless (or (not explicit) (path-string? explicit))
    (raise-argument-error 'smt_query "path-string? or #f" explicit))
  (define selected (or explicit (getenv "PILLE_MLIR_SMT_PLUGIN")))
  (unless selected
    (raise-user-error 'pille/mlir "no SMT query plugin was selected; ~a" plugin-instructions))
  (define path (path->complete-path selected))
  (unless (file-exists? path)
    (raise-user-error 'pille/mlir "cannot find the SMT query plugin ~a; ~a" path plugin-instructions))
  path)

;; A pass option is one token of the textual pipeline; quoting keeps a
;; temporary directory containing spaces intact.
(define (quote-pass-option who text)
  (define quotation
    (for/first ([candidate (in-list '("\"" "'"))]
                #:unless (string-contains? text candidate))
      candidate))
  (unless quotation
    (raise-user-error who "cannot pass ~s as a pass option: it contains both kinds of quotation mark"
                      text))
  (string-append quotation text quotation))

(define (run-smt-query-pass module plugin manifest)
  (unless (mlir-module? module) (raise-argument-error 'smt_query "mlir-module?" module))
  (unless (string? manifest) (raise-argument-error 'smt_query "string?" manifest))
  (run-tool (mlir-module-toolchain module) "mlir-opt" (mlir-module-ir module)
            '("--verify-each" "--mlir-print-debuginfo")
            #:irdl (mlir-module-irdl module)
            #:pass-plugins (list plugin)
            #:in-directory
            (lambda (directory)
              (define path (build-path directory "manifest.json"))
              (display-to-file manifest path #:exists 'truncate)
              (list (string-append
                     "--pass-pipeline=builtin.module(pille-smt-query{manifest="
                     (quote-pass-option 'smt_query (path->string path))
                     "})")))))

;; Verify with the stock tools only: no IRDL definitions and no plugins. This
;; is what mlir-translate sees, so a residual custom operation fails here.
(define (parse-stock-module source module)
  (define chain (mlir-module-toolchain module))
  (parse-module source "" (toolchain (toolchain-bin chain) '() '())))

;; Configure and build the plugin against the installation that supplies the
;; toolchain's mlir-opt. This is an explicit, caller-requested action.
(define (build-smt-plugin directory [chain (make-toolchain)] [cmake #f])
  (unless (path-string? directory) (raise-argument-error 'build_plugin "path-string?" directory))
  (unless (toolchain? chain) (raise-argument-error 'build_plugin "toolchain?" chain))
  (define executable
    (or cmake (find-executable-path (executable-name "cmake"))
        (raise-user-error 'pille/mlir "cannot find cmake on PATH to build the SMT query plugin")))
  (define build (path->complete-path directory))
  (define prefix (simplify-path (build-path (toolchain-bin chain) 'up)))
  (define configuration (build-path prefix "lib" "cmake" "mlir"))
  (unless (directory-exists? configuration)
    (raise-user-error 'pille/mlir
                      "cannot find MLIR's CMake package at ~a; the plugin needs the MLIR development files of the installation that supplies mlir-opt"
                      configuration))
  (make-directory* build)
  (define log (open-output-string))
  (define (run . arguments)
    (unless (parameterize ([current-output-port log] [current-error-port log]
                           [current-input-port (open-input-string "")])
              (apply system* executable arguments))
      (raise-user-error 'pille/mlir "building the SMT query plugin failed:\n~a"
                        (get-output-string log))))
  (run "-S" (path->string native-source) "-B" (path->string build)
       (string-append "-DMLIR_DIR=" (path->string configuration))
       "-DCMAKE_BUILD_TYPE=Release")
  (run "--build" (path->string build))
  (define plugin (build-path build "PilleSmtQuery.so"))
  (unless (file-exists? plugin)
    (raise-user-error 'pille/mlir "the plugin build did not produce ~a:\n~a"
                      plugin (get-output-string log)))
  plugin)
