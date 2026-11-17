#lang racket/base

(require racket/file racket/path racket/system
         racket/treelist file/sha1
         "temporary.rkt")

(provide (rename-out [toolchain? is_toolchain]
                     [make-toolchain make_toolchain]
                     [mlir-module? is_module]
                     [parse-module parse_module]
                     [mlir-module-ir module_ir]
                     [mlir-module-irdl module_irdl]
                     [module-generic module_generic]
                     [parse-stock-module parse_stock_module]
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

;; A tool's answer is kept by what it was asked. The tools are deterministic: the same executable given the same
;; arguments, plugins, dialect definitions and input writes the same output, so a second request for it is answered
;; from the kept output, with no process started. A lowering asks the same few things many times over (the same
;; module parsed, printed and exported for each query), and starting the tool is most of what each costs.
;;
;; The key is a digest of everything the output depends on: the executable (its path, size and modification time,
;; so another installation or a rebuilt tool is another key), each plugin the same way, the arguments, the working
;; directory (a pass option may name a file relative to it), the dialect definitions and the input. Only an answer
;; is kept: a failure runs the tool again and reports its diagnostics as before.
;;
;; PILLE_MLIR_CACHE names the folder (default: pille-mlir in the system's cache folder); "off" keeps nothing.
;; An entry not asked for in 30 days is removed, once a process, when the cache is first used.
(define memory (make-hash))   ; key -> output, for the process: no file is read twice

(define (cache-directory)
  (define said (getenv "PILLE_MLIR_CACHE"))
  (cond [(equal? said "off") #f]
        [(and said (not (equal? said ""))) (path->complete-path said)]
        [else (build-path (find-system-path 'cache-dir) "pille-mlir")]))

(define (file-identity path)
  (list (path->string path)
        (if (file-exists? path) (file-size path) -1)
        (if (file-exists? path) (file-or-directory-modify-seconds path) -1)))

(define (cache-key chain name executable input arguments irdl binary?)
  (sha1-bytes
   (string->bytes/utf-8
    (format "~s"
            (list 1 name (file-identity executable)
                  (if (equal? name "mlir-opt")
                      (map file-identity (append (toolchain-dialect-plugins chain) (toolchain-pass-plugins chain)))
                      '())
                  arguments (path->string (current-directory)) irdl binary? input)))))

(define pruned? #f)
(define (prune! directory)
  (unless pruned?
    (set! pruned? #t)
    (define oldest (- (current-seconds) (* 30 24 60 60)))
    (with-handlers ([exn:fail? void])
      (for ([entry (in-list (directory-list directory #:build? #t))])
        (with-handlers ([exn:fail? void])
          (when (and (file-exists? entry) (< (file-or-directory-modify-seconds entry) oldest))
            (delete-file entry)))))))

(define (kept directory key binary?)
  (define file (build-path directory (bytes->hex-string key)))
  (and (file-exists? file)
       (with-handlers ([exn:fail? (lambda (_) #f)])
         ;; asked for again: its day is today's, so an entry in use is not the one removed
         (when (< (file-or-directory-modify-seconds file) (- (current-seconds) (* 24 60 60)))
           (file-or-directory-modify-seconds file (current-seconds)))
         (if binary?
             (bytes->immutable-bytes (file->bytes file))
             (string->immutable-string (file->string file))))))

(define (keep! directory key output)
  ;; written beside its place and moved there, so a reader never sees a part of it and two writers of one key
  ;; (the same answer) do not mix; a cache that cannot be written is no failure of the tool
  (with-handlers ([exn:fail? void])
    (make-directory* directory)
    (define part (make-temporary-file "part-~a" #f directory))
    (if (bytes? output)
        (call-with-output-file part #:exists 'truncate (lambda (out) (write-bytes output out)))
        (display-to-file output part #:exists 'truncate))
    (rename-file-or-directory part (build-path directory (bytes->hex-string key)) #t)))

(define (run-tool chain name input arguments #:irdl [irdl ""] #:binary? [binary? #f])
  (define executable (tool-path chain name))
  (define directory (cache-directory))
  (define key (cache-key chain name executable input arguments irdl binary?))
  (when directory (prune! directory))
  (or (hash-ref memory key #f)
      (let ([output (or (and directory (kept directory key binary?))
                        (let ([made (run-tool/process chain name executable input arguments irdl binary?)])
                          (when directory (keep! directory key made))
                          made))])
        ;; a process that lives long (a server) does not hold every answer it ever had
        (when (>= (hash-count memory) 4096) (hash-clear! memory))
        (hash-set! memory key output)
        output)))

(define (run-tool/process chain name executable input arguments irdl binary?)
  ;; Files avoid pipe-buffer deadlocks for large modules and diagnostics. Run
  ;; directly, without a shell, so paths and pipelines remain literal arguments.
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
             (for/list ([path (in-list (toolchain-pass-plugins chain))])
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
                         (append registration-args arguments
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

;; The verified module in MLIR's generic form, which the SMT lowering reads.
;; Locations, attributes and types are printed in place, without aliases. It
;; is asked for once per module, however many queries are lowered over it.
(define generic-texts (make-weak-hasheq))

(define (module-generic module)
  (unless (mlir-module? module) (raise-argument-error 'module_generic "mlir-module?" module))
  (or (hash-ref generic-texts module #f)
      (let ([text (run-tool (mlir-module-toolchain module) "mlir-opt" (mlir-module-ir module)
                            '("--verify-each" "--mlir-print-op-generic" "--mlir-print-local-scope"
                              "--mlir-print-debuginfo")
                            #:irdl (mlir-module-irdl module))])
        (hash-set! generic-texts module text)
        text)))

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

;; Verify with the stock tools only: no IRDL definitions and no plugins. This
;; is what mlir-translate sees, so a residual custom operation fails here. The
;; SMT lowering (lower.rhm) writes its queries as text, and this is where the
;; toolchain reads them.
(define (parse-stock-module source module)
  (define chain (mlir-module-toolchain module))
  (parse-module source "" (toolchain (toolchain-bin chain) '() '())))
