#lang racket/base

;; Compiles every Rhombus and Racket file under the folders (and the files)
;; given, as `raco make` does for files named one by one:
;;
;;   racket -l- pille/make [-j N] PATH ...
;;
;; `raco test` does not rebuild a compiled file whose dependencies changed, so
;; this is run first. The paths are few however many files they hold, which
;; matters where a command line may not be long (Windows: `raco make` given a
;; folder's files by name can pass the limit, and then builds nothing).

(require compiler/cm
         racket/list
         racket/path
         setup/parallel-build)

(define (sources path)
  (cond
    [(directory-exists? path)
     (sort (for/list ([file (in-directory path (lambda (directory)
                                                 (not (member (path->string (file-name-from-path directory))
                                                              '("compiled" ".git")))))]
                      #:when (and (file-exists? file) (member (path-get-extension file) '(#".rhm" #".rkt"))))
             (path->complete-path file))
           string<? #:key path->string)]
    [(file-exists? path) (list (path->complete-path path))]
    [else (raise-user-error 'pille/make "no such file or folder: ~a" path)]))

(define (make-all paths workers)
  (define files (remove-duplicates (append-map sources paths)))
  (cond
    [(null? files) (raise-user-error 'pille/make "nothing to compile under: ~a" paths)]
    [(= workers 1)
     (define compile (make-caching-managed-compile-zo))
     (for ([file (in-list files)]) (compile file))]
    [else
     (define failed? #f)
     (parallel-compile-files (map path->string files)
                             #:worker-count workers
                             #:handler (lambda (worker kind file message out err)
                                         (case kind
                                           [(error fatal-error)
                                            (set! failed? #t)
                                            (eprintf "~a: ~a\n~a~a" file message out err)]
                                           [else (void)])))
     (when failed? (exit 1))])
  (printf "pille/make: ~a files up to date\n" (length files)))

(module+ main
  (define arguments (vector->list (current-command-line-arguments)))
  (define-values (workers paths)
    (if (and (pair? arguments) (equal? (car arguments) "-j") (pair? (cdr arguments))
             (exact-positive-integer? (string->number (cadr arguments))))
        (values (string->number (cadr arguments)) (cddr arguments))
        (values 1 arguments)))
  (when (null? paths)
    (eprintf "usage: racket -l- pille/make [-j N] PATH ...\n")
    (exit 2))
  (make-all paths workers))
