#lang racket/base

(require racket/file
         racket/port
         racket/string
         racket/system)

(provide python python-script process-alive? windows?)

;; Stand-ins for a solver, for the tests of how one is run and spoken to.
;;
;; A stand-in is a Python script, and it is run as `python SCRIPT ...`: the
;; interpreter is the solver's executable and the script the first of its
;; arguments. Nothing is marked executable, which Windows has no way to do to
;; a script, so the tests take the same path on every platform.

(define windows? (eq? (system-type) 'windows))

(define python
  (path->string
   (or (for/or ([name '("python3" "python3.exe" "python" "python.exe")]) (find-executable-path name))
       (error 'tests "these tests run their stand-in solvers with Python: put python3 on PATH"))))

;; Writes `lines` as a script at `path`; gives the path as a string.
(define (python-script path . lines)
  (display-lines-to-file lines path #:exists 'truncate)
  (path->string path))

;; Whether the process with this id (a number, or its digits) is running.
(define (process-alive? pid)
  (define id (if (number? pid) (number->string pid) (string-trim pid)))
  (parameterize ([current-error-port (open-output-nowhere)])
    (cond
      [windows?
       ;; tasklist prints a row that names the id where there is such a process
       (regexp-match? (regexp (string-append "(^|[^0-9])" id "([^0-9]|$)"))
                      (with-output-to-string
                        (lambda ()
                          (system* (find-executable-path "tasklist.exe") "/FI" (string-append "PID eq " id) "/NH" "/FO" "CSV"))))]
      [else (system* (find-executable-path "kill") "-0" id)])))
