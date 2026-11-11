#lang racket/base

(require rackunit
         racket/file
         racket/list
         racket/port
         racket/string
         racket/system
         "../../private/mlir/solver.rkt"
         "../../private/mlir/temporary.rkt")

;; Solver protocol tests. They use deterministic fake executables to reach
;; every outcome, including ones a real solver produces only by accident. They
;; need neither MLIR nor Z3; smt-integration.rkt covers the real solver.
(define query
  #<<SMT
; solver scope 0
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const flag (_ BitVec 1))
(assert (let ((tmp (= x #x00000001)))
        tmp))
(check-sat)
(reset)

SMT
  )
(define inputs '(("x" . 32) ("flag" . 1)))

;; Runs `body` with a scratch directory whose name contains a space, used both
;; for fake executables and as the base for the solver's temporary files.
(define (call-with-scratch body)
  (define root (make-temporary-file "pille solver test ~a" 'directory))
  (define work (build-path root "work files"))
  (make-directory work)
  (dynamic-wind
    void
    (lambda ()
      (parameterize ([current-temporary-base work])
        (body root work)))
    (lambda () (delete-directory/files root #:must-exist? #f))))

;; A fake solver is a shell script. $query is the script it was asked to run,
;; which is always the last argument.
(define (fake-solver root name . lines)
  (define path (build-path root name))
  (display-lines-to-file
   (append '("#!/bin/sh" "for query; do :; done") lines)
   path #:exists 'truncate)
  (file-or-directory-permissions path #o755)
  path)

(define (answering root first-answer model-answer)
  (fake-solver root "fake z3"
               "if grep -q get-value \"$query\"; then"
               (format "  printf '%s\\n' ~a" model-answer)
               "else"
               (format "  printf '%s\\n' ~a" first-answer)
               "fi"))

(define (status result) (solver_result_status result))
(define (diagnostics result) (solver_result_diagnostics result))

(test-case "the SMT-LIB reader splits commands and tolerates comments, strings, and quoting"
  (define commands (map car (smtlib-commands query)))
  (check-equal? (map car commands)
                '("set-logic" "declare-const" "declare-const" "assert" "check-sat" "reset"))
  (check-equal? (smtlib-declarations query) inputs)
  (check-equal? (map car (smtlib-commands "(echo \"a ) ; \"\" b\") ; (ignored)\n(|odd ) name| x)"))
                '(("echo" "\"a ) ; \"\" b\"") ("|odd ) name|" "x")))
  (for ([malformed '("(check-sat" ")" "(echo \"open)" "(|open)")])
    (check-exn #rx"malformed SMT-LIB" (lambda () (smtlib-commands malformed)) malformed))
  (check-exn #rx"unexpected declaration"
             (lambda () (smtlib-declarations "(declare-const p Bool)")))
  (check-exn #rx"unexpected declaration"
             (lambda () (smtlib-declarations "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))"))))

(test-case "the model script repeats the query through check-sat and then asks for values"
  (define script (model-script query '("x" "flag")))
  (check-equal? (map car (smtlib-commands script))
                '(("set-option" ":produce-models" "true")
                  ("set-logic" "QF_BV")
                  ("declare-const" "x" ("_" "BitVec" "32"))
                  ("declare-const" "flag" ("_" "BitVec" "1"))
                  ("assert" ("let" (("tmp" ("=" "x" "#x00000001"))) "tmp"))
                  ("check-sat")
                  ("get-value" ("x" "flag"))))
  ;; get-value is only legal after sat, so the trailing reset must be dropped.
  (check-false (string-contains? script "(reset)"))
  (check-exn #rx"exactly one \\(check-sat\\)" (lambda () (model-script "(set-logic QF_BV)" '("x"))))
  (check-exn #rx"exactly one \\(check-sat\\)"
             (lambda () (model-script "(check-sat)(check-sat)" '("x")))))

(test-case "models are accepted in every bitvector literal form and checked against the inputs"
  (define (parse text)
    (define-values (assignments reason) (parse-model (car (car (smtlib-commands text))) inputs))
    (or assignments reason))
  (check-equal? (parse "((x #x0000002a) (flag #b1))") '(("x" 32 42) ("flag" 1 1)))
  (check-equal? (parse "((x (_ bv4294967295 32)) (flag (_ bv0 1)))")
                '(("x" 32 4294967295) ("flag" 1 0)))
  (check-regexp-match #rx"expected 2 assignments" (parse "((x #x0000002a))"))
  (check-regexp-match #rx"expected a value for flag" (parse "((x #x0000002a) (x #x0000002a))"))
  (check-regexp-match #rx"has width 8, expected 32" (parse "((x #x2a) (flag #b1))"))
  (check-regexp-match #rx"has width 4, expected 1" (parse "((x #x0000002a) (flag #x1))"))
  (check-regexp-match #rx"not a bitvector literal" (parse "((x 42) (flag #b1))"))
  (check-regexp-match #rx"not a bitvector literal" (parse "((x true) (flag #b1))"))
  (check-regexp-match #rx"has width 32, expected 32|expected 32"
                      (parse "((x (_ bv4294967296 32)) (flag #b1))"))
  (check-regexp-match #rx"malformed assignment" (parse "((x) (flag #b1))"))
  (check-regexp-match #rx"expected 2 assignments" (parse "sat")))

(test-case "unsat, unknown, and sat with a model are distinguished"
  (call-with-scratch
   (lambda (root work)
     (define unsat (run_solver query inputs (answering root "unsat" "unused")))
     (check-eq? (status unsat) 'unsat)
     (check-equal? (solver_result_values unsat) '())
     (define unknown (run_solver query inputs (answering root "unknown" "unused")))
     (check-eq? (status unknown) 'unknown)
     (check-regexp-match #rx"unknown" (diagnostics unknown))
     (define sat
       (run_solver query inputs
                   (answering root "sat" "sat '((x #x00000001)' ' (flag #b0))'")))
     (check-eq? (status sat) 'sat)
     (check-equal? (solver_result_values sat) '(("x" 32 1) ("flag" 1 0)))
     ;; The command names the executable that was run, for reproduction.
     (check-equal? (solver_result_command sat)
                   (list (path->string (build-path root "fake z3")) "<query.smt2>"))
     (check-true (>= (solver_result_seconds sat) 0))
     ;; A query without inputs needs no model and no second run.
     (define closed
       (run_solver query '() (answering root "sat" "'unsat'")))
     (check-eq? (status closed) 'sat)
     (check-equal? (solver_result_values closed) '())
     ;; Every run cleaned up after itself.
     (check-equal? (directory-list work) '()))))

(test-case "sat without a complete, well-formed model is a failure, never a result"
  (call-with-scratch
   (lambda (root work)
     (for ([model '("sat"                                   ; no values at all
                    "sat '((x #x00000001))'"                ; one input missing
                    "sat '((x #x01) (flag #b0))'"           ; wrong width
                    "sat '((x 1) (flag #b0))'"              ; not a bitvector
                    "sat '((y #x00000001) (flag #b0))'"     ; wrong name
                    "sat '((x #x00000001) (flag #b0)'"      ; unbalanced
                    "unsat"                                 ; contradicts the first run
                    "sat '(error \"model is not available\")'"
                    "garbage")])
       (define result (run_solver query inputs (answering root "sat" model)))
       (check-eq? (status result) 'bad-model model)
       (check-equal? (solver_result_values result) '() model)
       (check-regexp-match #rx"the solver answered sat, but" (diagnostics result) model))
     ;; A model run that fails outright is reported with its diagnostics.
     (define failing
       (fake-solver root "fails on model"
                    "if grep -q get-value \"$query\"; then"
                    "  echo 'model generation exploded' >&2; exit 3"
                    "else echo sat; fi"))
     (define result (run_solver query inputs failing))
     (check-eq? (status result) 'bad-model)
     (check-regexp-match #rx"failed with status 3" (diagnostics result))
     (check-regexp-match #rx"model generation exploded" (diagnostics result))
     (check-equal? (directory-list work) '()))))

(test-case "malformed output and nonzero exits are operational failures with diagnostics"
  (call-with-scratch
   (lambda (root work)
     (for ([output '("" "maybe" "sat unsat" "'(error \"line 1: bad\")' sat" "SAT" "unsat extra")])
       (define result (run_solver query inputs (answering root output "unused")))
       (check-eq? (status result) 'malformed-response output)
       (check-regexp-match #rx"expected exactly one of sat, unsat, or unknown"
                           (diagnostics result) output))
     ;; Z3 prints an error and still answers; the exit status must win.
     (define erroring
       (fake-solver root "errors"
                    "echo '(error \"line 3 column 9: invalid declaration\")'"
                    "echo unsat"
                    "echo 'internal detail' >&2"
                    "exit 1"))
     (define result (run_solver query inputs erroring))
     (check-eq? (status result) 'nonzero-exit)
     (check-regexp-match #rx"exited with status 1" (diagnostics result))
     (check-regexp-match #rx"invalid declaration" (diagnostics result))
     (check-regexp-match #rx"internal detail" (diagnostics result))
     (check-equal? (directory-list work) '()))))

(test-case "a missing executable is reported, and explicit selections never fall back"
  (call-with-scratch
   (lambda (root work)
     (define missing (build-path root "no such solver"))
     (define result (run_solver query inputs missing))
     (check-eq? (status result) 'missing-executable)
     (check-regexp-match (regexp-quote (path->string missing)) (diagnostics result))
     (parameterize ([current-environment-variables
                     (environment-variables-copy (current-environment-variables))])
       ;; PILLE_Z3 selects the solver, and a broken selection is an error even
       ;; when a working z3 might be on PATH.
       (putenv "PILLE_Z3" (path->string missing))
       (check-eq? (status (run_solver query inputs)) 'missing-executable)
       (putenv "PILLE_Z3" (path->string (answering root "unsat" "unused")))
       (check-eq? (status (run_solver query inputs)) 'unsat)
       ;; An explicit executable takes precedence over the environment.
       (check-eq? (status (run_solver query inputs missing)) 'missing-executable)
       (environment-variables-set! (current-environment-variables) #"PILLE_Z3" #f)
       (putenv "PATH" (path->string work))
       (define absent (run_solver query inputs))
       (check-eq? (status absent) 'missing-executable)
       (check-regexp-match #rx"cannot find z3 on PATH" (diagnostics absent))
       ;; z3 on PATH is the final fallback.
       (copy-file (answering root "unsat" "unused") (build-path work "z3"))
       (check-eq? (status (run_solver query inputs)) 'unsat)
       (delete-file (build-path work "z3")))
     ;; A file that cannot be executed is not a solver either.
     (define inert (build-path root "inert"))
     (display-to-file "not a program" inert)
     (check-eq? (status (run_solver query inputs inert)) 'missing-executable)
     (check-equal? (directory-list work) '()))))

(define (process-alive? pid)
  (system* (find-executable-path "kill") "-0" (number->string pid)))

(test-case "a timeout terminates the child process and removes temporary files"
  (call-with-scratch
   (lambda (root work)
     (define pid-file (build-path root "pid"))
     (define hanging
       (fake-solver root "hangs"
                    (format "echo $$ > '~a'" (path->string pid-file))
                    "exec sleep 600"))
     (define started (current-inexact-milliseconds))
     (define result (run_solver query inputs hanging 0.5))
     (define elapsed (- (current-inexact-milliseconds) started))
     (check-eq? (status result) 'timeout)
     (check-regexp-match #rx"did not answer within 0.5 seconds and was terminated"
                         (diagnostics result))
     (check-true (< elapsed 10000) "the wait is bounded")
     (define pid (string->number (string-trim (file->string pid-file))))
     (check-false (parameterize ([current-error-port (open-output-nowhere)])
                    (process-alive? pid))
                  "the solver process was terminated")
     (check-equal? (directory-list work) '())
     ;; The bound covers both runs: a model that never arrives is a timeout,
     ;; not a counterexample.
     (define slow-model
       (fake-solver root "slow model"
                    "if grep -q get-value \"$query\"; then exec sleep 600; else echo sat; fi"))
     (define late (run_solver query inputs slow-model 0.5))
     (check-eq? (status late) 'timeout)
     (check-regexp-match #rx"answered sat, but did not report a model" (diagnostics late))
     (check-equal? (solver_result_values late) '())
     (check-equal? (directory-list work) '()))))

(test-case "breaking a waiting solver call also terminates the child and cleans up"
  (call-with-scratch
   (lambda (root work)
     (define pid-file (build-path root "pid"))
     (define hanging
       (fake-solver root "hangs"
                    (format "echo $$ > '~a'" (path->string pid-file))
                    "exec sleep 600"))
     (define base (current-temporary-base))
     (define worker
       (thread (lambda ()
                 (with-handlers ([exn:break? void])
                   (parameterize ([current-temporary-base base])
                     (run_solver query inputs hanging 600))))))
     (let wait ([attempts 0])
       (unless (or (file-exists? pid-file) (> attempts 200))
         (sleep 0.05)
         (wait (add1 attempts))))
     (sleep 0.1)
     (define pid (string->number (string-trim (file->string pid-file))))
     (break-thread worker)
     (thread-wait worker)
     (check-false (parameterize ([current-error-port (open-output-nowhere)])
                    (process-alive? pid))
                  "cancellation terminated the solver process")
     (check-equal? (directory-list work) '()))))

(test-case "paths containing spaces and extra arguments are passed literally"
  (call-with-scratch
   (lambda (root work)
     ;; The fake records its arguments one per line, then answers.
     (define log (build-path root "argument log"))
     (define recording
       (fake-solver root "records arguments"
                    (format "printf '%s\\n' \"$@\" > '~a'" (path->string log))
                    "echo unsat"))
     (define result (run_solver query inputs recording 10 '("-v:0" "model.completion=true two words")))
     (check-eq? (status result) 'unsat)
     (define arguments (file->lines log))
     (check-equal? (take arguments 2) '("-v:0" "model.completion=true two words"))
     ;; The query file lives under the space-containing temporary base.
     (check-true (string-prefix? (third arguments) (path->string work)))
     (check-regexp-match #rx"query\\.smt2$" (third arguments))
     (check-equal? (length arguments) 3)
     (check-equal? (solver_result_command result)
                   (list (path->string recording) "-v:0" "model.completion=true two words"
                         "<query.smt2>"))
     (check-equal? (directory-list work) '()))))

(test-case "arguments are validated before anything runs"
  (check-exn #rx"positive finite real" (lambda () (run_solver query inputs #f 0)))
  (check-exn #rx"positive finite real" (lambda () (run_solver query inputs #f +inf.0)))
  (check-exn #rx"positive finite real" (lambda () (run_solver query inputs #f -1)))
  (check-exn #rx"list or treelist of strings" (lambda () (run_solver query inputs #f 1 '(1))))
  (check-exn #rx"string\\?" (lambda () (run_solver 'query inputs))))
