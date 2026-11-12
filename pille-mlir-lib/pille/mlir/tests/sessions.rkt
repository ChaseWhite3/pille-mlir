#lang racket/base

(require rackunit
         racket/file
         racket/list
         racket/port
         racket/string
         racket/system
         racket/treelist
         "../../private/mlir/session.rkt"
         "../../private/mlir/solver.rkt")

(define expected '(("x" . 8)))
(define (question assertion)
  (string->immutable-string
   (format "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert ~a)\n(check-sat)\n(reset)\n" assertion)))
(define yes (question "(not (= x x))"))
(define no (question "(= x #x2a)"))
(define (status value) (solver_result_status value))

(define (scratch procedure)
  (define directory (make-temporary-file "pille session tests ~a" 'directory))
  (dynamic-wind void (lambda () (procedure directory))
                (lambda () (delete-directory/files directory #:must-exist? #f))))

;; Every fake speaks the same line-framed protocol as Z3. Startup, question,
;; model, pop, and exit failures can therefore be tested independently.
(define (fake directory mode)
  (define executable (build-path directory (string-append "fake solver " mode)))
  (define log (build-path directory "processes"))
  (define flag (build-path directory "already hung"))
  (define python (or (find-executable-path "python3") (error 'test "python3 is required for protocol fixtures")))
  (call-with-output-file executable #:exists 'truncate
    (lambda (output)
      (fprintf output "#!~a\n" python)
      (fprintf output "mode = ~s\nlog = ~s\nflag = ~s\n" mode (path->string log) (path->string flag))
      (display #<<PY
import sys, os, time
with open(log, 'a') as f:
    f.write(str(os.getpid()) + '\n')
with open(log + '.args', 'a') as f:
    f.write(repr(sys.argv[1:]) + '\n')
checks = 0
for line in sys.stdin:
    line = line.strip()
    if line == '(check-sat)':
        checks += 1
        if mode == 'hang-once' and not os.path.exists(flag):
            open(flag, 'w').close()
            time.sleep(600)
        if mode == 'nonzero':
            print('unsat', flush=True)
            sys.exit(7)
        if mode == 'short':
            sys.exit(0)
        if mode == 'malformed':
            print('unsat\nextra', flush=True)
        elif mode == 'unknown' or (mode in ['soft-timeout', 'soft-timeout-late'] and checks == 1):
            if mode == 'soft-timeout-late':
                time.sleep(0.06)
            print('unknown', flush=True)
        elif mode == 'bad-model' or mode == 'sat':
            print('sat', flush=True)
        else:
            print('unsat', flush=True)
    elif line.startswith('(get-info'):
        reason = 'timeout' if mode in ['soft-timeout', 'soft-timeout-late'] else 'incomplete'
        print('(:reason-unknown "' + reason + '")', flush=True)
    elif line.startswith('(get-value'):
        print('((x #x002a))' if mode == 'bad-model' else '((x #x2a))', flush=True)
    elif line.startswith('(echo '):
        print(line[7:-2], flush=True)
        if mode == 'no-read':
            time.sleep(600)
    elif line == '(exit)':
        sys.exit(9 if mode == 'bad-exit' else 0)
PY
               output)))
  (file-or-directory-permissions executable #o755)
  executable)

(test-case "batch and session answers retain isolation and counterexample assignments"
  (define batch (run_solver_batch (list (list yes expected) (list no expected)
                                       (list (question "false") expected) (list no expected))))
  (check-equal? (map status batch) '(unsat sat unsat sat))
  (check-equal? (solver_result_values (cadr batch)) '(("x" 8 42)))
  (check-equal? (solver_result_values (cadddr batch)) '(("x" 8 42)))
  (define s (make_session))
  (dynamic-wind void
                (lambda ()
                  (for ([script (list yes no yes no)])
                    (check-equal? (status (session_check s script expected))
                                  (status (run_solver script expected)))))
                (lambda () (close_session s)))
  (check-eq? (status (session_check s yes expected)) 'closed-session))

(test-case "batch counterexample model selection matches standalone even for unconstrained witnesses"
  (define scripts (for/list ([value (in-range 0 256 17)])
                    (question (format "(not (= x (_ bv~a 8)))" value))))
  (define results (run_solver_batch (map (lambda (script) (list script expected)) scripts)))
  (for ([script (in-list scripts)] [result (in-list results)])
    (define alone (run_solver script expected))
    (check-eq? (status result) (status alone))
    (check-equal? (solver_result_values result) (solver_result_values alone))))

(test-case "a batch uses one process and soft timeouts belong to their own questions"
  (scratch
   (lambda (directory)
     (define executable (fake directory "soft-timeout"))
     (define results (run_solver_batch (make-list 4 (list yes expected)) executable))
     (check-equal? (map status results) '(timeout unsat unsat unsat))
     (check-equal? (length (file->lines (build-path directory "processes"))) 1)
     (check-regexp-match #rx"question 0" (solver_result_diagnostics (car results))))))

(test-case "a batch leaves bounded protocol grace for a solver's timeout notification"
  (scratch
   (lambda (directory)
     (define executable (fake directory "soft-timeout-late"))
     (define results (run_solver_batch (make-list 3 (list yes expected)) executable 0.05 '() 2))
     (check-equal? (map status results) '(timeout unsat unsat))
     (check-equal? (length (file->lines (build-path directory "processes"))) 1))))

(test-case "session wall timeout kills the process and the next question restarts it"
  (scratch
   (lambda (directory)
     (define executable (fake directory "hang-once"))
     (define s (make_session executable))
     (dynamic-wind void
       (lambda ()
         (check-eq? (status (session_check s yes expected 0.3)) 'timeout)
         (define old-pid (car (file->lines (build-path directory "processes"))))
         (check-false (parameterize ([current-error-port (open-output-nowhere)])
                        (system* (find-executable-path "kill") "-0" old-pid)))
         (check-eq? (status (session_check s yes expected 3)) 'unsat)
         (check-equal? (length (file->lines (build-path directory "processes"))) 2))
       (lambda () (close_session s))))))

(test-case "unknown, malformed answers, short output, nonzero exits, and bad models never prove"
  (scratch
   (lambda (directory)
     (for ([mode '("unknown" "malformed" "short" "nonzero" "bad-model")]
           [wanted '(unknown malformed-response malformed-response nonzero-exit bad-model)])
       (define executable (fake directory mode))
       (define s (make_session executable))
       (dynamic-wind void
         (lambda () (check-eq? (status (session_check s no expected)) wanted mode))
         (lambda () (close_session s)))
       (define batch (run_solver_batch (make-list 2 (list no expected)) executable))
       (check-eq? (status (car batch)) wanted mode)
       (check-regexp-match #rx"question 0" (solver_result_diagnostics (car batch)))
       (unless (eq? wanted 'unknown)
         (check-eq? (status (cadr batch)) 'malformed-response mode)
         (check-regexp-match #rx"question 1.*question 0" (solver_result_diagnostics (cadr batch)))))
     (define bad-exit (fake directory "bad-exit"))
     (check-equal? (map status (run_solver_batch (make-list 2 (list yes expected)) bad-exit))
                   '(nonzero-exit nonzero-exit)))))

(test-case "missing executable never falls back and empty batches start no process"
  (scratch
   (lambda (directory)
     (define missing (build-path directory "missing"))
     (define s (make_session missing))
     (check-eq? (status (session_check s yes expected)) 'missing-executable)
     (check-eq? (status (car (run_solver_batch (list (list yes expected)) missing))) 'missing-executable)
     (check-equal? (run_solver_batch '() missing) '())
     (close_session s))))

(test-case "session restart retains its selected solver and passes arguments literally"
  (scratch
   (lambda (directory)
     (define executable (fake directory "hang-once"))
     (parameterize ([current-environment-variables
                     (environment-variables-copy (current-environment-variables))])
       (putenv "PILLE_Z3" (path->string executable))
       (define s (make_session #f '("argument containing spaces")))
       (dynamic-wind void
         (lambda ()
           (check-eq? (status (session_check s yes expected 0.3)) 'timeout)
           (putenv "PILLE_Z3" (path->string (build-path directory "missing")))
           (check-eq? (status (session_check s yes expected 3)) 'unsat)
           (check-equal? (file->lines (build-path directory "processes.args"))
                         '("['argument containing spaces', '-in']"
                           "['argument containing spaces', '-in']")))
         (lambda () (close_session s)))))))

(test-case "overall batch bound stops an unresponsive process without starting another"
  (scratch
   (lambda (directory)
     (define executable (fake directory "hang-once"))
     (define started (current-inexact-monotonic-milliseconds))
     (define results (run_solver_batch (make-list 3 (list yes expected)) executable 10 '() 0.3))
     (check-true (< (- (current-inexact-monotonic-milliseconds) started) 3000))
     (check-equal? (map status results) '(timeout malformed-response malformed-response))
     (check-equal? (length (file->lines (build-path directory "processes"))) 1))))

(test-case "custodian shutdown terminates a live session and rejects further questions"
  (scratch
   (lambda (directory)
     (define executable (fake directory "unsat"))
     (define owner (make-custodian))
     (define s (parameterize ([current-custodian owner]) (make_session executable)))
     (check-eq? (status (session_check s yes expected)) 'unsat)
     (define pid (car (file->lines (build-path directory "processes"))))
     (custodian-shutdown-all owner)
     (check-eq? (status (session_check s yes expected)) 'closed-session)
     (check-false (parameterize ([current-error-port (open-output-nowhere)])
                    (system* (find-executable-path "kill") "-0" pid)))
     (close_session s))))

(test-case "writing a large question to a nonreading solver also obeys the deadline"
  (scratch
   (lambda (directory)
     (define executable (fake directory "no-read"))
     (define s (make_session executable))
     (define large
       (string-append "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n;"
                      (make-string (* 2 1024 1024) #\x)
                      "\n(assert true)\n(check-sat)\n(reset)\n"))
     (define started (current-inexact-monotonic-milliseconds))
     (check-eq? (status (session_check s large expected 0.3)) 'timeout)
     (check-true (< (- (current-inexact-monotonic-milliseconds) started) 3000))
     (define pid (car (file->lines (build-path directory "processes"))))
     (check-false (parameterize ([current-error-port (open-output-nowhere)])
                    (system* (find-executable-path "kill") "-0" pid)))
     (close_session s))))

(test-case "cancelling a waiting question kills its child and permits a later restart"
  (scratch
   (lambda (directory)
     (define executable (fake directory "hang-once"))
     (define s (make_session executable))
     (define worker
       (thread (lambda ()
                 (with-handlers ([exn:break? void])
                   (session_check s yes expected 600)))))
     (let wait ([count 0])
       (unless (or (file-exists? (build-path directory "already hung")) (= count 200))
         (sleep 0.01)
         (wait (add1 count))))
     (define pid (car (file->lines (build-path directory "processes"))))
     (break-thread worker)
     (thread-wait worker)
     (check-false (parameterize ([current-error-port (open-output-nowhere)])
                    (system* (find-executable-path "kill") "-0" pid)))
     (check-eq? (status (session_check s yes expected)) 'unsat)
     (close_session s))))

(define (values-query expression [precondition "true"] [defined "#b1"])
  (string->immutable-string
   (format "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(declare-const result (_ BitVec 8))\n(declare-const defined (_ BitVec 1))\n(assert (= result ~a))\n(assert (= defined ~a))\n(assert ~a)\n(check-sat)\n(reset)\n"
           expression defined precondition)))

(test-case "values enumeration agrees with exhaustive i8 arithmetic and respects limits"
  (define s (make_session))
  (dynamic-wind void
    (lambda ()
      (for ([expression '("x" "(bvmul x #x02)" "(bvadd (bvmul x #x04) #x03)")]
            [evaluate (list values (lambda (x) (modulo (* x 2) 256))
                            (lambda (x) (modulo (+ (* x 4) 3) 256)))])
        (define expected (sort (remove-duplicates (for/list ([x (in-range 256)]) (evaluate x))) <))
        (define result (session_values s (values-query expression) "result" 8 257 10 "defined"))
        (check-true (is_enumeration result))
        (check-equal? (treelist->list (enumeration_values result)) expected)
        (check-true (enumeration_complete result)))
      (define empty (session_values s (values-query "x" "false") "result" 8 10 10 "defined"))
      (check-equal? (treelist->list (enumeration_values empty)) '())
      (check-true (enumeration_complete empty))
      (define singleton (session_values s (values-query "#x2a") "result" 8 2 10 "defined"))
      (check-equal? (treelist->list (enumeration_values singleton)) '(42))
      (check-true (enumeration_complete singleton))
      (define partial (session_values s (values-query "x") "result" 8 7 10 "defined"))
      (check-equal? (treelist-length (enumeration_values partial)) 7)
      (check-false (enumeration_complete partial))
      (define zero (session_values s (values-query "x") "result" 8 0 10 "defined"))
      (check-equal? (treelist->list (enumeration_values zero)) '())
      (check-false (enumeration_complete zero))
      (check-eq? (status (session_check s yes expected)) 'unsat))
    (lambda () (close_session s))))

(test-case "values enumeration refuses models undefined for a permitted input"
  (define s (make_session))
  (dynamic-wind void
    (lambda ()
      (define result
        (session_values s (values-query "#x01" "true" "(ite (= x #x00) #b1 #b0)")
                        "result" 8 10 10 "defined"))
      (check-eq? (status result) 'requirements-not-satisfied)
      (define restricted
        (session_values s (values-query "#x01" "(= x #x00)" "(ite (= x #x00) #b1 #b0)")
                        "result" 8 10 10 "defined"))
      (check-true (enumeration_complete restricted))
      (check-equal? (treelist->list (enumeration_values restricted)) '(1))
      (check-eq? (status (session_check s no expected)) 'sat))
    (lambda () (close_session s))))
