#lang racket/base

(require racket/async-channel
         racket/list
         racket/match
         racket/port
         racket/string
         racket/treelist
         "solver.rkt")

(provide make_session close_session session_check session_check_batch run_solver_batch
         session_values session_objective
         session_scope_open session_scope_assert session_scope_push session_scope_pop
         session_scope_check session_scope_close session_scope_depth
         (rename-out [session? is_session]
                     [enumeration? is_enumeration]
                     [enumeration-complete enumeration_complete])
         enumeration_values)

;; A session owns a child custodian. Its ports, reader threads, and process are
;; all registered there, so its caller's custodian shuts everything down too.
;; Access is serialized; no command from another thread can enter a scope.
(struct session ([executable #:mutable] arguments owner alive lock cache
                            [custodian #:mutable] [process #:mutable]
                            [input #:mutable] [output #:mutable]
                            [writer #:mutable]
                            [errors #:mutable] [command #:mutable]
                            [counter #:mutable] [closed? #:mutable]
                            ;; the depth of an open scope's solver stack, or #f
                            [scope #:mutable]))
(struct enumeration (values complete) #:transparent)
(struct prepared (body declarations) #:transparent)

;; What a session's solver is told when it starts, and again after any reset.
(define session-options
  "(set-option :print-success false)\n(set-option :produce-models true)\n(set-logic QF_BV)")
(struct exn:fail:protocol exn:fail (status))

(define (enumeration_values value) (list->treelist (enumeration-values value)))

(define (protocol-error status message . arguments)
  (raise (exn:fail:protocol (apply format message arguments)
                            (current-continuation-marks) status)))

(define (positive-seconds who seconds)
  (unless (and (real? seconds) (rational? seconds) (positive? seconds))
    (raise-argument-error who "positive finite real (seconds)" seconds)))

(define (as-list who value)
  (cond [(list? value) value]
        [(treelist? value) (treelist->list value)]
        [else (raise-argument-error who "list or treelist" value)]))

(define (make_session [executable #f] [arguments '()])
  (unless (or (not executable) (path-string? executable))
    (raise-argument-error 'Session "path-string? or #f" executable))
  (define extra (as-list 'Session arguments))
  (unless (andmap string? extra)
    (raise-argument-error 'Session "list or treelist of strings" arguments))
  (define owner (current-custodian))
  ;; Startup is lazy: importing or constructing this value needs no solver.
  (session (and executable (path->complete-path executable))
           (map string->immutable-string extra) owner
           (make-custodian-box owner #t) (make-semaphore 1) (make-weak-hasheq)
           #f #f #f #f #f #f '() 0 #f #f))

(define (check-session who value)
  (unless (session? value) (raise-argument-error who "Session" value)))

(define (stop! s)
  (define child (session-process s))
  (when (session-custodian s)
    (custodian-shutdown-all (session-custodian s)))
  (when child
    (with-handlers ([exn:fail? void])
      (when (eq? (subprocess-status child) 'running) (subprocess-kill child #t))
      (subprocess-wait child)))
  ;; an open scope's assertions were the solver's: they are gone with it
  (set-session-scope! s #f)
  (set-session-custodian! s #f)
  (set-session-process! s #f)
  (set-session-input! s #f)
  (set-session-output! s #f)
  (set-session-writer! s #f))

(define (close_session s)
  (check-session 'close s)
  (call-with-semaphore (session-lock s)
    (lambda () (set-session-closed?! s #t) (stop! s))))

(define (errors-text s)
  (if (session-errors s) (get-output-string (session-errors s)) ""))

(define (remaining deadline)
  (max 0.0 (/ (- deadline (current-inexact-monotonic-milliseconds)) 1000.0)))

(define (read-response s marker deadline)
  (let loop ([lines '()])
    (define next (sync/timeout (remaining deadline) (session-output s)))
    (cond
      [(not next)
       (protocol-error 'timeout "the solver did not answer before its deadline; it was terminated")]
      [(eof-object? next)
       (define child (session-process s))
       (sync/timeout (remaining deadline) child)
       (define code (subprocess-status child))
       (protocol-error (if (and (integer? code) (not (zero? code)))
                           'nonzero-exit 'malformed-response)
                       "solver output ended before marker ~a (exit ~a); output: ~a\n~a"
                       marker code (string-join (reverse lines) "\n") (errors-text s))]
      [(equal? next marker) (string-join (reverse lines) "\n")]
      [else (loop (cons next lines))])))

(define (exchange s script deadline)
  (set-session-counter! s (add1 (session-counter s)))
  (define marker (format "pille_smt_reply_~a" (session-counter s)))
  (with-handlers ([exn:fail:protocol? raise]
                  [exn:fail? (lambda (error)
                               (protocol-error 'nonzero-exit "cannot communicate with solver: ~a\n~a"
                                               (exn-message error) (errors-text s)))])
    (write-deadline s (string-append script (format "\n(echo ~s)\n" marker)) deadline))
  (read-response s marker deadline))

;; A dedicated writer can block on pipe capacity without blocking the caller.
;; Waiting for its acknowledgement uses the same deadline as reads. Both the
;; writer and pipe belong to the process custodian, so timeout/cancellation
;; tears down a write even when the child has stopped consuming input.
(define (write-deadline s text deadline)
  (define completion (make-async-channel))
  (async-channel-put (session-writer s) (cons text completion))
  (define response (sync/timeout (remaining deadline) completion))
  (cond
    [(not response)
     (protocol-error 'timeout "the solver did not consume its input before the deadline; it was terminated")]
    [(exn? response) (raise response)]
    [else (void)]))

(define (expect-empty s script deadline)
  (define response (exchange s script deadline))
  (unless (string=? (string-trim response) "")
    (protocol-error 'malformed-response "unexpected solver output: ~a" response)))

(define (start! s deadline)
  (when (or (session-closed? s) (not (custodian-box-value (session-alive s))))
    (protocol-error 'closed-session "the solver session is closed"))
  (unless (session-process s)
    (define-values (executable reason) (find-solver (session-executable s)))
    (define arguments (append (session-arguments s) '("-in")))
    (set-session-command! s
                          (cons (if executable (path->string executable)
                                    (format "~a" (or (session-executable s) "z3")))
                                arguments))
    (unless executable (protocol-error 'missing-executable "~a" reason))
    ;; Restarts retain the solver that this session selected, even if PATH,
    ;; PILLE_Z3, or the caller's working directory changes in the meantime.
    (set-session-executable! s executable)
    (define custodian (make-custodian (session-owner s)))
    (set-session-custodian! s custodian)
    (with-handlers ([exn:fail? (lambda (error)
                               (stop! s)
                               (protocol-error 'missing-executable "cannot start solver: ~a" (exn-message error)))])
      (parameterize ([current-custodian custodian]
                     [current-subprocess-custodian-mode 'kill]
                     [subprocess-group-enabled #t])
        (define-values (child stdout stdin stderr)
          (apply subprocess #f #f #f executable arguments))
        (define replies (make-async-channel))
        (define writes (make-async-channel))
        (define errors (open-output-string))
        (set-session-process! s child)
        (set-session-input! s stdin)
        (set-session-output! s replies)
        (set-session-writer! s writes)
        (set-session-errors! s errors)
        (file-stream-buffer-mode stdin 'none)
        (thread (lambda ()
                  (let loop ()
                    (define request (async-channel-get writes))
                    (define result
                      (with-handlers ([exn:fail? values])
                        (display (car request) stdin)
                        (flush-output stdin)
                        #t))
                    (async-channel-put (cdr request) result)
                    (loop))))
        (thread (lambda ()
                  (with-handlers ([exn:fail? (lambda (_) (async-channel-put replies eof))])
                    (let loop ()
                      (define line (read-line stdout 'any))
                      (async-channel-put replies line)
                      (unless (eof-object? line) (loop))))))
        (thread (lambda ()
                  (with-handlers ([exn:fail? void]) (copy-port stderr errors))))))
    (expect-empty s session-options deadline)))

;; Read actual SMT commands, retaining their original text. A query value is
;; already verified/exported, but only a narrowly scoped script is accepted.
;; Neither reset nor a nested push/pop can destroy a surrounding session scope.
(define (prepare s text)
  (unless (string? text) (raise-argument-error 'session_check "string?" text))
  (define (parse)
    (define body (open-output-string))
    (define checks 0)
    (define previous 0)
    (for ([entry (in-list (smtlib-commands text))])
      (define form (car entry))
      (define end (cdr entry))
      (define original (substring text previous end))
      (set! previous end)
      (match form
        [(list "set-logic" "QF_BV") (void)]
        [(list "reset") (void)]
        [(list "check-sat") (set! checks (add1 checks))]
        [(list (or "declare-const" "define-fun" "assert") _ ...)
         (when (positive? checks)
           (protocol-error 'malformed-response "query contains declarations or assertions after check-sat"))
         (display original body) (newline body)]
        [_ (protocol-error 'malformed-response "unsupported command in session query: ~s" form)]))
    (unless (= checks 1)
      (protocol-error 'malformed-response "expected exactly one check-sat in a session question, found ~a" checks))
    (prepared (get-output-string body) (smtlib-declarations text)))
  (if (immutable? text) (hash-ref! (session-cache s) text parse) (parse)))

(define (timeout-option seconds)
  (format "(set-option :timeout ~a)\n"
          (min 4294967295 (max 1 (inexact->exact (ceiling (* seconds 1000)))))))

(define (answer s script deadline)
  (define response (string-trim (exchange s script deadline)))
  (cond
    [(member response '("sat" "unsat")) (string->symbol response)]
    [(equal? response "unknown")
     (define reason (string-trim (exchange s "(get-info :reason-unknown)" deadline)))
     (define forms
       (with-handlers ([exn:fail? (lambda (_) #f)])
         (map car (smtlib-commands reason))))
     (match forms
       [(list (list ":reason-unknown" (? string? text)))
        (if (or (equal? text "\"timeout\"") (equal? text "\"canceled\""))
            'timeout 'unknown)]
       [_ (protocol-error 'malformed-response "invalid reason-unknown response: ~a" reason)])]
    [else (protocol-error 'malformed-response "expected exactly one of sat, unsat, or unknown; received: ~a" response)]))

(define (assignments s expected deadline)
  (cond
    [(null? expected) '()]
    [else
     (define response (exchange s (format "(get-value (~a))" (string-join (map car expected) " ")) deadline))
     (define forms
       (with-handlers ([exn:fail? (lambda (_) #f)]) (map car (smtlib-commands response))))
     (unless (and forms (= (length forms) 1))
       (protocol-error 'bad-model "malformed get-value response: ~a" response))
     (define-values (values reason) (parse-model (car forms) expected))
     (unless values (protocol-error 'bad-model "~a; response: ~a" reason response))
     values]))

(define (finish-scope s deadline)
  (expect-empty s "(pop 1)\n(set-option :timeout 0)" deadline))

(define (run-protected s timeout overall-deadline thunk)
  (define start (current-inexact-monotonic-milliseconds))
  (define deadline (min (+ start (* timeout 1000.0)) overall-deadline))
  (define (result status [values '()] [note ""])
    (solver-result status values
                   (string->immutable-string
                    (string-join (filter non-empty-string? (list note (errors-text s))) "\n"))
                   (session-command s)
                   (/ (- (current-inexact-monotonic-milliseconds) start) 1000.0)))
  (with-handlers ([exn:fail:protocol?
                   (lambda (error)
                     (define failure (result (exn:fail:protocol-status error) '() (exn-message error)))
                     (stop! s)
                     failure)]
                  [exn:fail?
                   (lambda (error)
                     (define failure (result 'malformed-response '() (exn-message error)))
                     (stop! s)
                     failure)]
                  [exn:break? (lambda (error) (stop! s) (raise error))])
    (start! s deadline)
    (thunk deadline result)))

(define (check/internal s text expected timeout overall-deadline batch-mode?)
  (run-protected
   ;; Z3's per-check timer must have time to report unknown/reason-unknown
   ;; before a batch's host deadline destroys the shared process. The overall
   ;; batch deadline still bounds this grace, including startup and protocol IO.
   s (if batch-mode? (+ timeout 1) timeout) overall-deadline
   (lambda (deadline result)
     (define query (prepare s text))
     (unless (equal? (prepared-declarations query) expected)
       (protocol-error 'bad-model "query input declarations do not match the expected names and widths"))
     (define status
       (answer s (string-append
                  (if batch-mode?
                      "(reset)\n(set-option :print-success false)\n(set-option :produce-models true)\n(set-logic QF_BV)\n"
                      "(push 1)\n")
                  (timeout-option timeout)
                                 (prepared-body query) "\n(check-sat)") deadline))
     (define values (if (eq? status 'sat) (assignments s expected deadline) '()))
     ;; Each batch question starts by resetting the process; the next reset or
     ;; final exit closes this scope. Avoid a redundant reset and round trip.
     ;; Fresh reset scopes also reproduce a standalone solver's model choice;
     ;; Z3's incremental push/pop tactic can select a different valid witness.
     (unless batch-mode? (finish-scope s deadline))
     (define outcome (result status values
                             (case status [(unknown) "solver answered unknown"]
                                   [(timeout) "solver reported its per-question timeout"]
                                   [else ""])))
     (when (and (eq? status 'timeout) (not batch-mode?)) (stop! s))
     outcome)))

;; Whether named assertions can hold together. `body` is declarations and
;; assertions only. The options a core needs must precede every assertion, so
;; the solver is reset before and after: nothing of a session's survives one
;; question to the next, and its usual options are put back. The answer is
;; 'infeasible with the core's names, 'feasible, or a failure as any check's.
(define (core/internal s body timeout overall-deadline)
  ;; 'unsat with the core's names, or another status with none
  (define (ask body deadline)
    (define status
      (answer s (string-append "(reset)\n(set-option :print-success false)\n" core-options
                               "(set-logic QF_BV)\n" (timeout-option timeout) body "\n(check-sat)")
              deadline))
    (values status
            (and (eq? status 'unsat)
                 (let* ([response (exchange s "(get-unsat-core)" deadline)]
                        [forms (with-handlers ([exn:fail? (lambda (_) #f)]) (map car (smtlib-commands response)))]
                        [names (and forms (= (length forms) 1) (parse-core (car forms)))])
                   (unless names (protocol-error 'malformed-response "malformed get-unsat-core response: ~a" response))
                   names))))
  (run-protected
   s timeout overall-deadline
   (lambda (deadline result)
     (define-values (status names) (ask body deadline))
     ;; The core, shrunk until no name can be left out (solver.rkt
     ;; `shrink-core`). Each further question has the bound a question has.
     ;; One that fails or is not answered in time ends the solver's process,
     ;; which the next question starts again, and the shrinking with it: the
     ;; preconditions are known not to hold together, and that stays the
     ;; answer, with the names not yet shown to be unneeded kept.
     (define alive? #t)
     (define shrunk
       (and names
            (shrink-core
             names
             (lambda (keep)
               (and alive?
                    (with-handlers ([exn:fail? (lambda (_error) (set! alive? #f) (stop! s) #f)])
                      (define-values (again smaller)
                        (ask (keeping-named body keep)
                             (min (+ (current-inexact-monotonic-milliseconds) (* timeout 1000.0)) overall-deadline)))
                      (and (eq? again 'unsat) smaller)))))))
     (when alive?
       (expect-empty s (string-append "(reset)\n" session-options)
                     (if names
                         (min (+ (current-inexact-monotonic-milliseconds) (* timeout 1000.0)) overall-deadline)
                         deadline)))
     (case status
       [(unsat) (result 'infeasible shrunk)]
       [(sat) (result 'feasible)]
       [else (result status '() "the solver did not decide whether the named preconditions can hold together")]))))

(define (session_check s text expected [timeout 10] [feasibility-body #f])
  (check-session 'check s)
  (positive-seconds 'check timeout)
  (call-with-semaphore (session-lock s)
    (lambda ()
      (no-scope 'check s)
      (define core (and feasibility-body (core/internal s feasibility-body timeout +inf.0)))
      (if (and core (not (memq (solver_result_status core) '(feasible unknown timeout))))
          core
          (check/internal s text expected timeout +inf.0 #f)))))

(define (annotate value index)
  (solver-result (solver_result_status value) (solver_result_values value)
                 (string->immutable-string
                  (format "question ~a: ~a" index (solver_result_diagnostics value)))
                 (solver_result_command value) (solver_result_seconds value)))

(define (batch/internal s requests timeout overall-timeout batch-mode?)
  (define deadline (+ (current-inexact-monotonic-milliseconds) (* overall-timeout 1000.0)))
  (let loop ([remaining requests] [index 0] [outcomes '()])
    (cond
      [(null? remaining) (reverse outcomes)]
      [else
       (define request (car remaining))
       (define result
         (cond
           [(<= deadline (current-inexact-monotonic-milliseconds))
            (stop! s)
            (solver-result 'timeout '() "overall batch timeout elapsed" (session-command s) overall-timeout)]
           [else
            ;; A question with named preconditions asks first whether they can
            ;; hold together; where they cannot, that is its answer.
            (define core
              (and (pair? (cddr request)) (caddr request)
                   (core/internal s (caddr request) timeout deadline)))
            (if (and core (not (memq (solver_result_status core) '(feasible unknown timeout))))
                core
                (check/internal s (car request) (cadr request) timeout deadline batch-mode?))]))
       (define tagged (annotate result index))
       (define status (solver_result_status result))
       (cond
         [(or (memq status '(unsat sat unknown infeasible))
              (and (eq? status 'timeout) (or (not batch-mode?) (session-process s))))
          (loop (cdr remaining) (add1 index) (cons tagged outcomes))]
         [else
          ;; After protocol failure no later answer can be attributed safely.
          ;; The existing answers survive; each unread slot names the first
          ;; unread question rather than pretending that it was solved.
          (append (reverse (cons tagged outcomes))
                  (for/list ([unused (in-list (cdr remaining))])
                    (solver-result 'malformed-response '()
                                   (format "cannot read question ~a after failure at question ~a: ~a"
                                           (add1 index) index (solver_result_diagnostics result))
                                   (session-command s) 0)))])])))

(define (validated-batch requests timeout overall-timeout)
  (positive-seconds 'check timeout)
  (define inputs (as-list 'check requests))
  (for ([request (in-list inputs)])
    (unless (and (list? request) (memv (length request) '(2 3)) (string? (car request))
                 (list? (cadr request))
                 (or (= (length request) 2) (not (caddr request)) (string? (caddr request))))
      (raise-argument-error 'check "list of (list SMT-LIB expected-inputs [feasibility-body])" requests)))
  (define overall (or overall-timeout (+ 1 (* timeout (length inputs)))))
  (positive-seconds 'check overall)
  (values inputs overall))

(define (session_check_batch s requests [timeout 10] [overall-timeout #f])
  (check-session 'check s)
  (define-values (inputs overall) (validated-batch requests timeout overall-timeout))
  (call-with-semaphore (session-lock s)
    (lambda () (no-scope 'check s) (batch/internal s inputs timeout overall #f))))

;;==============================================================================
;; A scope: assertions kept in the solver from one question to the next
;;
;; A scope declares its inputs once and holds assertions on the solver's stack.
;; Each question is asked in a frame of its own, which is popped again, so a
;; question leaves the scope as it found it. While a scope is open the
;; session's other questions are refused: a check would be asked under the
;; scope's assertions, and a feasibility question or an objective resets the
;; solver. A timeout or a protocol failure ends the solver process, and the
;; scope with it.

(define (no-scope who s)
  (when (session-scope s)
    (raise-user-error who "a scope is open on this session; close it before asking the session anything else")))

(define (in-scope who s)
  (unless (session-scope s)
    (raise-user-error who "the scope is closed: it was closed, or its solver ended on a timeout or a failure")))

;; Sends `script`, which must print nothing; gives 'ok or the failure's result.
(define (scope-command who s script)
  (check-session who s)
  (call-with-semaphore (session-lock s)
    (lambda ()
      (in-scope who s)
      (run-protected s 10 +inf.0
                     (lambda (deadline result) (expect-empty s script deadline) (result 'ok))))))

(define (session_scope_open s declarations)
  (check-session 'smt_scope s)
  (unless (string? declarations) (raise-argument-error 'smt_scope "string?" declarations))
  (call-with-semaphore (session-lock s)
    (lambda ()
      (no-scope 'smt_scope s)
      (run-protected s 10 +inf.0
                     (lambda (deadline result)
                       (expect-empty s (string-append "(push 1)\n" declarations) deadline)
                       (set-session-scope! s 1)
                       (result 'ok))))))

(define (session_scope_depth s) (session-scope s))

(define (session_scope_assert s assertions) (scope-command 'assert s assertions))

(define (session_scope_push s)
  (define answer (scope-command 'push s "(push 1)"))
  (when (and (eq? (solver_result_status answer) 'ok) (session-scope s))
    (set-session-scope! s (add1 (session-scope s))))
  answer)

(define (session_scope_pop s)
  (check-session 'pop s)
  (when (and (session-scope s) (<= (session-scope s) 1))
    (raise-user-error 'pop "nothing was pushed on this scope; close it to end it"))
  (define answer (scope-command 'pop s "(pop 1)"))
  (when (and (eq? (solver_result_status answer) 'ok) (session-scope s))
    (set-session-scope! s (sub1 (session-scope s))))
  answer)

(define (session_scope_close s)
  (check-session 'close s)
  (call-with-semaphore (session-lock s)
    (lambda ()
      (define depth (session-scope s))
      (when depth
        (set-session-scope! s #f)
        (run-protected s 10 +inf.0
                       (lambda (deadline result)
                         (expect-empty s (format "(pop ~a)" depth) deadline)
                         (result 'ok))))
      (void))))

;; One question under the scope's assertions: `goal` is asserted in a frame of
;; its own and the frame popped. 'unsat, 'sat with `expected`'s values, or as
;; any check's.
(define (session_scope_check s goal expected [timeout 10])
  (check-session 'check s)
  (positive-seconds 'check timeout)
  (call-with-semaphore (session-lock s)
    (lambda ()
      (in-scope 'check s)
      (run-protected
       s timeout +inf.0
       (lambda (deadline result)
         (define status
           (answer s (string-append "(push 1)\n" (timeout-option timeout) goal "\n(check-sat)") deadline))
         (define values (if (eq? status 'sat) (assignments s expected deadline) '()))
         (finish-scope s deadline)
         (define outcome (result status values
                                 (case status [(unknown) "solver answered unknown"]
                                       [(timeout) "solver reported its per-question timeout"]
                                       [else ""])))
         (when (eq? status 'timeout) (stop! s))
         outcome)))))

;;==============================================================================
;; An objective, asked of a session's solver

;; `body` is declarations and assertions; `expected` the objective's symbol
;; and then each input, as (name . width). The solver is reset before and
;; after, as for a feasibility question. 'optimum with the values, 'infeasible
;; (with a core where `feasibility-body` is given and its named assertions
;; cannot hold together), or as any check's.
(define (session_objective s body direction symbol expected [timeout 10] [feasibility-body #f])
  (check-session 'check s)
  (positive-seconds 'check timeout)
  (call-with-semaphore (session-lock s)
    (lambda ()
      (no-scope 'check s)
      (define core (and feasibility-body (core/internal s feasibility-body timeout +inf.0)))
      (if (and core (not (memq (solver_result_status core) '(feasible unknown timeout))))
          core
          (run-protected
           s timeout +inf.0
           (lambda (deadline result)
             (define status
               (answer s (string-append "(reset)\n" session-options "\n" (timeout-option timeout) body
                                        (format "\n(~a ~a)\n(check-sat)" direction symbol))
                       deadline))
             (define values (if (eq? status 'sat) (assignments s expected deadline) '()))
             (expect-empty s (string-append "(reset)\n" session-options) deadline)
             (case status
               [(sat) (result 'optimum values)]
               [(unsat) (result 'infeasible '())]
               [else (result status '() "the solver did not find the objective's best value")])))))))

(define (run_solver_batch requests [executable #f] [timeout 10] [arguments '()] [overall-timeout #f])
  (define-values (inputs overall) (validated-batch requests timeout overall-timeout))
  (define s (make_session executable arguments))
  (define deadline (+ (current-inexact-monotonic-milliseconds) (* overall 1000.0)))
  (dynamic-wind void
                (lambda ()
                  (define results (batch/internal s inputs timeout overall #t))
                  ;; A batch is a complete solver run, so validate its exit too.
                  ;; An exit failure is never allowed to leave an apparent proof.
                  (define failure
                    (and (session-process s)
                         (with-handlers ([exn:fail:protocol?
                                          (lambda (error)
                                            (solver-result (exn:fail:protocol-status error) '()
                                                           (format "batch termination after question ~a: ~a"
                                                                   (sub1 (length inputs)) (exn-message error))
                                                           (session-command s) 0))]
                                         [exn:fail?
                                          (lambda (error)
                                            (solver-result 'nonzero-exit '() (exn-message error)
                                                           (session-command s) 0))])
                           (write-deadline s "(exit)\n" deadline)
                           (close-output-port (session-input s))
                           (unless (sync/timeout (remaining deadline) (session-process s))
                             (protocol-error 'timeout "solver did not exit within the overall bound"))
                           (define code (subprocess-status (session-process s)))
                           (unless (eqv? code 0)
                             (protocol-error 'nonzero-exit "solver exited with status ~a\n~a" code (errors-text s)))
                           (let drain ()
                             (define line (sync/timeout (remaining deadline) (session-output s)))
                             (cond [(not line) (protocol-error 'timeout "solver output did not close")]
                                   [(eof-object? line) #f]
                                   [else (protocol-error 'malformed-response "unexpected trailing solver output: ~a" line)])))))
                  (if failure (make-list (length results) failure) results))
                (lambda () (close_session s))))

(define (session_values s text result-name result-width limit [timeout 10] [defined-name #f])
  (check-session 'values s)
  (positive-seconds 'values timeout)
  (unless (exact-nonnegative-integer? limit)
    (raise-argument-error 'values "exact-nonnegative-integer?" limit))
  (unless (and (string? result-name) (exact-positive-integer? result-width))
    (raise-arguments-error 'values "expected a result symbol and positive bitvector width"
                           "result" result-name "width" result-width))
  (call-with-semaphore
   (session-lock s)
   (lambda ()
     (no-scope 'values s)
     (run-protected
      s timeout +inf.0
      (lambda (deadline result)
        (define query (prepare s text))
        (unless (equal? (assoc result-name (prepared-declarations query)) (cons result-name result-width))
          (protocol-error 'bad-model "the result declaration is missing or has the wrong width"))
        (when (and defined-name
                   (not (equal? (assoc defined-name (prepared-declarations query)) (cons defined-name 1))))
          (protocol-error 'bad-model "the definedness declaration is missing or has the wrong width"))
        (expect-empty s (string-append "(push 1)\n" (timeout-option timeout) (prepared-body query)) deadline)
        (let/ec return
          (define (failed status note)
            (finish-scope s deadline)
            (define value (result status '() note))
            (when (eq? status 'timeout) (stop! s))
            (return value))
          (when defined-name
            (define status
              (answer s (format "(push 1)\n(assert (= ~a #b0))\n(check-sat)" defined-name) deadline))
            (expect-empty s "(pop 1)" deadline)
            (case status
              [(sat) (failed 'requirements-not-satisfied
                             "some input allowed by the preconditions violates a declared semantic requirement")]
              [(unknown timeout) (failed status "could not establish that every allowed input satisfies the semantic requirements")]))
          (let loop ([found '()])
            (cond
              [(>= (length found) limit)
               (finish-scope s deadline)
               (enumeration (sort found <) #f)]
              [else
               (define status (answer s "(check-sat)" deadline))
               (case status
                 [(unsat) (finish-scope s deadline) (enumeration (sort found <) #t)]
                 [(unknown timeout) (failed status "solver did not complete result enumeration")]
                 [(sat)
                  (define assignment (car (assignments s (list (cons result-name result-width)) deadline)))
                  (define value (caddr assignment))
                  (when (member value found)
                    (protocol-error 'bad-model "solver repeated an explicitly excluded result value ~a" value))
                  (expect-empty s (format "(assert (not (= ~a (_ bv~a ~a))))" result-name value result-width) deadline)
                  (loop (cons value found))])]))))))))
