#lang racket/base

(require racket/file
         racket/list
         racket/match
         racket/port
         racket/string
         racket/treelist
         "temporary.rkt")

(provide smtlib-commands
         smtlib-declarations
         model-script
         parse-model
         find-solver
         solver-result
         run_solver
         run_solver_core
         run_solver_objective
         core-options
         parse-core
         keeping-named
         shrink-core
         (rename-out [solver-result? is_solver_result]
                     [solver-result-status solver_result_status]
                     [solver-result-values solver_result_values]
                     [solver-result-diagnostics solver_result_diagnostics]
                     [solver-result-command solver_result_command]
                     [result-assignments solver_result_assignments]
                     [result-core solver_result_core]
                     [result-command-line solver_result_command_line]
                     [solver-result-seconds solver_result_seconds]))

;; status is one of:
;;   'unsat 'sat 'unknown            the solver's answer
;;   'timeout                        the requested bound elapsed; child killed
;;   'missing-executable 'nonzero-exit 'malformed-response 'bad-model
;;                                   operational failures
;;   'infeasible                     named preconditions cannot hold together;
;;                                   values is then the names of an unsatisfiable
;;                                   set of them, as the solver reported it
;;   'feasible                       a feasibility check found them satisfiable
;;                                   (internal: never a query's answer)
;;   'optimum                        an objective's best value was found; values
;;                                   is then the objective's symbol first, and
;;                                   the inputs that reach it
;; values is a list of (name width value) and is only non-empty for 'sat.
;; Only 'unsat means that no counterexample exists.
(struct solver-result (status values diagnostics command seconds) #:transparent)

;; Immutable views for Rhombus callers.
(define (result-core value)
  (for/treelist ([name (in-list (solver-result-values value))]) (string->immutable-string name)))

(define (result-assignments value)
  (for/treelist ([assignment (in-list (solver-result-values value))])
    (treelist (string->immutable-string (car assignment)) (cadr assignment) (caddr assignment))))

(define (result-command-line value)
  (for/treelist ([part (in-list (solver-result-command value))])
    (string->immutable-string part)))

;; A small reader for the SMT-LIB that MLIR exports and that solvers print.
;; Atoms stay strings; each top-level form is returned with its end offset.
(define (smtlib-commands text)
  (define size (string-length text))
  (define (malformed) (raise-user-error 'pille/mlir "malformed SMT-LIB text"))
  (define (delimiter? character)
    (or (char-whitespace? character) (memv character '(#\( #\) #\; #\" #\|))))
  (define (skip position)
    (cond
      [(= position size) position]
      [(char-whitespace? (string-ref text position)) (skip (add1 position))]
      [(char=? (string-ref text position) #\;)
       (let loop ([position position])
         (if (or (= position size) (char=? (string-ref text position) #\newline))
             (skip position)
             (loop (add1 position))))]
      [else position]))
  ;; Returns the datum and the offset just past it.
  (define (read-form start)
    (define position (skip start))
    (when (= position size) (malformed))
    (define character (string-ref text position))
    (cond
      [(char=? character #\()
       (let loop ([position (add1 position)] [items '()])
         (define next (skip position))
         (cond
           [(= next size) (malformed)]
           [(char=? (string-ref text next) #\)) (values (reverse items) (add1 next))]
           [else
            (define-values (item end) (read-form next))
            (loop end (cons item items))]))]
      [(char=? character #\)) (malformed)]
      [(memv character '(#\" #\|))
       ;; Strings escape a quote by doubling it; quoted symbols have no escapes.
       (let loop ([end (add1 position)])
         (cond
           [(= end size) (malformed)]
           [(not (char=? (string-ref text end) character)) (loop (add1 end))]
           [(and (char=? character #\") (< (add1 end) size)
                 (char=? (string-ref text (add1 end)) #\"))
            (loop (+ end 2))]
           [else (values (substring text position (add1 end)) (add1 end))]))]
      [else
       (let loop ([end position])
         (if (or (= end size) (delimiter? (string-ref text end)))
             (values (substring text position end) end)
             (loop (add1 end))))]))
  (let loop ([position 0] [forms '()])
    (define next (skip position))
    (cond
      [(= next size) (reverse forms)]
      [else
       (define-values (form end) (read-form next))
       (loop end (cons (cons form end) forms))])))

(define (width-text? text)
  (and (string? text) (regexp-match? #px"^[1-9][0-9]*$" text)))

;; Every symbolic constant of the query, in declaration order.
(define (smtlib-declarations text)
  (for/list ([command (in-list (smtlib-commands text))]
             #:when (match (car command)
                      [(list (or "declare-const" "declare-fun") _ ...) #t]
                      [_ #f]))
    (match (car command)
      [(list "declare-const" (? string? name) (list "_" "BitVec" (? width-text? width)))
       (cons name (string->number width))]
      [_ (raise-user-error 'pille/mlir "unexpected declaration in exported SMT-LIB")])))

;; The exported query ends with (check-sat) and (reset). Counterexample values
;; are requested with the standard get-value command, which is only legal after
;; a satisfiable answer, so it lives in a second script derived from the first:
;; the same commands through (check-sat), followed by get-value.
(define (model-script text names)
  (define checks
    (for/list ([command (in-list (smtlib-commands text))]
               #:when (equal? (car command) '("check-sat")))
      (cdr command)))
  (unless (= (length checks) 1)
    (raise-user-error 'pille/mlir "expected exactly one (check-sat) in the exported SMT-LIB, found ~a"
                      (length checks)))
  (string-append "(set-option :produce-models true)\n"
                 (substring text 0 (car checks))
                 "\n(get-value (" (string-join names " ") "))\n"))

(define (parse-value datum)
  (match datum
    [(? string? (regexp #px"^#x([0-9a-fA-F]+)$" (list _ digits)))
     (cons (* 4 (string-length digits)) (string->number digits 16))]
    [(? string? (regexp #px"^#b([01]+)$" (list _ digits)))
     (cons (string-length digits) (string->number digits 2))]
    [(list "_" (? string? (regexp #px"^bv([0-9]+)$" (list _ digits))) (? width-text? width))
     (cons (string->number width) (string->number digits))]
    [_ #f]))

;; Returns (values assignments #f) or (values #f reason). The response must
;; assign every requested constant exactly once, with a value of its width.
(define (parse-model datum expected)
  (let/ec return
    (define (bad . arguments) (return #f (apply format arguments)))
    (unless (and (list? datum) (= (length datum) (length expected)))
      (bad "expected ~a assignments in the solver's get-value response" (length expected)))
    (define assignments
      (for/list ([entry (in-list datum)] [wanted (in-list expected)])
        (match entry
          [(list (? string? name) value)
           (unless (equal? name (car wanted))
             (bad "expected a value for ~a, but the solver reported ~a" (car wanted) name))
           (define parsed (parse-value value))
           (unless parsed (bad "the value reported for ~a is not a bitvector literal" name))
           (unless (and (= (car parsed) (cdr wanted)) (< (cdr parsed) (expt 2 (cdr wanted))))
             (bad "the value reported for ~a has width ~a, expected ~a"
                  name (car parsed) (cdr wanted)))
           (list name (cdr wanted) (cdr parsed))]
          [_ (bad "malformed assignment in the solver's get-value response")])))
    (values assignments #f)))

(define (executable-name name)
  (if (eq? (system-type) 'windows) (string-append name ".exe") name))

;; An explicit or environment selection must work; it never falls back.
(define (find-solver explicit)
  (define selected (or explicit (getenv "PILLE_Z3")))
  (cond
    [selected
     (define path (path->complete-path selected))
     (cond
       [(not (file-exists? path))
        (values #f (format "cannot find the solver executable ~a" path))]
       [(not (memq 'execute (file-or-directory-permissions path)))
        (values #f (format "the solver ~a is not an executable file" path))]
       [else (values path #f)])]
    [(find-executable-path (executable-name "z3")) => (lambda (path) (values path #f))]
    [else
     (values #f "cannot find z3 on PATH; pass an explicit solver executable or set PILLE_Z3")]))

;; Runs one script to completion or to the deadline. Returns
;; (values 'exited code stdout stderr), (values 'timeout #f stdout stderr), or
;; (values 'failed #f "" message) when the process cannot be started.
(define (run-script executable arguments directory name script deadline)
  (define source (build-path directory (string-append name ".smt2")))
  (define output (build-path directory (string-append name ".stdout")))
  (define diagnostics (build-path directory (string-append name ".stderr")))
  (display-to-file script source #:exists 'truncate)
  ;; The child is terminated and reaped on every exit from this function,
  ;; including a timeout and a break of the waiting thread. It runs in its own
  ;; process group so that anything it started is terminated with it.
  (define child #f)
  (dynamic-wind
    void
    (lambda ()
      (define failure
        (with-handlers ([exn:fail? exn-message])
          (call-with-output-file output #:exists 'truncate
            (lambda (output-port)
              (call-with-output-file diagnostics #:exists 'truncate
                (lambda (error-port)
                  (parameterize ([subprocess-group-enabled #t])
                    (define-values (process _output input _error)
                      (apply subprocess output-port #f error-port executable
                             (append arguments (list (path->string source)))))
                    (set! child process)
                    (close-output-port input))))))
          #f))
      (cond
        [failure (values 'failed #f "" failure)]
        [else
         (define remaining (/ (- deadline (current-inexact-milliseconds)) 1000.0))
         (define finished? (and (> remaining 0) (sync/timeout remaining child) #t))
         (unless finished?
           (subprocess-kill child #t)
           (subprocess-wait child))
         (values (if finished? 'exited 'timeout)
                 (and finished? (subprocess-status child))
                 (file->string output)
                 (file->string diagnostics))]))
    (lambda ()
      (when (and child (eq? (subprocess-status child) 'running))
        (subprocess-kill child #t)
        (subprocess-wait child)))))

(define (text-list who value)
  (define entries (if (treelist? value) (treelist->list value) value))
  (unless (and (list? entries) (andmap string? entries))
    (raise-argument-error who "list or treelist of strings" value))
  entries)

;; `inputs` is a list of (name . width) in declaration order.
(define (run_solver smtlib inputs [executable #f] [timeout 10] [arguments '()])
  (unless (string? smtlib) (raise-argument-error 'run_solver "string?" smtlib))
  (unless (or (not executable) (path-string? executable))
    (raise-argument-error 'run_solver "path-string? or #f" executable))
  (unless (and (real? timeout) (rational? timeout) (positive? timeout))
    (raise-argument-error 'run_solver "positive finite real (seconds)" timeout))
  (define extra (text-list 'run_solver arguments))
  (define started (current-inexact-milliseconds))
  (define deadline (+ started (* 1000.0 timeout)))
  (define-values (solver missing) (find-solver executable))
  (define command
    (append (list (if solver (path->string solver) (or (and executable (format "~a" executable)) "z3")))
            extra (list "<query.smt2>")))
  (define (result status values . notes)
    (solver-result status values
                   (string->immutable-string (string-join (filter non-empty-string? notes) "\n"))
                   command
                   (/ (- (current-inexact-milliseconds) started) 1000.0)))
  (define (transcript stdout stderr)
    (string-append
     (if (non-empty-string? (string-trim stdout)) (format "solver output:\n~a" (string-trim stdout)) "")
     (if (and (non-empty-string? (string-trim stdout)) (non-empty-string? (string-trim stderr))) "\n" "")
     (if (non-empty-string? (string-trim stderr)) (format "solver diagnostics:\n~a" (string-trim stderr)) "")))
  (cond
    [(not solver) (result 'missing-executable '() missing)]
    [else
     (define directory (make-work-directory "pille-smt-~a"))
     (dynamic-wind
       void
       (lambda ()
         (define (run name script)
           (run-script solver extra directory name script deadline))
         (define-values (state code stdout stderr) (run "query" smtlib))
         (define answer (string-trim stdout))
         (cond
           [(eq? state 'failed)
            (result 'missing-executable '() (format "cannot run the solver: ~a" stderr))]
           [(eq? state 'timeout)
            (result 'timeout '() (format "the solver did not answer within ~a seconds and was terminated" timeout)
                    (transcript stdout stderr))]
           [(not (eqv? code 0))
            (result 'nonzero-exit '() (format "the solver exited with status ~a" code)
                    (transcript stdout stderr))]
           [(equal? answer "unsat") (result 'unsat '() (transcript "" stderr))]
           [(equal? answer "unknown") (result 'unknown '() (transcript stdout stderr))]
           [(not (equal? answer "sat"))
            (result 'malformed-response '() "expected exactly one of sat, unsat, or unknown"
                    (transcript stdout stderr))]
           [(null? inputs) (result 'sat '() (transcript "" stderr))]
           [else
            ;; A counterexample is only reported with a complete, well-formed
            ;; model. Anything less is a failure, never a success.
            (define-values (model-state model-code model-stdout model-stderr)
              (run "model" (model-script smtlib (map car inputs))))
            (define forms
              (with-handlers ([exn:fail? (lambda (_error) #f)])
                (map car (smtlib-commands model-stdout))))
            (cond
              [(eq? model-state 'timeout)
               (result 'timeout '()
                       (format "the solver answered sat, but did not report a model within ~a seconds and was terminated"
                               timeout)
                       (transcript model-stdout model-stderr))]
              [(not (and (eq? model-state 'exited) (eqv? model-code 0)))
               (result 'bad-model '()
                       (format "the solver answered sat, but requesting a model failed with status ~a"
                               model-code)
                       (transcript model-stdout model-stderr))]
              [(not (and forms (= (length forms) 2) (equal? (car forms) "sat")))
               (result 'bad-model '()
                       "the solver answered sat, but its get-value response was malformed"
                       (transcript model-stdout model-stderr))]
              [else
               (define-values (assignments reason) (parse-model (cadr forms) inputs))
               (if assignments
                   (result 'sat assignments (transcript "" model-stderr))
                   (result 'bad-model '()
                           (format "the solver answered sat, but ~a" reason)
                           (transcript model-stdout model-stderr)))])]))
       (lambda () (delete-directory/files directory #:must-exist? #f)))]))

;; What a solver needs before its first assertion to report which named
;; assertions cannot hold together. The solver's minimizing is asked for, but
;; is its best effort: `shrink-core` is what makes a core one none of whose
;; names can be left out.
(define core-options
  "(set-option :produce-unsat-cores true)\n(set-option :smt.core.minimize true)\n")

;; The names in a get-unsat-core response, or #f. A name is printed bare or
;; between bars.
(define (parse-core datum)
  (and (list? datum)
       (andmap string? datum)
       (for/list ([name (in-list datum)])
         (if (regexp-match? #rx"^[|].*[|]$" name)
             (substring name 1 (sub1 (string-length name)))
             name))))

;; `script` without the assertions that are named, other than those named in
;; `keep`. Everything else stands as it was: options, declarations, assertions
;; without a name, and the commands after them.
(define (keeping-named script keep)
  (define out (open-output-string))
  (define end
    (for/fold ([previous 0]) ([entry (in-list (smtlib-commands script))])
      (define name
        (match (car entry)
          [(list "assert" (list "!" _ ":named" (? string? name))) (car (parse-core (list name)))]
          [_ #f]))
      (unless (and name (not (member name keep)))
        (write-string (substring script previous (cdr entry)) out))
      (cdr entry)))
  (write-string (substring script end) out)
  (get-output-string out))

;; A solver's core is a set that cannot hold together, and may name more than
;; is needed. This leaves each name out in turn and asks again: where the rest
;; still cannot hold together, the name was not needed. `ask` takes the names
;; to keep and gives the core of that question where it is unsatisfiable, #f
;; where it is not or was not decided (the name is then kept, so the answer is
;; always a set that cannot hold together). Where every question was decided,
;; no name of the result can be left out. The solver's order is kept.
(define (shrink-core names ask)
  (for/fold ([core names]) ([name (in-list names)])
    (cond
      [(not (member name core)) core]
      [else
       (define rest (remove name core))
       (define smaller (ask rest))
       (if smaller
           (filter (lambda (kept) (member kept smaller)) rest)
           core)])))

;; Runs a feasibility script: named assertions, (check-sat), (get-unsat-core).
;; Status 'infeasible carries the core's names, shrunk until none can be left
;; out (`shrink-core`; each further question is a run of the solver, within
;; the same bound); 'feasible means the assertions can hold together (the core
;; request then fails, which is not an error here).
(define (run_solver_core smtlib [executable #f] [timeout 10] [arguments '()])
  (unless (string? smtlib) (raise-argument-error 'run_solver_core "string?" smtlib))
  (define extra (text-list 'run_solver_core arguments))
  (define started (current-inexact-milliseconds))
  (define deadline (+ started (* 1000.0 timeout)))
  (define-values (solver missing) (find-solver executable))
  (define command
    (append (list (if solver (path->string solver) (or (and executable (format "~a" executable)) "z3")))
            extra (list "<feasibility.smt2>")))
  (define (result status values . notes)
    (solver-result status values
                   (string->immutable-string (string-join (filter non-empty-string? notes) "\n"))
                   command
                   (/ (- (current-inexact-milliseconds) started) 1000.0)))
  (cond
    [(not solver) (result 'missing-executable '() missing)]
    [else
     (define directory (make-work-directory "pille-smt-~a"))
     (dynamic-wind
       void
       (lambda ()
         (define (attempt script)
           (define-values (state code stdout stderr)
             (run-script solver extra directory "feasibility" script deadline))
           (define forms
             (with-handlers ([exn:fail? (lambda (_error) #f)]) (map car (smtlib-commands stdout))))
           (cond
             [(eq? state 'failed) (result 'missing-executable '() (format "cannot run the solver: ~a" stderr))]
             [(eq? state 'timeout)
              (result 'timeout '() (format "the solver did not answer within ~a seconds and was terminated" timeout))]
             [(not (and forms (pair? forms)))
              (result 'malformed-response '() "expected sat, unsat, or unknown from the feasibility check" stdout stderr)]
             [(equal? (car forms) "sat") (result 'feasible '())]
             [(equal? (car forms) "unknown") (result 'unknown '())]
             [(and (equal? (car forms) "unsat") (pair? (cdr forms)) (parse-core (cadr forms)))
              => (lambda (names) (result 'infeasible names))]
             [else
              (result 'malformed-response '() "the solver answered unsat, but its unsat core was malformed" stdout stderr)]))
         (define first (attempt smtlib))
         (cond
           [(eq? (solver-result-status first) 'infeasible)
            (result 'infeasible
                    (shrink-core (solver-result-values first)
                                 (lambda (keep)
                                   (and (< (current-inexact-milliseconds) deadline)
                                        (let ([again (attempt (keeping-named smtlib keep))])
                                          (and (eq? (solver-result-status again) 'infeasible)
                                               (solver-result-values again)))))))]
           [else first]))
       (lambda () (delete-directory/files directory #:must-exist? #f)))]))

;; Runs an objective script: assertions, (minimize s) or (maximize s),
;; (check-sat), (get-value (s input ...)). `expected` is (name . width) for the
;; symbol and then each input. Status 'optimum carries their values; 'unsat
;; means no input satisfies the assertions (the value request then fails, which
;; is not an error here).
(define (run_solver_objective smtlib expected [executable #f] [timeout 10] [arguments '()])
  (unless (string? smtlib) (raise-argument-error 'run_solver_objective "string?" smtlib))
  (define extra (text-list 'run_solver_objective arguments))
  (define started (current-inexact-milliseconds))
  (define deadline (+ started (* 1000.0 timeout)))
  (define-values (solver missing) (find-solver executable))
  (define command
    (append (list (if solver (path->string solver) (or (and executable (format "~a" executable)) "z3")))
            extra (list "<objective.smt2>")))
  (define (result status values . notes)
    (solver-result status values
                   (string->immutable-string (string-join (filter non-empty-string? notes) "\n"))
                   command
                   (/ (- (current-inexact-milliseconds) started) 1000.0)))
  (cond
    [(not solver) (result 'missing-executable '() missing)]
    [else
     (define directory (make-work-directory "pille-smt-~a"))
     (dynamic-wind
       void
       (lambda ()
         (define-values (state code stdout stderr)
           (run-script solver extra directory "objective" smtlib deadline))
         (define forms
           (with-handlers ([exn:fail? (lambda (_error) #f)]) (map car (smtlib-commands stdout))))
         (cond
           [(eq? state 'failed) (result 'missing-executable '() (format "cannot run the solver: ~a" stderr))]
           [(eq? state 'timeout)
            (result 'timeout '() (format "the solver did not answer within ~a seconds and was terminated" timeout))]
           [(not (and forms (pair? forms)))
            (result 'malformed-response '() "expected sat, unsat, or unknown from the objective" stdout stderr)]
           [(equal? (car forms) "unsat") (result 'unsat '())]
           [(equal? (car forms) "unknown") (result 'unknown '() stdout)]
           [(and (equal? (car forms) "sat") (pair? (cdr forms)))
            (define-values (assignments reason) (parse-model (cadr forms) expected))
            (if assignments
                (result 'optimum assignments)
                (result 'bad-model '() (format "the solver answered sat, but ~a" reason) stdout stderr))]
           [else (result 'malformed-response '() "the solver answered sat without the objective's value" stdout stderr)]))
       (lambda () (delete-directory/files directory #:must-exist? #f)))]))
