#lang racket/base

(require racket/list)

(provide idle initial escalation re-escalation responded auto-disconnect
         on off disconnect respond time nothing
         machine-step machine-run
         unrolled-machine-text stepped-machine-text)

;; A small timed machine, for the tests of CLOSER_TIMED_MACHINE_WORK_ORDER.md
;; (smt-synthesis.rkt, smt-bounded.rkt). It is a fixture: nothing in the
;; library knows of phases or messages.
;;
;; The state is (phase, level, since, clock), each an i32. Its durations are
;; inputs: `initial` and `escalation`, then a `repeat` between re-escalations.
;; Each message is a kind and an amount:
;;
;;   0 on          idle -> initial, since := clock
;;   1 off         -> idle
;;   2 disconnect  -> idle
;;   3 respond     initial, escalation or re-escalation -> responded
;;   4 time        clock := clock + amount
;;   other         nothing
;;
;; and after every message a timed phase is what the time since `since` makes
;; it: initial before `initial`, escalation before `initial + escalation`, then
;; re-escalation at level 1, 2, 3 as each further `repeat` passes, and 4 after.
;;
;; No message takes the machine to `auto-disconnect`. The altered machine
;; (#:altered? #t) is one with a fault: a disconnect of an alarm that is on
;; (initial, escalation or re-escalation) goes there, not to idle.

(define-values (idle initial escalation re-escalation responded auto-disconnect) (values 0 1 2 3 5 6))
(define-values (on off disconnect respond time nothing) (values 0 1 2 3 4 9))

(define (wrap32 value) (modulo value (expt 2 32)))
(define (timed? phase) (and (memv phase (list initial escalation re-escalation)) #t))

;;==============================================================================
;; The machine, written on numbers

(define (machine-step state durations kind amount #:altered? [altered? #f])
  (define-values (phase level since clock) (apply values state))
  (define-values (I E R) (apply values durations))
  (define start? (and (= kind on) (= phase idle)))
  (define clock* (if (= kind time) (wrap32 (+ clock amount)) clock))
  (define since* (if start? clock since))
  (define phase1
    (let* ([p-on (if start? initial phase)]
           [p (if (= kind off) idle p-on)]
           [p (if (= kind disconnect) idle p)]
           [p (if (and altered? (= kind disconnect) (timed? p-on)) auto-disconnect p)])
      (if (and (= kind respond) (timed? p)) responded p)))
  (cond
    [(timed? phase1)
     (define elapsed (wrap32 (- clock* since*)))
     (define-values (l0 l1 l2 l3)
       (values (wrap32 (+ I E)) (wrap32 (+ I E R)) (wrap32 (+ I E R R)) (wrap32 (+ I E R R R))))
     (list (cond [(< elapsed I) initial] [(< elapsed l0) escalation] [else re-escalation])
           (cond [(< elapsed l0) 0] [(< elapsed l1) 1] [(< elapsed l2) 2] [(< elapsed l3) 3] [else 4])
           since* clock*)]
    [else (list phase1 0 since* clock*)]))

(define (machine-run durations kinds amounts #:altered? [altered? #f])
  (for/fold ([state (list idle 0 0 0)]) ([kind (in-list kinds)] [amount (in-list amounts)])
    (machine-step state durations kind amount #:altered? altered?)))

;;==============================================================================
;; The machine as MLIR: the fixture dialect's add and sub, arith.constant,
;; arith.cmpi and arith.select

(define (emitter out)
  (define (line format-string . arguments) (fprintf out "    ~a\n" (apply format format-string arguments)))
  (values
   line
   (lambda (name value) (line "%~a = arith.constant ~a : i32" name value))
   (lambda (name operation lhs rhs) (line "%~a = \"arithmetic.~a\"(%~a, %~a) : (i32, i32) -> i32" name operation lhs rhs))
   (lambda (name predicate lhs rhs) (line "%~a = arith.cmpi ~a, %~a, %~a : i32" name predicate lhs rhs))
   (lambda (name test chosen otherwise type) (line "%~a = arith.select %~a, %~a, %~a : ~a" name test chosen otherwise type))))

;; The constants and the durations' sums a step uses, named for all steps of one function.
(define (emit-preamble out)
  (define-values (line constant op compare choose) (emitter out))
  (for ([value '(0 1 2 3 4 5 6)]) (constant (format "c~a" value) value))
  (line "%no = arith.constant false")
  (line "%yes = arith.constant true")
  (op "l0" "add" "I" "E")
  (op "l1" "add" "l0" "R")
  (op "l2" "add" "l1" "R")
  (op "l3" "add" "l2" "R"))

;; One step, its names ending in `suffix`: gives the names of the new phase,
;; level, since and clock.
(define (emit-step out suffix m d phase level since clock altered?)
  (define-values (line constant op compare choose) (emitter out))
  (define (n name) (format "~a_~a" name suffix))
  (define (timed name of)
    (compare (format "~a_1" name) "eq" of "c1")
    (compare (format "~a_2" name) "eq" of "c2")
    (compare (format "~a_3" name) "eq" of "c3")
    (choose (format "~a_23" name) (format "~a_2" name) "yes" (format "~a_3" name) "i1")
    (choose name (format "~a_1" name) "yes" (format "~a_23" name) "i1"))
  (compare (n "is_on") "eq" m "c0")
  (compare (n "is_off") "eq" m "c1")
  (compare (n "is_dis") "eq" m "c2")
  (compare (n "is_resp") "eq" m "c3")
  (compare (n "is_time") "eq" m "c4")
  (compare (n "was_idle") "eq" phase "c0")
  (choose (n "start") (n "is_on") (n "was_idle") "no" "i1")
  (op (n "later") "add" clock d)
  (choose (n "clock") (n "is_time") (n "later") clock "i32")
  (choose (n "since") (n "start") clock since "i32")
  (choose (n "p_on") (n "start") "c1" phase "i32")
  (choose (n "p_off") (n "is_off") "c0" (n "p_on") "i32")
  (choose (n "p_idle") (n "is_dis") "c0" (n "p_off") "i32")
  (cond
    [altered?
     (timed (n "was_on") (n "p_on"))
     (choose (n "to_auto") (n "is_dis") (n "was_on") "no" "i1")
     (choose (n "p_dis") (n "to_auto") "c6" (n "p_idle") "i32")]
    [else (choose (n "p_dis") "yes" (n "p_idle") (n "p_idle") "i32")])
  (timed (n "can_respond") (n "p_dis"))
  (choose (n "responds") (n "is_resp") (n "can_respond") "no" "i1")
  (choose (n "p_resp") (n "responds") "c5" (n "p_dis") "i32")
  (timed (n "timed") (n "p_resp"))
  (op (n "elapsed") "sub" (n "clock") (n "since"))
  (compare (n "lt_i") "ult" (n "elapsed") "I")
  (compare (n "lt_0") "ult" (n "elapsed") "l0")
  (compare (n "lt_1") "ult" (n "elapsed") "l1")
  (compare (n "lt_2") "ult" (n "elapsed") "l2")
  (compare (n "lt_3") "ult" (n "elapsed") "l3")
  (choose (n "tp_e") (n "lt_0") "c2" "c3" "i32")
  (choose (n "tp") (n "lt_i") "c1" (n "tp_e") "i32")
  (choose (n "tl_3") (n "lt_3") "c3" "c4" "i32")
  (choose (n "tl_2") (n "lt_2") "c2" (n "tl_3") "i32")
  (choose (n "tl_1") (n "lt_1") "c1" (n "tl_2") "i32")
  (choose (n "tl") (n "lt_0") "c0" (n "tl_1") "i32")
  (choose (n "phase") (n "timed") (n "tp") (n "p_resp") "i32")
  (choose (n "level") (n "timed") (n "tl") "c0" "i32")
  (values (n "phase") (n "level") (n "since") (n "clock")))

(define (message-arguments count)
  (apply string-append (for/list ([k (in-range count)]) (format ", %m~a: i32, %d~a: i32" k k))))

;; @machine(I, E, R, m0, d0, ...) -> (phase, level, since, clock): the step
;; written out in the function's body once for each message.
(define (unrolled-machine-text messages #:altered? [altered? #f])
  (define out (open-output-string))
  (fprintf out "  func.func @machine(%I: i32, %E: i32, %R: i32~a) -> (i32, i32, i32, i32) {\n"
           (message-arguments messages))
  (emit-preamble out)
  (define-values (phase level since clock)
    (for/fold ([phase "c0"] [level "c0"] [since "c0"] [clock "c0"]) ([k (in-range messages)])
      (emit-step out k (format "m~a" k) (format "d~a" k) phase level since clock altered?)))
  (fprintf out "    return %~a, %~a, %~a, %~a : i32, i32, i32, i32\n  }\n" phase level since clock)
  (get-output-string out))

;; @step(phase, level, since, clock, I, E, R, m, d) -> (phase, level, since,
;; clock), written once, and @run(I, E, R, m0, d0, ...) that calls it once for
;; each message and returns the phase after each of them, in order.
(define (stepped-machine-text messages #:altered? [altered? #f])
  (define out (open-output-string))
  (fprintf out "  func.func private @step(%phase: i32, %level: i32, %since: i32, %clock: i32, %I: i32, %E: i32, %R: i32, %m: i32, %d: i32) -> (i32, i32, i32, i32) {\n")
  (emit-preamble out)
  (define-values (phase level since clock) (emit-step out "s" "m" "d" "phase" "level" "since" "clock" altered?))
  (fprintf out "    return %~a, %~a, %~a, %~a : i32, i32, i32, i32\n  }\n" phase level since clock)
  (fprintf out "  func.func @run(%I: i32, %E: i32, %R: i32~a) -> (~a) {\n"
           (message-arguments messages)
           (apply string-append (add-between (make-list messages "i32") ", ")))
  (fprintf out "    %zero = arith.constant 0 : i32\n")
  (define states
    (for/fold ([states '()]) ([k (in-range messages)])
      (define (previous index) (if (null? states) "%zero" (format "%~a#~a" (car states) index)))
      (fprintf out "    %s~a:4 = func.call @step(~a, ~a, ~a, ~a, %I, %E, %R, %m~a, %d~a) : (i32, i32, i32, i32, i32, i32, i32, i32, i32) -> (i32, i32, i32, i32)\n"
               k (previous 0) (previous 1) (previous 2) (previous 3) k k)
      (cons (format "s~a" k) states)))
  (fprintf out "    return ~a : ~a\n  }\n"
           (apply string-append (add-between (for/list ([state (in-list (reverse states))]) (format "%~a#0" state)) ", "))
           (apply string-append (add-between (make-list messages "i32") ", ")))
  (get-output-string out))
