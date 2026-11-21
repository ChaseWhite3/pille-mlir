#lang racket/base

(require rackunit
         racket/file
         racket/list
         racket/port
         racket/system
         racket/runtime-path
         racket/string
         racket/treelist
         "../../private/mlir/query.rkt"
         "../../private/mlir/schema.rkt"
         "../../private/mlir/session.rkt"
         "../../private/mlir/solver.rkt"
         "../../private/mlir/tools.rkt"
         "machine-fixture.rkt")

;; Slice B of CLOSER_TIMED_MACHINE_WORK_ORDER.md: a step written once and called
;; for each message, questions asked of one solver as the number of messages
;; grows, and counterexamples of many inputs. These need real MLIR tools and a
;; real Z3; a missing tool is a failure, not a skip.
(define-runtime-path fixtures "semantics")
(define arithmetic (dynamic-require (build-path fixtures "valid.rhm") 'arithmetic))

(define chain (make_toolchain))

;; Every question here is exported both ways, by the lowering itself and by
;; mlir-translate, and the two texts must be the same.
(smt_export_mode 'both)
(define z3
  (or (getenv "PILLE_Z3")
      (find-executable-path "z3")
      (error 'smt-bounded "these tests require Z3: put z3 on PATH or set PILLE_Z3")))

(define (program . functions)
  (parse_module (string-append "module {\n" (apply string-append functions) "}\n")
                (dialect_irdl arithmetic) chain))
(define (query module function inputs property [preconditions '()])
  (make_smt_query arithmetic module function inputs property preconditions))
(define (status value) (solver_result_status (query_check value z3)))
(define (rejects pattern thunk)
  (check-exn (lambda (error) (and (exn:fail? error) (regexp-match? pattern (exn-message error)))) thunk))

(define a32 (smt_input "a" 32))
(define b32 (smt_input "b" 32))
(define r32 (smt_result 32))
(define (is term value) (smt_eq term (smt_const value 32)))

;;==============================================================================
;; B1. Calls inlined

(define calls
  (program
   "  func.func private @inc(%x: i32) -> i32 {\n    %one = arith.constant 1 : i32\n    %r = \"arithmetic.add\"(%x, %one) : (i32, i32) -> i32\n    return %r : i32\n  }\n"
   ;; the same names as its caller uses, for other values
   "  func.func private @both(%a0: i32, %a1: i32) -> (i32, i1) {\n    %r = \"arithmetic.add\"(%a0, %a1) : (i32, i32) -> i32\n    %c = arith.cmpi ult, %a0, %a1 : i32\n    return %r, %c : i32, i1\n  }\n"
   "  func.func @thrice(%a0: i32) -> i32 {\n    %x = func.call @inc(%a0) : (i32) -> i32\n    %y = func.call @inc(%x) : (i32) -> i32\n    %r = func.call @inc(%y) : (i32) -> i32\n    return %r : i32\n  }\n"
   ;; a call inside a called function, and a callee of several results
   "  func.func private @inc2(%x: i32) -> i32 {\n    %y = func.call @inc(%x) : (i32) -> i32\n    %r = func.call @inc(%y) : (i32) -> i32\n    return %r : i32\n  }\n"
   "  func.func @nested(%a0: i32, %a1: i32) -> (i32, i1) {\n    %r = func.call @inc2(%a0) : (i32) -> i32\n    %s:2 = func.call @both(%r, %a1) : (i32, i32) -> (i32, i1)\n    return %s#0, %s#1 : i32, i1\n  }\n"
   ;; what is refused
   "  func.func @loops(%a0: i32) -> i32 {\n    %r = func.call @loops(%a0) : (i32) -> i32\n    return %r : i32\n  }\n"
   "  func.func @ping(%a0: i32) -> i32 {\n    %r = func.call @pong(%a0) : (i32) -> i32\n    return %r : i32\n  }\n"
   "  func.func @pong(%a0: i32) -> i32 {\n    %r = func.call @ping(%a0) : (i32) -> i32\n    return %r : i32\n  }\n"
   "  func.func private @declared(i32) -> i32\n"
   "  func.func @outside(%a0: i32) -> i32 {\n    %r = func.call @declared(%a0) : (i32) -> i32\n    return %r : i32\n  }\n"
   "  func.func private @branches(%a0: i32) -> i32 {\n    cf.br ^next\n  ^next:\n    return %a0 : i32\n  }\n"
   "  func.func @jumps(%a0: i32) -> i32 {\n    %r = func.call @branches(%a0) : (i32) -> i32\n    return %r : i32\n  }\n"
   "  func.func private @adds(%a0: i32) -> i32 {\n    %r = arith.addi %a0, %a0 : i32\n    return %r : i32\n  }\n"
   "  func.func @unmodeled(%a0: i32) -> i32 {\n    %r = func.call @adds(%a0) : (i32) -> i32\n    return %r : i32\n  }\n"))

;; What `z3` prints for a script, run by hand.
(define (by-hand script)
  (define file (make-temporary-file "pille-smt-by-hand-~a.smt2"))
  (dynamic-wind
    void
    (lambda ()
      (display-to-file script file #:exists 'truncate)
      (string-trim (regexp-replace* #rx"\r\n" (with-output-to-string (lambda () (system* z3 (path->string file))))
                                    "\n")))
    (lambda () (delete-file file))))

(test-case "a call is the called function's body, where the call stands"
  (check-eq? (status (query calls "thrice" (list a32) (smt_eq r32 (smt_binary 'add a32 (smt_const 3 32))))) 'unsat)
  (check-eq? (status (query calls "thrice" (list a32) (smt_eq r32 (smt_binary 'add a32 (smt_const 2 32))))) 'sat)
  ;; a call within a call, and each of a callee's results
  (define nested
    (query calls "nested" (list a32 b32)
           (smt_and (list (smt_eq (smt_result_at 0 32)
                                  (smt_binary 'add (smt_binary 'add a32 (smt_const 2 32)) b32))
                          (smt_eq (smt_result_at 1 1)
                                  (smt_ite (smt_cmp 'ult (smt_binary 'add a32 (smt_const 2 32)) b32)
                                           (smt_const 1 1) (smt_const 0 1)))))))
  (check-eq? (status nested) 'unsat)
  ;; nothing of the calls or the dialect is left in what the solver is given
  (check-false (regexp-match? #rx"func\\.|arithmetic\\.|arith\\." (module_ir (query_module nested)))))

(test-case "the lowering's own SMT-LIB is the exporter's, whatever the inputs are called, and each mode gives one text"
  ;; the exporter names what it binds tmp, tmp_0, tmp_1, ..., passing over a name an input has
  (for ([names (in-list '(("tmp" "tmp_0") ("tmp_0" "tmp") ("tmp_1" "tmp_3") ("tmp_2" "b")))])
    (define first (smt_input (car names) 32))
    (define second (smt_input (cadr names) 32))
    (define sum (smt_binary 'add (smt_binary 'add first (smt_const 2 32)) second))
    (define asked (query calls "nested" (list first second) (smt_eq (smt_result_at 0 32) sum)
                         (list (smt_cmp 'ult first (smt_const 9 32)))))
    (check-eq? (status asked) 'unsat)
    (check-equal? (by-hand (query_smtlib asked)) "unsat"))
  ;; the three modes: the same text, and the module verified when it is asked for
  (define (text-in mode)
    (parameterize ([smt_export_mode mode])
      (define asked (query calls "thrice" (list a32) (smt_eq r32 (smt_binary 'add a32 (smt_const 3 32)))))
      (check-true (is_module (query_module asked)))
      (query_smtlib asked)))
  (check-equal? (text-in 'direct) (text-in 'tools))
  (check-equal? (text-in 'direct) (text-in 'both))
  ;; where no tool ran the lowering wrote no SMT operations; asked for, the module is lowered then, and is
  ;; the one the tools were given: a query's, and each member's of a batch
  (define (modules-in mode)
    (parameterize ([smt_export_mode mode])
      (define specs (list (make_spec "thrice" (list a32) (smt_eq r32 (smt_binary 'add a32 (smt_const 3 32))) '())
                          (make_spec "nested" (list a32 b32) (smt_eq (smt_result_at 0 32) a32) '())))
      (define batch (make_smt_batch arithmetic calls specs))
      (cons (module_ir (query_module (query calls "thrice" (list a32) (smt_eq r32 a32))))
            (cons (module_ir (batch_module batch))
                  (for/list ([member (in-treelist (batch_queries batch))]) (module_ir (query_module member)))))))
  (check-equal? (modules-in 'direct) (modules-in 'tools))
  (check-equal? (length (modules-in 'direct)) 4)
  (check-exn #rx"smt_export_mode" (lambda () (smt_export_mode 'neither))))

(test-case "a call that cannot be inlined is refused, naming it"
  (define trivial (smt_eq r32 r32))
  (rejects #rx"recursive call to @loops [(]@loops calls @loops[)]; a call is inlined, so recursion is unsupported"
           (lambda () (query calls "loops" (list a32) trivial)))
  (rejects #rx"recursive call to @ping [(]@ping calls @pong calls @ping[)]"
           (lambda () (query calls "ping" (list a32) trivial)))
  (rejects #rx"call to @declared, which is a declaration without a body"
           (lambda () (query calls "outside" (list a32) trivial)))
  (rejects #rx"unsupported control flow: called function @branches has 2 blocks"
           (lambda () (query calls "jumps" (list a32) trivial)))
  ;; a callee is held to the fragment as a selected function is, by name
  (rejects #rx"unsupported operation 'arith.addi'" (lambda () (query calls "unmodeled" (list a32) trivial)))
  ;; and the refusal says where: the place of the call or of the operation
  (check-regexp-match #rx"<stdin>:[0-9]+:[0-9]+"
                      (with-handlers ([exn:fail? exn-message]) (query calls "outside" (list a32) trivial))))

;;==============================================================================
;; B2. A scope on a session, and objectives asked of one

(define (scope-status scope property) (solver_result_status (scope_check scope property)))
(define (lt term value) (smt_cmp 'ult term (smt_const value 32)))

(test-case "a scope keeps its assumptions from one question to the next, and each question leaves it as it was"
  (define s (make_session z3))
  (define scope (make_smt_scope s arithmetic calls "thrice" (list a32)))
  (check-true (scope_is_open scope))
  ;; nothing assumed: a + 3 < 13 does not hold for every a
  (check-eq? (scope-status scope (lt r32 13)) 'sat)
  (scope_assert scope (lt a32 10))
  (check-eq? (scope-status scope (lt r32 13)) 'unsat)
  (check-eq? (scope-status scope (lt r32 12)) 'sat)
  ;; a question's own assertion is gone when it has been answered
  (check-eq? (scope-status scope (lt r32 13)) 'unsat)
  ;; a frame of further assumptions, and its end
  (scope_push scope)
  (scope_assert scope (is a32 5))
  (check-equal? (treelist->list (scope_assumptions scope)) '("a <u 0x0000000a:bv32" "a == 0x00000005:bv32"))
  (check-eq? (scope-status scope (is r32 8)) 'unsat)
  (define refuted (scope_check scope (is r32 9)))
  (check-eq? (solver_result_status refuted) 'sat)
  (check-equal? (solver_result_values refuted) '(("a" 32 5)))
  (scope_pop scope)
  (check-equal? (treelist->list (scope_assumptions scope)) '("a <u 0x0000000a:bv32"))
  (check-eq? (scope-status scope (is r32 8)) 'sat)
  ;; assumptions that cannot hold together prove anything, as a query's do
  (scope_push scope)
  (scope_assert scope (smt_cmp 'ugt a32 (smt_const 20 32)))
  (check-eq? (scope-status scope (is r32 0)) 'unsat)
  ;; the question as one script gives the same answer run by hand
  (check-equal? (by-hand (scope_goal_script scope (is r32 0))) "unsat")
  (scope_pop scope)
  (check-equal? (by-hand (scope_goal_script scope (lt r32 13))) "unsat")
  (check-equal? (by-hand (scope_goal_script scope (lt r32 12))) "sat")
  ;; only what was pushed can be popped
  (rejects #rx"nothing was pushed on this scope" (lambda () (scope_pop scope)))
  ;; while it is open the session takes nothing else, nor a second scope
  (define plain (query calls "thrice" (list a32) (lt r32 13)))
  (rejects #rx"a scope is open on this session" (lambda () (query_session_check s plain)))
  (rejects #rx"a scope is open on this session" (lambda () (make_smt_scope s arithmetic calls "thrice" (list a32))))
  ;; several questions asked together are each answered as alone, in order, counterexamples included, and
  ;; leave the scope as it was; no question is no answer
  (define several (treelist->list (scope_check_all scope (list (lt r32 13) (lt r32 12) (is r32 9)))))
  (check-equal? (for/list ([entry (in-list several)]) (solver_result_status (treelist-ref entry 1)))
                (list (scope-status scope (lt r32 13)) (scope-status scope (lt r32 12)) (scope-status scope (is r32 9))))
  (check-equal? (solver_result_values (treelist-ref (cadr several) 1))
                (solver_result_values (scope_check scope (lt r32 12))))
  (check-equal? (treelist->list (scope_assumptions scope)) '("a <u 0x0000000a:bv32"))
  (check-equal? (treelist->list (scope_check_all scope '())) '())
  (rejects #rx"check_all: expected a Boolean predicate" (lambda () (scope_check_all scope (list (lt r32 13) a32))))
  (scope_close scope)
  (check-false (scope_is_open scope))
  (rejects #rx"the scope is closed" (lambda () (scope_check scope (lt r32 13))))
  ;; and then it does: nothing of the scope is left in the solver
  (check-eq? (solver_result_status (query_session_check s plain)) 'sat)
  (define again (make_smt_scope s arithmetic calls "thrice" (list a32)))
  (check-eq? (scope-status again (lt r32 13)) 'sat)
  (scope_close again)
  (close_session s))

(test-case "an objective asked of a session is the standalone one's answer"
  (define s (make_session z3))
  (define (both value)
    (define alone (objective_check value z3))
    (define within (objective_session_check s value))
    (check-eq? (solver_result_status within) (solver_result_status alone))
    (and (eq? (solver_result_status within) 'optimum)
         (check-equal? (objective_value value (caddr (car (solver_result_values within))))
                       (objective_value value (caddr (car (solver_result_values alone)))))
         (objective_value value (caddr (car (solver_result_values within))))))
  (define three (smt_const 3 32))
  (check-equal? (both (make_smt_objective arithmetic calls "thrice" (list a32) a32 'maximize #f
                                          (list (smt_no_overflow 'add a32 three #f))))
                (- (expt 2 32) 4))
  ;; the least signed a + 3 with a >= -7: the least number there is, where the sum may wrap,
  ;; and -4 where it may not
  (check-equal? (both (make_smt_objective arithmetic calls "thrice" (list a32) r32 'minimize #t
                                          (list (smt_cmp 'sge a32 (smt_const -7 32)))))
                (- (expt 2 31)))
  (check-equal? (both (make_smt_objective arithmetic calls "thrice" (list a32) r32 'minimize #t
                                          (list (smt_cmp 'sge a32 (smt_const -7 32))
                                                (smt_no_overflow 'add a32 three #t))))
                -4)
  ;; named preconditions that cannot hold together: the core, from the session too
  (define conflict
    (make_smt_objective arithmetic calls "thrice" (list a32) a32 'minimize #f
                        (list (smt_named (lt a32 3) "low") (smt_named (smt_cmp 'ugt a32 (smt_const 9 32)) "high"))))
  (define refused (objective_session_check s conflict))
  (check-eq? (solver_result_status refused) 'infeasible)
  (check-equal? (sort (treelist->list (solver_result_core refused)) string<?) '("high" "low"))
  ;; and the session's solver is as it was for the next question
  (define next (query_session_check s (query calls "thrice" (list a32) (lt r32 13))))
  (check-eq? (solver_result_status next) 'sat)
  (close_session s))

;;==============================================================================
;; B3. A counterexample of many inputs

(test-case "200 inputs, of 8 and of 32 bits, are reported in argument order with the values asked"
  ;; (the fragment's widths are 1, 8, 16, 32 and 64: 8 stands for a small field)
  (define count 200)
  (define widths (for/list ([index (in-range count)]) (if (even? index) 8 32)))
  (define inputs (for/list ([index (in-range count)] [width (in-list widths)]) (smt_input (format "x~a" index) width)))
  (define wanted
    (for/list ([index (in-range count)] [width (in-list widths)]) (modulo (+ 7 (* index index 2654435761)) (expt 2 width))))
  (define wide
    (program (format "  func.func @wide(~a) -> i8 {\n    return %a0 : i8\n  }\n"
                     (string-join (for/list ([index (in-range count)] [width (in-list widths)]) (format "%a~a: i~a" index width)) ", "))))
  ;; "some input is not the value asked": refuted only by exactly those values
  (define property
    (smt_not (smt_and (for/list ([input (in-list inputs)] [value (in-list wanted)] [width (in-list widths)])
                        (smt_eq input (smt_const value width))))))
  (define expected (for/list ([index (in-range count)] [width (in-list widths)] [value (in-list wanted)])
                     (list (format "x~a" index) width value)))
  (define value (query wide "wide" inputs property))
  (define alone (query_check value z3 10))
  (check-eq? (solver_result_status alone) 'sat)
  (check-equal? (solver_result_values alone) expected)
  (check-true (< (solver_result_seconds alone) 10))
  (define s (make_session z3))
  (check-equal? (solver_result_values (query_session_check s value 10)) expected)
  (define scope (make_smt_scope s arithmetic wide "wide" inputs))
  (check-equal? (solver_result_values (scope_check scope property 10)) expected)
  (scope_close scope)
  (close_session s))

;;==============================================================================
;; Acceptance for Slice B: the fixture's step, written once and called for each
;; of twelve messages (machine-fixture.rkt)

(define depth 12)
(define sound (program (stepped-machine-text depth)))
(define faulty (program (stepped-machine-text depth #:altered? #t)))

(define-values (I E R) (values (smt_input "I" 32) (smt_input "E" 32) (smt_input "R" 32)))
(define kinds (for/list ([k (in-range depth)]) (smt_input (format "m~a" k) 32)))
(define amounts (for/list ([k (in-range depth)]) (smt_input (format "d~a" k) 32)))
(define run-inputs (append (list I E R) (append* (map list kinds amounts))))
;; the phase after each of the first `count` messages is not auto-disconnect
(define (never count)
  (smt_and (for/list ([k (in-range count)]) (smt_not (is (smt_result_at k 32) auto-disconnect)))))

(test-case "the called step is the machine written on numbers, sound and faulty, on random message sequences"
  (define generator (make-pseudo-random-generator))
  (parameterize ([current-pseudo-random-generator generator])
    (random-seed 20261121)
    (for ([module (list sound faulty)] [altered? '(#f #t)])
      (define specs
        (for/list ([_ (in-range 40)])
          (define durations (list (random 1 20) (random 1 40) (random 1 30)))
          (define said-kinds (for/list ([_ (in-range depth)]) (list-ref (list on off disconnect respond time time time nothing) (random 8))))
          (define said-amounts (for/list ([_ (in-range depth)]) (random 0 60)))
          (define phases
            (for/list ([count (in-range 1 (add1 depth))])
              (first (machine-run durations (take said-kinds count) (take said-amounts count) #:altered? altered?))))
          (make_spec "run" run-inputs
                     (smt_and (for/list ([phase (in-list phases)] [k (in-naturals)]) (is (smt_result_at k 32) phase)))
                     (append (list (is I (first durations)) (is E (second durations)) (is R (third durations)))
                             (append* (for/list ([kind (in-list kinds)] [amount (in-list amounts)]
                                                 [said-kind (in-list said-kinds)] [said-amount (in-list said-amounts)])
                                        (list (is kind said-kind) (is amount said-amount))))))))
      (define answers (treelist->list (batch_check (make_smt_batch arithmetic module specs) z3 20 '() 600)))
      (check-equal? (remove-duplicates (map solver_result_status answers)) '(unsat)))))

(test-case "acceptance: twelve symbolic messages never reach auto-disconnect, and the faulty step does"
  (check-eq? (status (query sound "run" run-inputs (never depth))) 'unsat)
  (define broken (query_check (query faulty "run" run-inputs (never depth)) z3 60))
  (check-eq? (solver_result_status broken) 'sat)
  ;; the counterexample's messages hold a disconnect after an on
  (define found (for/hash ([entry (in-list (solver_result_values broken))]) (values (car entry) (caddr entry))))
  (define said-kinds (for/list ([k (in-range depth)]) (hash-ref found (format "m~a" k))))
  (define said-amounts (for/list ([k (in-range depth)]) (hash-ref found (format "d~a" k))))
  (check-true (for*/or ([i (in-range depth)] [j (in-range (add1 i) depth)])
                (and (= (list-ref said-kinds i) on) (= (list-ref said-kinds j) disconnect))))
  ;; replayed on numbers, it reaches auto-disconnect in the faulty machine and not in the sound one
  (define durations (list (hash-ref found "I") (hash-ref found "E") (hash-ref found "R")))
  (define (phases altered?)
    (for/list ([count (in-range 1 (add1 depth))])
      (first (machine-run durations (take said-kinds count) (take said-amounts count) #:altered? altered?))))
  (check-true (and (memv auto-disconnect (phases #t)) #t))
  (check-false (memv auto-disconnect (phases #f))))

(test-case "acceptance: deepening from 1 to 12 in one session gives what fresh queries give"
  (for ([module (list sound faulty)]
        ;; one message cannot be an on and then a disconnect
        [expected (list (make-list depth 'unsat) (cons 'unsat (make-list (sub1 depth) 'sat)))])
    (define fresh (for/list ([count (in-range 1 (add1 depth))]) (status (query module "run" run-inputs (never count)))))
    (check-equal? fresh expected)
    (define s (make_session z3))
    (define scope (make_smt_scope s arithmetic module "run" run-inputs))
    (define deepened
      (for/list ([count (in-range 1 (add1 depth))]) (solver_result_status (scope_check scope (never count) 60))))
    (check-equal? deepened fresh)
    ;; asked together, their formulas lowered in one pass: the same answers, and each one's script, run by
    ;; hand, gives its answer
    (define together (treelist->list (scope_check_all scope (for/list ([count (in-range 1 (add1 depth))]) (never count)) 60)))
    (check-equal? (for/list ([entry (in-list together)]) (solver_result_status (treelist-ref entry 1))) fresh)
    (check-equal? (for/list ([entry (in-list together)]) (string->symbol (by-hand (treelist-ref entry 0)))) fresh)
    ;; under an assumption kept in the scope: with no disconnect said, the faulty machine is sound too
    (scope_assert scope (smt_and (for/list ([kind (in-list kinds)]) (smt_not (is kind disconnect)))))
    (check-equal? (for/list ([count (in-range 1 (add1 depth))]) (solver_result_status (scope_check scope (never count) 60)))
                  (make-list depth 'unsat))
    (scope_close scope)
    (close_session s)))

;;==============================================================================
;; A scope's solver holds the function's body

;; The same questions of a scope that sends the body once and of one that
;; sends each question whole, as the tools export it.
(define (asked-both-ways module function inputs assumptions claims)
  (for/list ([mode '(direct tools)])
    (parameterize ([smt_export_mode mode])
      (define s (make_session z3))
      (define scope (make_smt_scope s arithmetic module function inputs))
      (for ([assumption (in-list assumptions)]) (scope_assert scope assumption))
      (define answers
        (for/list ([entry (in-treelist (scope_check_all scope claims 60))])
          (define answer (treelist-ref entry 1))
          ;; a counterexample is one of perhaps many: what is compared is that there is one, and each
          ;; question's script, run by hand, says the same
          (check-equal? (by-hand (treelist-ref entry 0)) (symbol->string (solver_result_status answer)))
          (solver_result_status answer)))
      (define script (scope_goal_script scope (car claims)))
      (scope_close scope)
      (close_session s)
      (list answers (regexp-match? #rx"define-fun" script)))))

(test-case "a scope that sends the body once answers as one that sends every question whole"
  (for ([module (list sound faulty)])
    (define claims (for/list ([count (in-range 1 (add1 depth))]) (never count)))
    (define plain (asked-both-ways module "run" run-inputs '() claims))
    ;; the first defines the body, the second does not, and the answers are the same
    (check-equal? (map cadr plain) '(#t #f))
    (check-equal? (car (car plain)) (car (cadr plain)))
    (define assuming
      (asked-both-ways module "run" run-inputs
                       (list (smt_cmp 'ult I (smt_const 9 32))
                             (smt_and (for/list ([kind (in-list (cdr kinds))]) (smt_not (is kind disconnect)))))
                       claims))
    (check-equal? (car (car assuming)) (car (cadr assuming))))
  ;; a claim's own text is its formula: it does not grow with the body
  (define s (make_session z3))
  (define scope (make_smt_scope s arithmetic sound "run" run-inputs))
  (define held (string-length (scope_goal_script scope (never 1))))
  (check-true (< (- (string-length (scope_goal_script scope (never 2))) held) 400))
  (scope_close scope)
  (close_session s))

(test-case "the body's definitions keep clear of the inputs' names, and its requirements are still to be shown"
  ;; inputs named as the definitions would be
  (define first (smt_input "pille_v0" 32))
  (define second (smt_input "pille_v_1" 32))
  (define sum (smt_binary 'add (smt_binary 'add first (smt_const 2 32)) second))
  (define s (make_session z3))
  (define scope (make_smt_scope s arithmetic calls "nested" (list first second)))
  (check-eq? (solver_result_status (scope_check scope (smt_eq (smt_result_at 0 32) sum))) 'unsat)
  (define refuted (scope_check scope (smt_eq (smt_result_at 0 32) first)))
  (check-eq? (solver_result_status refuted) 'sat)
  (check-equal? (map car (solver_result_values refuted)) '("pille_v0" "pille_v_1"))
  (check-equal? (by-hand (scope_goal_script scope (smt_eq (smt_result_at 0 32) sum))) "unsat")
  (scope_close scope)
  ;; an operation whose model requires something of its operand: a claim is not proved where the
  ;; requirement may fail, and is where the scope assumes it holds
  (define choice (dynamic-require (build-path fixtures "valid.rhm") 'choice))
  (define before
    (parse_module "module {\n  func.func @before(%a0: i32) -> i32 {\n    %r = \"choice.predecessor\"(%a0) : (i32) -> i32\n    return %r : i32\n  }\n}\n"
                  (dialect_irdl choice) chain))
  (define within (make_smt_scope s choice before "before" (list a32)))
  (define trivial (smt_eq r32 r32))
  (check-eq? (solver_result_status (scope_check within trivial)) 'sat)
  (scope_assert within (smt_eq a32 (smt_const 2 32)))
  (check-eq? (solver_result_status (scope_check within trivial)) 'unsat)
  (check-eq? (solver_result_status (scope_check within (smt_eq r32 (smt_const 1 32)))) 'unsat)
  (check-equal? (by-hand (scope_goal_script within trivial)) "unsat")
  ;; and it is what a whole query says
  (check-eq? (solver_result_status (query_check (make_smt_query choice before "before" (list a32) trivial '()) z3)) 'sat)
  (scope_close within)
  (close_session s))
