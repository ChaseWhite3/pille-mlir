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
         "../../private/mlir/tools.rkt")

;; What a query needs to ask about a small machine whose step is comparisons
;; and choices (CLOSER_TIMED_MACHINE_WORK_ORDER.md, Slice A): orderings,
;; selection and several results here; overflow guards, named preconditions
;; and objectives in the sections below as they are added. These need real
;; MLIR tools and a real Z3; a missing tool is a failure, not a skip.
(define-runtime-path fixtures "semantics")
(define arithmetic (dynamic-require (build-path fixtures "valid.rhm") 'arithmetic))

(define chain (make_toolchain))
(define z3
  (or (getenv "PILLE_Z3")
      (find-executable-path "z3")
      (error 'smt-synthesis "these tests require Z3: put z3 on PATH or set PILLE_Z3")))

(define (program . functions)
  (parse_module (string-append "module {\n" (apply string-append functions) "}\n")
                (dialect_irdl arithmetic) chain))

(define (query module function inputs property [preconditions '()])
  (make_smt_query arithmetic module function inputs property preconditions))
(define (status value) (solver_result_status (query_check value z3)))
(define (rejects pattern thunk)
  (check-exn (lambda (error) (and (exn:fail? error) (regexp-match? pattern (exn-message error)))) thunk))

(define a8 (smt_input "a" 8))
(define b8 (smt_input "b" 8))
(define a32 (smt_input "a" 32))
(define b32 (smt_input "b" 32))
(define c1 (smt_input "c" 1))
(define one (smt_const 1 1))
(define zero (smt_const 0 1))
(define (bit formula) (smt_ite formula one zero))

;;==============================================================================
;; A1. Orderings

(define predicates '(eq ne slt sle sgt sge ult ule ugt uge))

;; What each predicate means, written without the lowering: on the unsigned
;; residues, or on the two's complement values they stand for.
(define (signed value width) (if (>= value (expt 2 (sub1 width))) (- value (expt 2 width)) value))
(define (holds? predicate lhs rhs width)
  (define-values (l r) (values (signed lhs width) (signed rhs width)))
  (case predicate
    [(eq) (= lhs rhs)] [(ne) (not (= lhs rhs))]
    [(ult) (< lhs rhs)] [(ule) (<= lhs rhs)] [(ugt) (> lhs rhs)] [(uge) (>= lhs rhs)]
    [(slt) (< l r)] [(sle) (<= l r)] [(sgt) (> l r)] [(sge) (>= l r)]))

(define comparisons
  (apply program
         (for/list ([predicate (in-list predicates)])
           (format "  func.func @cmp_~a(%a0: i8, %a1: i8) -> i1 {\n    %r = arith.cmpi ~a, %a0, %a1 : i8\n    return %r : i1\n  }\n"
                   predicate predicate))))

(test-case "the builders check sorts and widths, and say the signedness"
  (rejects #rx"width mismatch" (lambda () (smt_cmp 'ult a8 a32)))
  (rejects #rx"expected bitvector terms" (lambda () (smt_cmp 'slt a8 (smt_eq a8 b8))))
  (check-exn exn:fail? (lambda () (smt_cmp 'lt a8 b8)))
  (rejects #rx"expected a Boolean predicate" (lambda () (smt_ite a8 a8 b8)))
  (rejects #rx"width mismatch" (lambda () (smt_ite (smt_eq a8 b8) a8 a32)))
  (check-equal? (render_formula (smt_cmp 'ult a8 b8)) "a <u b")
  (check-equal? (render_formula (smt_cmp 'sge a8 b8)) "a >=s b")
  (check-equal? (render_term (smt_ite (smt_cmp 'slt a8 b8) a8 b8)) "(a <s b ? a : b)")
  (check-equal? (render_term (smt_result_at 1 32)) "result[1]"))

(test-case "arith.cmpi is the comparison of its predicate, on values chosen to tell them apart"
  ;; 0x80 is the least signed and a large unsigned value, so the signed and
  ;; unsigned orderings of each pair differ wherever they can.
  (define pairs '((0 0) (1 2) (2 1) (#x80 1) (1 #x80) (#xff #x80) (#x7f #x80) (#xff #xff)))
  (define specs
    (for*/list ([predicate (in-list predicates)] [pair (in-list pairs)])
      (define expected (if (holds? predicate (car pair) (cadr pair) 8) 1 0))
      (make_spec (format "cmp_~a" predicate) (list a8 b8)
                 (smt_eq (smt_result 1) (smt_const expected 1))
                 (list (smt_eq a8 (smt_const (car pair) 8)) (smt_eq b8 (smt_const (cadr pair) 8))))))
  (define answers (treelist->list (batch_check (make_smt_batch arithmetic comparisons specs) z3)))
  (check-equal? (map solver_result_status answers) (make-list (length specs) 'unsat))
  ;; and each ordering builder says what its cmpi does, for every input
  (for ([predicate (in-list (cddr predicates))])
    (check-eq? (status (query comparisons (format "cmp_~a" predicate) (list a8 b8)
                              (smt_eq (smt_result 1) (bit (smt_cmp predicate a8 b8)))))
               'unsat
               (format "~a" predicate)))
  ;; a comparison that is not the function's has a counterexample
  (check-eq? (status (query comparisons "cmp_ult" (list a8 b8)
                            (smt_eq (smt_result 1) (bit (smt_cmp 'slt a8 b8)))))
             'sat)
  ;; the lowering writes the SMT comparison, and no arith operation is left
  (define ir (module_ir (query_module (query comparisons "cmp_slt" (list a8 b8) (smt_eq (smt_result 1) one)))))
  (check-regexp-match #rx"smt.bv.cmp slt" ir)
  (check-false (regexp-match? #rx"arith\\." ir)))

;;==============================================================================
;; A2. Selection

(define choices
  (program
   "  func.func @choose(%a0: i1, %a1: i32, %a2: i32) -> i32 {\n    %r = arith.select %a0, %a1, %a2 : i32\n    return %r : i32\n  }\n"
   "  func.func @larger(%a0: i32, %a1: i32) -> i32 {\n    %c = arith.cmpi ugt, %a0, %a1 : i32\n    %r = arith.select %c, %a0, %a1 : i32\n    return %r : i32\n  }\n"
   ;; a step that stays or advances: phase 3 after `limit`, else unchanged
   "  func.func @step(%a0: i32, %a1: i32, %a2: i32) -> i32 {\n    %three = arith.constant 3 : i32\n    %due = arith.cmpi uge, %a1, %a2 : i32\n    %r = arith.select %due, %three, %a0 : i32\n    return %r : i32\n  }\n"
   "  func.func @vector(%a0: i1, %a1: i32, %a2: i32) -> i32 {\n    %r = arith.select %a0, %a1, %a2 : i32\n    %s = arith.addi %r, %r : i32\n    return %s : i32\n  }\n"))

(test-case "arith.select chooses by an i1 that is 1, and the ite builder says the same"
  (define r32 (smt_result 32))
  (check-eq? (status (query choices "choose" (list c1 a32 b32)
                            (smt_eq r32 (smt_ite (smt_eq c1 one) a32 b32))))
             'unsat)
  ;; the arms are not interchangeable
  (check-eq? (status (query choices "choose" (list c1 a32 b32)
                            (smt_eq r32 (smt_ite (smt_eq c1 one) b32 a32))))
             'sat)
  ;; a comparison feeding a select: the larger of two, unsigned
  (check-eq? (status (query choices "larger" (list a32 b32)
                            (smt_and (list (smt_cmp 'uge r32 a32) (smt_cmp 'uge r32 b32)
                                           (smt_or (list (smt_eq r32 a32) (smt_eq r32 b32)))))))
             'unsat)
  (check-eq? (status (query choices "larger" (list a32 b32) (smt_cmp 'sge r32 a32))) 'sat)
  ;; a step that stays in its phase or enters phase 3, under a precondition
  (define-values (phase clock limit) (values (smt_input "phase" 32) (smt_input "clock" 32) (smt_input "limit" 32)))
  (check-eq? (status (query choices "step" (list phase clock limit) (smt_eq r32 (smt_const 3 32))
                            (list (smt_cmp 'uge clock limit))))
             'unsat)
  (check-eq? (status (query choices "step" (list phase clock limit) (smt_eq r32 phase)
                            (list (smt_cmp 'ult clock limit))))
             'unsat)
  ;; what is still outside the fragment is still refused by name
  (rejects #rx"unsupported operation 'arith.addi'"
           (lambda () (query choices "vector" (list c1 a32 b32) (smt_eq r32 r32)))))

;;==============================================================================
;; A3. Several results

(define several
  (program
   "  func.func @both(%a0: i32, %a1: i32) -> (i32, i32, i1) {\n    %s = \"arithmetic.add\"(%a0, %a1) : (i32, i32) -> i32\n    %c = arith.cmpi ult, %a0, %a1 : i32\n    return %s, %a0, %c : i32, i32, i1\n  }\n"
   "  func.func @single(%a0: i32) -> i32 {\n    return %a0 : i32\n  }\n"))

(test-case "each of a function's results is named by its index"
  (define inputs (list a32 b32))
  (define value
    (query several "both" inputs
           (smt_and (list (smt_eq (smt_result_at 0 32) (smt_binary 'add a32 b32))
                          (smt_eq (smt_result_at 1 32) a32)
                          (smt_eq (smt_result_at 2 1) (bit (smt_cmp 'ult a32 b32)))))))
  (check-eq? (status value) 'unsat)
  (check-equal? (query_function value) "both")
  ;; a result may stand in a precondition, and results are not interchangeable
  (check-eq? (status (query several "both" inputs (smt_cmp 'ult a32 b32)
                            (list (smt_eq (smt_result_at 2 1) one))))
             'unsat)
  (check-eq? (status (query several "both" inputs (smt_eq (smt_result_at 0 32) (smt_result_at 1 32)))) 'sat)
  ;; `result` with no index is the result of a one-result function, and stays so
  (check-eq? (status (query several "single" (list a32) (smt_eq (smt_result 32) a32))) 'unsat)
  (check-eq? (status (query several "single" (list a32) (smt_eq (smt_result_at 0 32) a32))) 'unsat)
  (rejects #rx"function @both returns 3 values; the query refers to the result of a one-result function"
           (lambda () (query several "both" inputs (smt_eq (smt_result 32) a32))))
  (rejects #rx"refers to result 3, but function @both returns 3 value"
           (lambda () (query several "both" inputs (smt_eq (smt_result_at 3 32) a32))))
  (rejects #rx"refers to a 32-bit result 2, but function @both returns 'i1' there"
           (lambda () (query several "both" inputs (smt_eq (smt_result_at 2 32) a32))))
  (rejects #rx"result 0 is referenced with conflicting widths"
           (lambda () (query several "both" inputs
                             (smt_and (list (smt_eq (smt_result_at 0 32) a32)
                                            (smt_eq (smt_result_at 0 8) a8))))))
  ;; possible values are enumerated of one result
  (rejects #rx"function @both returns 3 values; possible values are enumerated of a one-result function"
           (lambda () (make_smt_values_query arithmetic several "both" inputs '()))))

;;==============================================================================
;; A4. Overflow guards

;; Whether lhs op rhs, on the numbers the residues stand for, stays in range.
(define (fits? operation signed? lhs rhs width)
  (define-values (l r) (if signed? (values (signed lhs width) (signed rhs width)) (values lhs rhs)))
  (define exact (case operation [(add) (+ l r)] [(sub) (- l r)] [(mul) (* l r)]))
  (if signed?
      (<= (- (expt 2 (sub1 width))) exact (sub1 (expt 2 (sub1 width))))
      (<= 0 exact (sub1 (expt 2 width)))))

(define sums
  (program
   "  func.func @sum(%a0: i32, %a1: i32) -> i32 {\n    %r = \"arithmetic.add\"(%a0, %a1) : (i32, i32) -> i32\n    return %r : i32\n  }\n"))

(test-case "a guard holds exactly where the operation, done on numbers, stays in range"
  (rejects #rx"width mismatch" (lambda () (smt_no_overflow 'add a8 a32 #f)))
  (check-equal? (render_formula (smt_no_overflow 'mul a8 b8 #t)) "no_overflow(a * b, signed)")
  ;; every pair of these, for each operation, unsigned and signed
  (define edges '(0 1 2 3 15 16 17 127 128 129 254 255))
  (define specs
    (for*/list ([operation '(add sub mul)] [signed? '(#f #t)] [lhs (in-list edges)] [rhs (in-list edges)])
      (define guard (smt_no_overflow operation a8 b8 signed?))
      (make_spec "cmp_eq" (list a8 b8)
                 (if (fits? operation signed? lhs rhs 8) guard (smt_not guard))
                 (list (smt_eq a8 (smt_const lhs 8)) (smt_eq b8 (smt_const rhs 8))))))
  (define answers (treelist->list (batch_check (make_smt_batch arithmetic comparisons specs) z3 10 '() 600)))
  (check-equal? (length specs) 864)
  (check-equal? (remove-duplicates (map solver_result_status answers)) '(unsat))
  ;; and for every input, the well-known tests: an unsigned sum did not wrap
  ;; exactly where it is no less than a term, a difference where a >= b
  (define (iff p q) (smt_or (list (smt_and (list p q)) (smt_and (list (smt_not p) (smt_not q))))))
  (check-eq? (status (query comparisons "cmp_eq" (list a8 b8)
                            (iff (smt_no_overflow 'add a8 b8 #f) (smt_cmp 'uge (smt_binary 'add a8 b8) a8))))
             'unsat)
  (check-eq? (status (query comparisons "cmp_eq" (list a8 b8)
                            (iff (smt_no_overflow 'sub a8 b8 #f) (smt_cmp 'uge a8 b8))))
             'unsat)
  ;; the widening is all in the formula: the terms keep their width
  (define ir (module_ir (query_module (query comparisons "cmp_eq" (list a8 b8) (smt_no_overflow 'mul a8 b8 #t)))))
  (check-regexp-match #rx"smt.bv.concat" ir)
  (check-regexp-match #rx"!smt.bv<16>" ir))

(test-case "a sum that holds only by wrapping is found without the guard and excluded with it"
  (define r32 (smt_result 32))
  ;; "the sum is no less than a": false where the addition wraps
  (define without (query_check (query sums "sum" (list a32 b32) (smt_cmp 'uge r32 a32)) z3))
  (check-eq? (solver_result_status without) 'sat)
  ;; the counterexample is a wrapping pair
  (define found (for/hash ([entry (in-list (solver_result_values without))]) (values (car entry) (caddr entry))))
  (check-true (>= (+ (hash-ref found "a") (hash-ref found "b")) (expt 2 32)))
  (check-eq? (status (query sums "sum" (list a32 b32) (smt_cmp 'uge r32 a32)
                            (list (smt_no_overflow 'add a32 b32 #f))))
             'unsat)
  ;; and the other way: asked for a wrapped sum, the guard leaves none
  (check-eq? (status (query sums "sum" (list a32 b32) (smt_not (smt_cmp 'ult r32 a32)))) 'sat)
  (check-eq? (status (query sums "sum" (list a32 b32) (smt_not (smt_cmp 'ult r32 a32))
                            (list (smt_no_overflow 'add a32 b32 #f))))
             'unsat))

;;==============================================================================
;; A5. Named preconditions and unsat cores

;; What `z3` prints for a script, run by hand: no option but the file.
(define (by-hand script)
  (define file (make-temporary-file "pille-smt-by-hand-~a.smt2"))
  (dynamic-wind
    void
    (lambda ()
      (display-to-file script file #:exists 'truncate)
      (string-trim (with-output-to-string (lambda () (system* z3 (path->string file))))))
    (lambda () (delete-file file))))

(define (core-of answer) (sort (treelist->list (solver_result_core answer)) string<?))

(test-case "a name is a nonempty string that can be written between bars, once a query"
  (define p (smt_cmp 'ult a32 (smt_const 10 32)))
  (rejects #rx"invalid precondition name" (lambda () (smt_named p "")))
  (rejects #rx"invalid precondition name" (lambda () (smt_named p "a|b")))
  (rejects #rx"invalid precondition name" (lambda () (smt_named p "a\\b")))
  (rejects #rx"invalid precondition name" (lambda () (smt_named p "two\nlines")))
  (rejects #rx"expected a Boolean predicate" (lambda () (smt_named a32 "x")))
  (rejects #rx"duplicate precondition name \"same\""
           (lambda () (query sums "sum" (list a32 b32) (smt_eq a32 a32)
                             (list (smt_named p "same") (smt_named (smt_eq b32 b32) "same"))))))

(test-case "named preconditions that cannot hold together are infeasible, and the core names which"
  (define r32 (smt_result 32))
  (define early (smt_named (smt_cmp 'ult a32 (smt_const 10 32)) "event-phases.md:22"))
  (define late (smt_named (smt_cmp 'ugt a32 (smt_const 20 32)) "event-phases.md:31"))
  (define aside (smt_named (smt_cmp 'ult b32 (smt_const 100 32)) "another page, line 4"))
  (define plain (smt_cmp 'uge a32 (smt_const 0 32)))
  (define value (query sums "sum" (list a32 b32) (smt_eq r32 r32) (list early aside plain late)))
  (define answer (query_check value z3))
  (check-eq? (solver_result_status answer) 'infeasible)
  ;; the two that conflict, and not the third that has nothing to do with it
  (check-equal? (core-of answer) '("event-phases.md:22" "event-phases.md:31"))
  ;; the names are in the query's text, and its assumptions say them
  (check-true (string-contains? (query_smtlib value) ":named |event-phases.md:22|"))
  (check-equal? (treelist->list (query_assumptions value))
                '("event-phases.md:22: a <u 0x0000000a:bv32" "another page, line 4: b <u 0x00000064:bv32"
                  "a >=u 0x00000000:bv32" "event-phases.md:31: a >u 0x00000014:bv32"))
  ;; run by hand, the feasibility question gives the same answer
  (check-equal? (by-hand (query_feasibility value)) "unsat\n(|event-phases.md:31| |event-phases.md:22|)")
  ;; a session and a batch answer as a single check does
  (define s (make_session z3))
  (check-equal? (core-of (query_session_check s value)) '("event-phases.md:22" "event-phases.md:31"))
  ;; and the session's solver is as it was: the next question has its model
  (define next (query_session_check s (query sums "sum" (list a32 b32) (smt_cmp 'uge r32 a32))))
  (check-eq? (solver_result_status next) 'sat)
  (check-equal? (map car (solver_result_values next)) '("a" "b"))
  (check-equal? (core-of (query_session_check s value)) '("event-phases.md:22" "event-phases.md:31"))
  (close_session s)
  (define batch
    (make_smt_batch arithmetic sums
                    (list (make_spec "sum" (list a32 b32) (smt_eq r32 r32) (list early aside plain late))
                          (make_spec "sum" (list a32 b32) (smt_cmp 'uge r32 a32))
                          (make_spec "sum" (list a32 b32) (smt_eq r32 r32) (list late early))
                          (make_spec "sum" (list a32 b32) (smt_cmp 'uge r32 a32)
                                     (list (smt_named (smt_no_overflow 'add a32 b32 #f) "no wrap"))))))
  (define answers (treelist->list (batch_check batch z3)))
  (check-equal? (map solver_result_status answers) '(infeasible sat infeasible unsat))
  (check-equal? (core-of (first answers)) '("event-phases.md:22" "event-phases.md:31")))

(test-case "named preconditions that can hold together change nothing but the text"
  (define r32 (smt_result 32))
  (define guard (smt_named (smt_no_overflow 'add a32 b32 #f) "no wrap"))
  (define proved (query sums "sum" (list a32 b32) (smt_cmp 'uge r32 a32) (list guard)))
  (check-eq? (status proved) 'unsat)
  (check-equal? (by-hand (query_smtlib proved)) "unsat")
  (define refuted (query sums "sum" (list a32 b32) (smt_eq r32 a32) (list guard)))
  (check-eq? (status refuted) 'sat)
  (check-equal? (by-hand (query_smtlib refuted)) "sat"))

(test-case "preconditions without a name are as before: inconsistent ones prove vacuously"
  (define r32 (smt_result 32))
  (define early (smt_cmp 'ult a32 (smt_const 10 32)))
  (define late (smt_cmp 'ugt a32 (smt_const 20 32)))
  (define value (query sums "sum" (list a32 b32) (smt_eq r32 a32) (list early late)))
  (check-false (query_feasibility value))
  (check-false (string-contains? (query_smtlib value) ":named"))
  (check-eq? (status value) 'unsat)
  ;; and where they alone conflict, a named one beside them is not blamed
  (define beside
    (query sums "sum" (list a32 b32) (smt_eq r32 a32)
           (list early late (smt_named (smt_cmp 'ult b32 (smt_const 5 32)) "unrelated"))))
  (define answer (query_check beside z3))
  (check-eq? (solver_result_status answer) 'infeasible)
  (check-equal? (core-of answer) '()))

;;==============================================================================
;; A6. Objectives

(define (objective module function inputs term direction signed? [preconditions '()])
  (make_smt_objective arithmetic module function inputs term direction signed? preconditions))
;; the optimum as the number asked for, or the answer's status
(define (optimum value)
  (define answer (objective_check value z3))
  (if (eq? (solver_result_status answer) 'optimum)
      (objective_value value (caddr (car (solver_result_values answer))))
      (solver_result_status answer)))

(test-case "the least and greatest value of a term, unsigned and signed"
  ;; a between -5 and 3 as signed numbers: as unsigned ones, 0..3 and 251..255
  (define within (list (smt_cmp 'sge a8 (smt_const -5 8)) (smt_cmp 'sle a8 (smt_const 3 8))))
  (define (of direction signed?) (optimum (objective comparisons "cmp_eq" (list a8 b8) a8 direction signed? within)))
  (check-equal? (of 'minimize #t) -5)
  (check-equal? (of 'maximize #t) 3)
  ;; the unsigned order is another order: its least and greatest are elsewhere
  (check-equal? (of 'minimize #f) 0)
  (check-equal? (of 'maximize #f) 255)
  ;; a term of the inputs, not only an input: the greatest a + b that does not wrap
  (check-equal? (optimum (objective comparisons "cmp_eq" (list a8 b8) (smt_binary 'add a8 b8) 'maximize #f
                                    (list (smt_no_overflow 'add a8 b8 #f) (smt_cmp 'ule a8 (smt_const 100 8)))))
                255)
  ;; a result of the function may be the objective: the least a <u b is 0
  (check-equal? (optimum (objective comparisons "cmp_ult" (list a8 b8) (smt_result 1) 'minimize #f)) 0)
  ;; the inputs reported reach the optimum
  (define value (objective comparisons "cmp_eq" (list a8 b8) a8 'minimize #t within))
  (define answer (objective_check value z3))
  (check-equal? (map car (solver_result_values answer)) '("pille_objective" "a" "b"))
  (check-equal? (caddr (cadr (solver_result_values answer))) #xfb)
  ;; the text is the question, with the objective written in; run by hand it answers
  (define script (objective_smtlib value))
  (check-true (string-contains? script "(minimize pille_objective)"))
  (check-regexp-match #rx"^sat\n[(][(]pille_objective #x7b[)]\n [(]a #xfb[)]" (by-hand script))
  ;; no input at all: infeasible, with a core where names say which
  (check-eq? (optimum (objective comparisons "cmp_eq" (list a8 b8) a8 'minimize #f
                                 (list (smt_cmp 'ult a8 (smt_const 0 8)))))
             'infeasible)
  (define conflict
    (objective comparisons "cmp_eq" (list a8 b8) a8 'minimize #f
               (list (smt_named (smt_cmp 'ult a8 (smt_const 3 8)) "low") (smt_named (smt_cmp 'ugt a8 (smt_const 9 8)) "high")
                     (smt_named (smt_cmp 'ult b8 (smt_const 9 8)) "aside"))))
  (define refused (objective_check conflict z3))
  (check-eq? (solver_result_status refused) 'infeasible)
  (check-equal? (core-of refused) '("high" "low"))
  ;; an input named as the symbol would be gets another symbol
  (define taken (smt_input "pille_objective" 8))
  (check-equal? (optimum (objective comparisons "cmp_eq" (list taken b8) taken 'maximize #f
                                    (list (smt_cmp 'ult taken (smt_const 7 8)))))
                6)
  (check-exn exn:fail? (lambda () (objective comparisons "cmp_eq" (list a8 b8) a8 'smallest #f))))

;;==============================================================================
;; Acceptance for Slice A: a small timed machine
;;
;; The fixture is the test's, not the library's: nothing above knows of phases.
;; A machine over (phase, level, since, clock), each an i32. Its durations are
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

(define-values (idle initial escalation re-escalation responded) (values 0 1 2 3 5))
(define-values (on off disconnect respond time nothing) (values 0 1 2 3 4 9))
(define messages 6)

;; The machine, written on numbers.
(define (machine-step state durations kind amount)
  (define-values (phase level since clock) (apply values state))
  (define-values (I E R) (apply values durations))
  (define start? (and (= kind on) (= phase idle)))
  (define clock* (if (= kind time) (wrap32 (+ clock amount)) clock))
  (define since* (if start? clock since))
  (define phase1
    (let* ([p (if start? initial phase)]
           [p (if (or (= kind off) (= kind disconnect)) idle p)])
      (if (and (= kind respond) (memv p (list initial escalation re-escalation))) responded p)))
  (cond
    [(memv phase1 (list initial escalation re-escalation))
     (define elapsed (wrap32 (- clock* since*)))
     (define-values (l0 l1 l2 l3)
       (values (wrap32 (+ I E)) (wrap32 (+ I E R)) (wrap32 (+ I E R R)) (wrap32 (+ I E R R R))))
     (list (cond [(< elapsed I) initial] [(< elapsed l0) escalation] [else re-escalation])
           (cond [(< elapsed l0) 0] [(< elapsed l1) 1] [(< elapsed l2) 2] [(< elapsed l3) 3] [else 4])
           since* clock*)]
    [else (list phase1 0 since* clock*)]))
(define (wrap32 value) (modulo value (expt 2 32)))
(define (machine-run durations kinds amounts)
  (for/fold ([state (list idle 0 0 0)]) ([kind (in-list kinds)] [amount (in-list amounts)])
    (machine-step state durations kind amount)))

;; The same machine as one function, its step written out once for each message.
(define machine-text
  (let ([out (open-output-string)])
    (define (line format-string . arguments) (fprintf out "    ~a\n" (apply format format-string arguments)))
    (define (constant name value) (line "%~a = arith.constant ~a : i32" name value))
    (define (op name operation lhs rhs) (line "%~a = \"arithmetic.~a\"(%~a, %~a) : (i32, i32) -> i32" name operation lhs rhs))
    (define (compare name predicate lhs rhs) (line "%~a = arith.cmpi ~a, %~a, %~a : i32" name predicate lhs rhs))
    (define (choose name test chosen otherwise type) (line "%~a = arith.select %~a, %~a, %~a : ~a" name test chosen otherwise type))
    (fprintf out "  func.func @machine(%I: i32, %E: i32, %R: i32~a) -> (i32, i32, i32, i32) {\n"
             (apply string-append (for/list ([k (in-range messages)]) (format ", %m~a: i32, %d~a: i32" k k))))
    (for ([value '(0 1 2 3 4 5)]) (constant (format "c~a" value) value))
    (line "%no = arith.constant false")
    (line "%yes = arith.constant true")
    (op "l0" "add" "I" "E")
    (op "l1" "add" "l0" "R")
    (op "l2" "add" "l1" "R")
    (op "l3" "add" "l2" "R")
    (define-values (phase level since clock)
      (for/fold ([phase "c0"] [level "c0"] [since "c0"] [clock "c0"]) ([k (in-range messages)])
        (define (n name) (format "~a_~a" name k))
        (define-values (m d) (values (format "m~a" k) (format "d~a" k)))
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
        (choose (n "p_dis") (n "is_dis") "c0" (n "p_off") "i32")
        ;; timed: the phase so far is initial, escalation or re-escalation
        (define (timed name of)
          (compare (format "~a_1" name) "eq" of "c1")
          (compare (format "~a_2" name) "eq" of "c2")
          (compare (format "~a_3" name) "eq" of "c3")
          (choose (format "~a_23" name) (format "~a_2" name) "yes" (format "~a_3" name) "i1")
          (choose name (format "~a_1" name) "yes" (format "~a_23" name) "i1"))
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
        (values (n "phase") (n "level") (n "since") (n "clock"))))
    (fprintf out "    return %~a, %~a, %~a, %~a : i32, i32, i32, i32\n  }\n" phase level since clock)
    (get-output-string out)))

(define machine (program machine-text))

(define-values (I E R) (values (smt_input "I" 32) (smt_input "E" 32) (smt_input "R" 32)))
(define kinds (for/list ([k (in-range messages)]) (smt_input (format "m~a" k) 32)))
(define amounts (for/list ([k (in-range messages)]) (smt_input (format "d~a" k) 32)))
(define machine-inputs (append (list I E R) (append* (map list kinds amounts))))
(define (is term value) (smt_eq term (smt_const value 32)))
(define-values (phase-after level-after) (values (smt_result_at 0 32) (smt_result_at 1 32)))

;; the messages said: each a kind and an amount, the rest nothing
(define (said . pairs)
  (define padded (append pairs (make-list (- messages (length pairs)) (list nothing 0))))
  (append* (for/list ([pair (in-list padded)] [kind (in-list kinds)] [amount (in-list amounts)])
             (list (is kind (car pair)) (is amount (cadr pair))))))

(test-case "the fixture's function is the machine written on numbers, on random message sequences"
  (define generator (make-pseudo-random-generator))
  (parameterize ([current-pseudo-random-generator generator])
    (random-seed 20261120)
    (define cases
      (for/list ([_ (in-range 60)])
        (define durations (list (random 1 20) (random 1 40) (random 1 30)))
        (define said-kinds (for/list ([_ (in-range messages)]) (list-ref (list on off disconnect respond time time time nothing) (random 8))))
        (define said-amounts (for/list ([_ (in-range messages)]) (random 0 60)))
        (list durations said-kinds said-amounts (machine-run durations said-kinds said-amounts))))
    ;; the sequences pass through every phase the machine has, and every level
    (define passed
      (append* (for/list ([c (in-list cases)])
                 (for/list ([count (in-range 1 (add1 messages))])
                   (machine-run (first c) (take (second c) count) (take (third c) count))))))
    (check-equal? (sort (remove-duplicates (map first passed)) <)
                  (list idle initial escalation re-escalation responded))
    (check-equal? (sort (remove-duplicates (map second passed)) <) '(0 1 2 3 4))
    (define specs
      (for/list ([c (in-list cases)])
        (define-values (durations said-kinds said-amounts expected) (apply values c))
        (make_spec "machine" machine-inputs
                   (smt_and (for/list ([value (in-list expected)] [index (in-naturals)])
                              (is (smt_result_at index 32) value)))
                   (append (list (is I (first durations)) (is E (second durations)) (is R (third durations)))
                           (apply said (map list said-kinds said-amounts))))))
    (define answers (treelist->list (batch_check (make_smt_batch arithmetic machine specs) z3 20 '() 600)))
    (check-equal? (remove-duplicates (map solver_result_status answers)) '(unsat))))

;; re-escalation 2 after `on` and 65 units of time, with initial 10 and escalation 30
(define expectation
  (append (list (is I 10) (is E 30))
          (said (list on 0) (list time 65))
          (list (is phase-after re-escalation) (is level-after 2))))
;; the sums the machine makes of its durations do not wrap
(define sums-fit
  (let* ([l0 (smt_binary 'add I E)] [l1 (smt_binary 'add l0 R)] [l2 (smt_binary 'add l1 R)])
    (list (smt_no_overflow 'add I E #f) (smt_no_overflow 'add l0 R #f) (smt_no_overflow 'add l1 R #f)
          (smt_no_overflow 'add l2 R #f))))

(test-case "acceptance: the durations a page's expectation admits"
  ;; escalation is entered at 10, re-escalation 1 at 40, re-escalation 2 at 40 + R and
  ;; re-escalation 3 at 40 + 2R, so 40 + R <= 65 < 40 + 2R: R is 13 to 25
  (define least (objective machine "machine" machine-inputs R 'minimize #f (append expectation sums-fit)))
  (define greatest (objective machine "machine" machine-inputs R 'maximize #f (append expectation sums-fit)))
  (check-equal? (optimum least) 13)
  (check-equal? (optimum greatest) 25)
  ;; and every R between is admitted, none outside: the expectation is exactly that range
  (check-eq? (status (query machine "machine" machine-inputs
                            (smt_and (list (smt_cmp 'uge R (smt_const 13 32)) (smt_cmp 'ule R (smt_const 25 32))))
                            (append expectation sums-fit)))
             'unsat)
  (check-eq? (status (query machine "machine" machine-inputs
                            (smt_and (list (is phase-after re-escalation) (is level-after 2)))
                            (append (list (is I 10) (is E 30) (smt_cmp 'uge R (smt_const 13 32))
                                          (smt_cmp 'ule R (smt_const 25 32)))
                                    (said (list on 0) (list time 65)))))
             'unsat)
  ;; run by hand, each objective's text gives its answer
  (check-regexp-match #rx"^sat\n[(][(]pille_objective #x0000000d[)]" (by-hand (objective_smtlib least)))
  (check-regexp-match #rx"^sat\n[(][(]pille_objective #x00000019[)]" (by-hand (objective_smtlib greatest))))

(test-case "acceptance: an answer that holds only by wrapping is found without the guards, excluded with them"
  ;; without the guards the greatest R is one whose sums wrap, far past 25
  (define unguarded (optimum (objective machine "machine" machine-inputs R 'maximize #f expectation)))
  (check-true (> unguarded 25))
  (check-true (>= (+ 40 (* 2 unguarded)) (expt 2 32)))
  (check-equal? (optimum (objective machine "machine" machine-inputs R 'maximize #f (append expectation sums-fit))) 25))

(test-case "acceptance: two named expectations that cannot both hold are infeasible, naming both"
  (define at-65 (said (list on 0) (list time 65)))
  (define line-22 (smt_named (smt_and (list (is phase-after re-escalation) (is level-after 2))) "event-phases.md:22"))
  (define line-31 (smt_named (is level-after 1) "event-phases.md:31"))
  (define settings (smt_named (smt_and (list (is I 10) (is E 30))) "settings.md:4"))
  (define preconditions (append at-65 sums-fit (list line-22 settings line-31)))
  (define value (query machine "machine" machine-inputs (is phase-after re-escalation) preconditions))
  (define answer (query_check value z3))
  (check-eq? (solver_result_status answer) 'infeasible)
  (check-equal? (core-of answer) '("event-phases.md:22" "event-phases.md:31"))
  (check-regexp-match #rx"^unsat\n[(][^()]*event-phases.md:(22|31)[^()]*event-phases.md:(22|31)[^()]*[)]$"
                      (by-hand (query_feasibility value)))
  ;; the same expectations asked of an objective
  (define asked (objective_check (objective machine "machine" machine-inputs R 'minimize #f preconditions) z3))
  (check-eq? (solver_result_status asked) 'infeasible)
  (check-equal? (core-of asked) '("event-phases.md:22" "event-phases.md:31"))
  ;; with the second expectation gone, the first is as before
  (check-equal? (optimum (objective machine "machine" machine-inputs R 'minimize #f
                                    (append at-65 sums-fit (list line-22 settings))))
                13))
