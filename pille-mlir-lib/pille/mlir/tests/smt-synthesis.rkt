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
