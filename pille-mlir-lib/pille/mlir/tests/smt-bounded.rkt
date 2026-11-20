#lang racket/base

(require rackunit
         racket/list
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
