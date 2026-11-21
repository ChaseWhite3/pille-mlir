#lang racket/base

(require json
         (only-in "../../private/mlir/tools.rkt" make_toolchain toolchain_bin)
         rackunit
         racket/file
         racket/list
         racket/path
         racket/port
         racket/runtime-path
         racket/string
         racket/system
         racket/treelist
         "../../private/mlir/query.rkt"
         "../../private/mlir/schema.rkt"
         "../../private/mlir/solver.rkt"
         "../../private/mlir/temporary.rkt"
         "../../private/mlir/tools.rkt")

;; End-to-end tests of declaration-driven SMT verification. They require real
;; MLIR tools and a real Z3. A missing tool is a test failure, not a skip.
(define-runtime-path fixtures "semantics")
(define (dialect name) (dynamic-require (build-path fixtures "valid.rhm") name))

(define chain (make_toolchain))

;; Every question here is exported both ways, by the lowering itself and by
;; mlir-translate, and the two texts must be the same.
(smt_export_mode 'both)
(define z3
  (or (getenv "PILLE_Z3")
      (find-executable-path "z3")
      (error 'smt-integration "these tests require Z3: put z3 on PATH or set PILLE_Z3")))

(define arithmetic (dialect 'arithmetic))
(define second (dialect 'vectorless))
(define twin-add (dialect 'twin_add))
(define twin-sub (dialect 'twin_sub))

;; func.func @name(%a0: t0, ...) -> result { body...; return %r : result }
(define (function name types result . body)
  (format "  func.func @~a(~a) -> ~a {\n~a    return %r : ~a\n  }\n"
          name
          (string-join (for/list ([type (in-list types)] [index (in-naturals)])
                         (format "%a~a: ~a" index type))
                       ", ")
          result
          (apply string-append (for/list ([line (in-list body)]) (format "    ~a\n" line)))
          result))

(define (call target operation type . operands)
  (format "~a = \"~a\"(~a) : (~a) -> ~a" target operation (string-join operands ", ")
          (string-join (for/list ([_operand (in-list operands)]) type) ", ") type))

(define (program dialect . functions)
  (parse_module (string-append "module {\n" (apply string-append functions) "}\n")
                (dialect_irdl dialect) chain))

(define (query dialect module function inputs property [preconditions '()])
  (make_smt_query dialect module function inputs property preconditions))

(define (solve value . arguments) (apply query_check value z3 arguments))
(define (status value . arguments) (solver_result_status (apply solve value arguments)))
(define (smt-ir value) (module_ir (query_module value)))

(define (input name width) (smt_input name width))
(define (literal value width) (smt_const value width))
(define (same lhs rhs) (smt_eq lhs rhs))

;; An evaluator written independently of the lowering: exact integers reduced
;; modulo 2^width. It shares no code with the semantic model or the lowering.
(define (wrap value width) (modulo value (expt 2 width)))
(define (model-add lhs rhs width) (wrap (+ lhs rhs) width))
(define (model-sub lhs rhs width) (wrap (- lhs rhs) width))
(define (model-mul lhs rhs width) (wrap (* lhs rhs) width))

(define x32 (input "x" 32))
(define y32 (input "y" 32))
(define r32 (smt_result 32))

(define basics
  (program arithmetic
           (function "add_zero" '("i32") "i32"
                     "%zero = arith.constant 0 : i32"
                     (call "%r" "arithmetic.add" "i32" "%a0" "%zero"))
           (function "round_trip" '("i32" "i32") "i32"
                     (call "%sum" "arithmetic.add" "i32" "%a0" "%a1")
                     (call "%r" "arithmetic.sub" "i32" "%sum" "%a1"))
           (function "successor" '("i32") "i32"
                     "%one = arith.constant 1 : i32"
                     (call "%r" "arithmetic.add" "i32" "%a0" "%one"))
           (function "shared" '("i32" "i32") "i32"
                     (call "%sum" "arithmetic.add" "i32" "%a0" "%a1")
                     (call "%square" "arithmetic.mul" "i32" "%sum" "%sum")
                     (call "%r" "arithmetic.sub" "i32" "%square" "%sum"))
           (function "double" '("i32") "i32"
                     "%two = arith.constant 2 : i32"
                     (call "%r" "arithmetic.mul" "i32" "%a0" "%two"))
           (function "twice" '("i32") "i32"
                     (call "%r" "arithmetic.add" "i32" "%a0" "%a0"))))

(test-case "a query is a verified SMT module with no residual custom operations"
  (define value (query arithmetic basics "add_zero" (list x32) (same r32 x32)))
  (define ir (smt-ir value))
  (check-regexp-match #rx"smt.solver" ir)
  (check-regexp-match #rx"smt.set_logic \"QF_BV\"" ir)
  (check-regexp-match #rx"smt.declare_fun \"x\" : !smt.bv<32>" ir)
  (check-false (regexp-match? #rx"arithmetic\\.|func\\.func|arith\\." ir))
  ;; The stock tools accept it with no IRDL definitions and no plugin, and the
  ;; stored SMT-LIB is exactly what the existing exporter produces for it.
  (define reparsed (parse_module ir "" chain))
  (check-equal? (module_ir reparsed) ir)
  (check-equal? (to_smtlib (query_module value)) (query_smtlib value))
  (check-true (string-contains? (query_smtlib value) "(set-logic QF_BV)"))
  (check-true (string-contains? (query_smtlib value) "(declare-const x (_ BitVec 32))"))
  (check-true (string-contains? (query_smtlib value) "(check-sat)"))
  (check-equal? (query_function value) "add_zero")
  (check-equal? (query_dialect value) "arithmetic")
  (check-equal? (treelist->list (query_inputs value)) (list (treelist "x" 32)))
  ;; Building and exporting a query does not run a solver; checking it does.
  (check-eq? (status value) 'unsat))

(test-case "true properties of wrapping arithmetic are proved"
  ;; add(x, 0) == x
  (check-eq? (status (query arithmetic basics "add_zero" (list x32) (same r32 x32))) 'unsat)
  ;; sub(add(x, y), y) == x, through two composed custom operation instances.
  (define round-trip (query arithmetic basics "round_trip" (list x32 y32) (same r32 x32)))
  (check-eq? (status round-trip) 'unsat)
  (check-regexp-match #rx"%0 = smt.bv.add %x, %y" (smt-ir round-trip))
  (check-regexp-match #rx"%1 = smt.bv.neg %y" (smt-ir round-trip))
  (check-regexp-match #rx"%2 = smt.bv.add %0, %1" (smt-ir round-trip))
  ;; The same operation is not provably the identity on its second argument.
  (check-eq? (status (query arithmetic basics "round_trip" (list x32 y32) (same r32 y32))) 'sat)
  ;; mul(x, 2) == add(x, x), comparing a multiplication with a property term.
  (check-eq? (status (query arithmetic basics "double" (list x32)
                            (same r32 (smt_binary 'add x32 x32))))
             'unsat)
  (check-eq? (status (query arithmetic basics "twice" (list x32)
                            (same r32 (smt_binary 'mul x32 (literal 2 32)))))
             'unsat))

(test-case "a choice lowers to smt.ite and is decided by the solver"
  (define choice (dialect 'choice))
  (define toggles
    (program choice
             (function "once" '("i8") "i8"
                       (call "%r" "choice.toggle" "i8" "%a0"))
             (function "twice" '("i8") "i8"
                       (call "%t" "choice.toggle" "i8" "%a0")
                       (call "%r" "choice.toggle" "i8" "%t"))
             (function "thrice" '("i8") "i8"
                       (call "%t" "choice.toggle" "i8" "%a0")
                       (call "%u" "choice.toggle" "i8" "%t")
                       (call "%r" "choice.toggle" "i8" "%u"))))
  (define x8 (input "x" 8))
  (define r8 (smt_result 8))
  (define once (query choice toggles "once" (list x8) (same r8 (literal 1 8))
                      (list (same x8 (literal 0 8)))))
  (check-regexp-match #rx"smt.ite" (smt-ir once))
  ;; toggle(0) == 1, and toggle of anything else is 0.
  (check-eq? (status once) 'unsat)
  (check-eq? (status (query choice toggles "once" (list x8) (same r8 (literal 0 8))
                            (list (smt_not (same x8 (literal 0 8))))))
             'unsat)
  ;; Toggling twice is not the identity (5 goes to 0 and then to 1) ...
  (check-eq? (status (query choice toggles "twice" (list x8) (same r8 x8))) 'sat)
  ;; ... but three toggles are one.
  (check-eq? (status (query choice toggles "thrice" (list x8)
                            (same r8 (smt_binary 'sub (literal 1 8) (literal 1 8)))
                            (list (smt_not (same x8 (literal 0 8))))))
             'unsat))

(test-case "what an operation requires is proved of every use, not assumed"
  (define choice (dialect 'choice))
  (define uses
    (program choice
             (function "once" '("i8") "i8"
                       (call "%r" "choice.predecessor" "i8" "%a0"))
             (function "twice" '("i8") "i8"
                       (call "%t" "choice.predecessor" "i8" "%a0")
                       (call "%r" "choice.predecessor" "i8" "%t"))))
  (define x8 (input "x" 8))
  (define r8 (smt_result 8))
  (define trivially (same r8 r8))
  (define (given value) (list (same x8 (literal value 8))))
  ;; Nothing restricts x, so the requirement itself has a counterexample even
  ;; though the property asked about is trivially true.
  (check-eq? (status (query choice uses "once" (list x8) trivially)) 'sat)
  ;; Within the requirement the property is proved ...
  (check-eq? (status (query choice uses "once" (list x8) (same r8 (literal 1 8)) (given 2))) 'unsat)
  ;; ... and a false property still has a counterexample there.
  (check-eq? (status (query choice uses "once" (list x8) (same r8 (literal 2 8)) (given 2))) 'sat)
  ;; Each use has its own obligation: from 2 both hold (2, then 1); from 1 the
  ;; second use receives 0, which the model does not cover.
  (check-eq? (status (query choice uses "twice" (list x8) trivially (given 2))) 'unsat)
  (check-eq? (status (query choice uses "twice" (list x8) trivially (given 1))) 'sat))

(test-case "SSA values, repeated uses, and operand order are preserved"
  (define value (query arithmetic basics "shared" (list x32 y32)
                       (same r32 (smt_binary 'sub
                                             (smt_binary 'mul (smt_binary 'add x32 y32)
                                                         (smt_binary 'add x32 y32))
                                             (smt_binary 'add x32 y32)))))
  (define ir (smt-ir value))
  ;; One addition feeds both operands of the multiplication and the subtraction.
  (check-equal? (length (regexp-match* #rx"= smt.bv.add %x, %y" ir)) 4)
  (check-regexp-match #rx"%1 = smt.bv.mul %0, %0" ir)
  (check-regexp-match #rx"%2 = smt.bv.neg %0" ir)
  (check-regexp-match #rx"%3 = smt.bv.add %1, %2" ir)
  (check-eq? (status value) 'unsat)
  ;; Subtraction is not commutative, so swapped operands must be refuted.
  (define ordered
    (program arithmetic
             (function "difference" '("i32" "i32") "i32"
                       (call "%r" "arithmetic.sub" "i32" "%a0" "%a1"))))
  (check-eq? (status (query arithmetic ordered "difference" (list x32 y32)
                            (same r32 (smt_binary 'sub x32 y32))))
             'unsat)
  (check-eq? (status (query arithmetic ordered "difference" (list x32 y32)
                            (same r32 (smt_binary 'sub y32 x32))))
             'sat)
  ;; Inputs are bound by position, whatever they are called.
  (define swapped-names
    (query arithmetic ordered "difference" (list (input "first" 32) (input "second" 32))
           (same r32 (smt_binary 'sub (input "first" 32) (input "second" 32)))))
  (check-eq? (status swapped-names) 'unsat))

(test-case "a false property is refuted with a counterexample that replays"
  ;; add(x, 1) == x is false for every x.
  (define plain (solve (query arithmetic basics "successor" (list x32) (same r32 x32))))
  (check-eq? (solver_result_status plain) 'sat)
  (define assignment (car (solver_result_values plain)))
  (check-equal? (take assignment 2) '("x" 32))
  (define (violates? x) (not (= (model-add x 1 32) x)))
  (check-true (violates? (third assignment)))
  ;; With preconditions, the counterexample must satisfy them as well as
  ;; violate the property. Excluding the solver's first answer forces another.
  (define excluded (third assignment))
  (define preconditions
    (list (smt_not (same x32 (literal excluded 32)))
          (smt_not (same x32 (literal #xffffffff 32)))))
  (define constrained
    (solve (query arithmetic basics "successor" (list x32) (same r32 x32) preconditions)))
  (check-eq? (solver_result_status constrained) 'sat)
  (define x (third (car (solver_result_values constrained))))
  (check-true (and (not (= x excluded)) (not (= x #xffffffff))) "preconditions hold")
  (check-true (violates? x) "the property is violated")
  ;; Two inputs: round_trip returns x, so result == y fails exactly when x != y.
  (define both (solve (query arithmetic basics "round_trip" (list x32 y32) (same r32 y32))))
  (define assigned (for/hash ([entry (in-list (solver_result_values both))])
                     (values (car entry) (third entry))))
  (check-equal? (sort (hash-keys assigned) string<?) '("x" "y"))
  (define returned (model-sub (model-add (hash-ref assigned "x") (hash-ref assigned "y") 32)
                              (hash-ref assigned "y") 32))
  (check-false (= returned (hash-ref assigned "y"))))

(test-case "overflow wraps at the declared width instead of using mathematical integers"
  (define overflow
    (program arithmetic
             (function "max_plus_one" '() "i32"
                       "%max = arith.constant 4294967295 : i32"
                       "%one = arith.constant 1 : i32"
                       (call "%r" "arithmetic.add" "i32" "%max" "%one"))
             (function "square" '("i32") "i32"
                       (call "%r" "arithmetic.mul" "i32" "%a0" "%a0"))
             (function "wide_square" '("i64") "i64"
                       (call "%r" "arithmetic.mul" "i64" "%a0" "%a0"))
             (function "negative_one" '() "i32"
                       "%r = arith.constant -1 : i32")))
  ;; add(0xffffffff, 1) == 0 is proved, and == 0xffffffff is refuted.
  (check-eq? (status (query arithmetic overflow "max_plus_one" '() (same r32 (literal 0 32))))
             'unsat)
  (define refuted
    (solve (query arithmetic overflow "max_plus_one" '() (same r32 (literal #xffffffff 32)))))
  (check-eq? (solver_result_status refuted) 'sat)
  (check-equal? (solver_result_values refuted) '())
  ;; As integers 4294967296 would also differ from 0; as 32 bits it is 0.
  (check-eq? (status (query arithmetic overflow "max_plus_one" '()
                            (smt_not (same r32 (literal 0 32)))))
             'sat)
  ;; The same facts with a symbolic input pinned by a precondition.
  (check-eq? (status (query arithmetic basics "successor" (list x32) (same r32 (literal 0 32))
                            (list (same x32 (literal #xffffffff 32)))))
             'unsat)
  ;; Multiplication: 0x10000 * 0x10000 is 2^32, which is 0 in 32 bits and
  ;; 0x100000000 in 64 bits.
  (check-eq? (status (query arithmetic overflow "square" (list x32) (same r32 (literal 0 32))
                            (list (same x32 (literal #x10000 32)))))
             'unsat)
  (define x64 (input "x" 64))
  (define r64 (smt_result 64))
  (check-eq? (status (query arithmetic overflow "wide_square" (list x64)
                            (same r64 (literal #x100000000 64))
                            (list (same x64 (literal #x10000 64)))))
             'unsat)
  (check-eq? (status (query arithmetic overflow "wide_square" (list x64) (same r64 (literal 0 64))
                            (list (same x64 (literal #x100000000 64)))))
             'unsat)
  ;; Negative literals denote their two's complement residue, in MLIR
  ;; constants and in property literals alike.
  (check-eq? (status (query arithmetic overflow "negative_one" '()
                            (same r32 (literal #xffffffff 32))))
             'unsat)
  (check-eq? (status (query arithmetic overflow "negative_one" '() (same r32 (literal -1 32))))
             'unsat))

;; the installation the toolchain chose, however it was found
(define mlir-opt
  (build-path (toolchain_bin (make_toolchain)) (if (eq? (system-type) 'windows) "mlir-opt.exe" "mlir-opt")))

;; The generic form prints every operand and result type explicitly.
(define (generic-ir value)
  (define file (make-temporary-file "pille-smt-generic-~a.mlir"))
  (dynamic-wind
    void
    (lambda ()
      (display-to-file (smt-ir value) file #:exists 'truncate)
      (with-output-to-string
        (lambda () (check-true (system* mlir-opt "--mlir-print-op-generic" file)))))
    (lambda () (delete-file file))))

(test-case "every supported width maps to a bitvector of exactly that width"
  (for ([width '(1 8 16 32 64)])
    (define type (format "i~a" width))
    (define module
      (program arithmetic
               (function "f" (list type type) type
                         (call "%sum" "arithmetic.add" type "%a0" "%a1")
                         (call "%r" "arithmetic.sub" type "%sum" "%a1"))
               (function "next" (list type) type
                         (call "%r" "arithmetic.increment" type "%a0"))
               (function "ones" '() type
                         (call "%r" "arithmetic.minus_one" type))))
    (define x (input "x" width))
    (define y (input "y" width))
    (define result (smt_result width))
    (define value (query arithmetic module "f" (list x y) (same result x)))
    (check-true (string-contains? (smt-ir value) (format "!smt.bv<~a>" width)) type)
    (check-equal? (smtlib-declarations (query_smtlib value)) `(("x" . ,width) ("y" . ,width)))
    (check-eq? (status value) 'unsat type)
    ;; A width-relative literal is instantiated at the instance's width.
    (check-eq? (status (query arithmetic module "next" (list x)
                              (same result (smt_binary 'add x (literal 1 width)))))
               'unsat type)
    (check-eq? (status (query arithmetic module "ones" '()
                              (same result (literal (sub1 (expt 2 width)) width))))
               'unsat type)
    (when (= width 1)
      ;; i1 is a one-bit bitvector. Predicates over it are SMT Booleans, a
      ;; different sort that only equality produces.
      (define generic (generic-ir value))
      (check-regexp-match #rx"\"smt.declare_fun\"\\(\\).*-> !smt.bv<1>" generic)
      (check-regexp-match #rx"\"smt.bv.add\"\\(.*\\) : \\(!smt.bv<1>, !smt.bv<1>\\) -> !smt.bv<1>"
                          generic)
      (check-regexp-match #rx"\"smt.eq\"\\(.*\\) : \\(!smt.bv<1>, !smt.bv<1>\\) -> !smt.bool" generic)
      (check-regexp-match #rx"\"smt.not\"\\(.*\\) : \\(!smt.bool\\) -> !smt.bool" generic)
      (check-regexp-match #rx"\"smt.assert\"\\(.*\\) : \\(!smt.bool\\) -> \\(\\)" generic)
      (check-false (regexp-match? #rx"i1" generic))
      ;; MLIR's i1 constants lower to one-bit bitvectors, not to Booleans.
      (define bits
        (program arithmetic
                 (function "one_plus_one" '() "i1"
                           "%one = arith.constant true"
                           (call "%r" "arithmetic.add" "i1" "%one" "%one"))))
      (define closed (query arithmetic bits "one_plus_one" '() (same result (literal 0 1))))
      (check-regexp-match #rx"smt.bv.constant #smt.bv<-?1> : !smt.bv<1>" (smt-ir closed))
      (check-eq? (status closed) 'unsat)
      ;; In one bit, adding 1 twice is the identity and 1 + 1 wraps to 0.
      (check-eq? (status (query arithmetic module "next" (list x)
                                (smt_not (same result x))))
                 'unsat)))
  ;; The builder keeps the sorts apart as well.
  (define bit (input "bit" 1))
  (check-exn #rx"expected a Boolean predicate, received a 1-bit bitvector" (lambda () (smt_not bit)))
  (check-exn #rx"expected a Boolean predicate, received a 1-bit bitvector"
             (lambda () (smt_and (list (same bit bit) bit))))
  (check-exn #rx"expected bitvector terms, received a Boolean predicate"
             (lambda () (same (same bit bit) (same bit bit))))
  (check-exn #rx"expected bitvector terms, received a Boolean predicate"
             (lambda () (smt_binary 'add bit (same bit bit)))))

(test-case "one declaration is instantiated at each instance's width, and widths never mix"
  (define module
    (program arithmetic
             (function "narrow" '("i32" "i32") "i32"
                       (call "%r" "arithmetic.add" "i32" "%a0" "%a1"))
             (function "wide" '("i64" "i64") "i64"
                       (call "%r" "arithmetic.add" "i64" "%a0" "%a1"))
             (function "loose_same" '("i64" "i64") "i64"
                       (call "%r" "arithmetic.loose" "i64" "%a0" "%a1"))
             ;; IRDL accepts these: `loose` constrains each port independently.
             (function "loose_operands" '("i32" "i64") "i32"
                       "%r = \"arithmetic.loose\"(%a0, %a1) : (i32, i64) -> i32")
             (function "loose_result" '("i32" "i32") "i64"
                       "%r = \"arithmetic.loose\"(%a0, %a1) : (i32, i32) -> i64")
             (function "any_integer" '("i16" "i16") "i16"
                       (call "%r" "arithmetic.anything" "i16" "%a0" "%a1"))
             (function "any_float" '("f32" "f32") "i32"
                       "%f = \"arithmetic.anything\"(%a0, %a1) : (f32, f32) -> f32"
                       "%r = arith.constant 0 : i32")))
  (define x64 (input "x" 64))
  (define y64 (input "y" 64))
  (define r64 (smt_result 64))
  (define narrow (query arithmetic module "narrow" (list x32 y32)
                        (same r32 (smt_binary 'add x32 y32))))
  (define wide (query arithmetic module "wide" (list x64 y64)
                      (same r64 (smt_binary 'add x64 y64))))
  (check-equal? (smtlib-declarations (query_smtlib narrow)) '(("x" . 32) ("y" . 32)))
  (check-equal? (smtlib-declarations (query_smtlib wide)) '(("x" . 64) ("y" . 64)))
  (check-false (string-contains? (smt-ir narrow) "bv<64>"))
  (check-false (string-contains? (smt-ir wide) "bv<32>"))
  (check-eq? (status narrow) 'unsat)
  (check-eq? (status wide) 'unsat)
  ;; A 64-bit instance really is 64 bits wide: 2^32 + 2^32 is not 0.
  (check-eq? (status (query arithmetic module "wide" (list x64 y64) (same r64 (literal 0 64))
                            (list (same x64 (literal #x80000000 64))
                                  (same y64 (literal #x80000000 64)))))
             'sat)
  (check-eq? (status (query arithmetic module "loose_same" (list x64 y64)
                            (same r64 (smt_binary 'add x64 y64))))
             'unsat)
  ;; Mixed widths are rejected before any solver runs: never coerced, and
  ;; never treated as an assumption that the widths agree.
  (check-exn #rx"bv.add in the semantics of 'arithmetic.loose' combines a 32-bit value with a 64-bit value; widths must be equal and are never coerced or assumed equal"
             (lambda () (query arithmetic module "loose_operands" (list x32 y64) (same r32 x32))))
  (check-exn #rx"the semantics of 'arithmetic.loose' produce a 32-bit value for result 'out', whose type is 'i64'"
             (lambda () (query arithmetic module "loose_result" (list x32 y32) (same r64 r64))))
  ;; An unbounded constraint is decided per instance too.
  (define x16 (input "x" 16))
  (define y16 (input "y" 16))
  (check-eq? (status (query arithmetic module "any_integer" (list x16 y16)
                            (same (smt_result 16) (smt_binary 'add x16 y16))))
             'unsat)
  (check-exn #rx"unsupported type 'f32' of argument 0"
             (lambda () (query arithmetic module "any_float"
                               (list x32 y32) (same r32 r32)))))

(test-case "renamed operations, another namespace, and other models need no change to the lowering"
  (define module
    (program second
             (function "plus_zero" '("i32") "i32"
                       "%zero = arith.constant 0 : i32"
                       (call "%r" "second.plus" "i32" "%a0" "%zero"))
             (function "affine" '("i32" "i32") "i32"
                       (call "%r" "second.affine" "i32" "%a0" "%a1"))
             (function "mixed" '("i32" "i32") "i32"
                       (call "%sum" "second.plus" "i32" "%a0" "%a1")
                       (call "%r" "second.affine" "i32" "%sum" "%a0"))))
  (check-eq? (status (query second module "plus_zero" (list x32) (same r32 x32))) 'unsat)
  ;; affine(x, y) = 2x + y - 3
  (define expected
    (smt_binary 'sub (smt_binary 'add (smt_binary 'mul x32 (literal 2 32)) y32) (literal 3 32)))
  (define affine (query second module "affine" (list x32 y32) (same r32 expected)))
  (check-false (regexp-match? #rx"second\\." (smt-ir affine)))
  (check-eq? (status affine) 'unsat)
  (check-eq? (status (query second module "affine" (list x32 y32)
                            (same r32 (smt_binary 'add x32 y32))))
             'sat)
  ;; Different declared operations in one function: affine(plus(x, y), x).
  (check-eq? (status (query second module "mixed" (list x32 y32)
                            (same r32 (smt_binary
                                       'sub
                                       (smt_binary 'add
                                                   (smt_binary 'mul (smt_binary 'add x32 y32)
                                                               (literal 2 32))
                                                   x32)
                                       (literal 3 32)))))
             'unsat)
  ;; The first dialect's model is not consulted for the second's operations.
  (check-exn #rx"was not verified against dialect arithmetic's generated IRDL"
             (lambda () (query arithmetic module "plus_zero" (list x32) (same r32 x32)))))

(test-case "the dialect value selects the model; names and IRDL do not"
  ;; twin_add and twin_sub declare the same namespace, operation, and IRDL.
  (check-equal? (dialect_irdl twin-add) (dialect_irdl twin-sub))
  (define source
    (function "combine" '("i32" "i32") "i32"
              (call "%r" "twin.combine" "i32" "%a0" "%a1")))
  (define module (program twin-add source))
  (define sum (same r32 (smt_binary 'add x32 y32)))
  (define difference (same r32 (smt_binary 'sub x32 y32)))
  (check-eq? (status (query twin-add module "combine" (list x32 y32) sum)) 'unsat)
  (check-eq? (status (query twin-add module "combine" (list x32 y32) difference)) 'sat)
  ;; The very same module, under the other dialect value's declared meaning.
  (check-eq? (status (query twin-sub module "combine" (list x32 y32) sum)) 'sat)
  (check-eq? (status (query twin-sub module "combine" (list x32 y32) difference)) 'unsat)
  ;; Interleaving them shows that no model is remembered between queries.
  (check-eq? (status (query twin-add module "combine" (list x32 y32) sum)) 'unsat)
  (check-regexp-match #rx"smt.bv.neg" (smt-ir (query twin-sub module "combine" (list x32 y32) sum)))
  (check-false (regexp-match? #rx"smt.bv.neg"
                              (smt-ir (query twin-add module "combine" (list x32 y32) sum)))))

(test-case "lowered expressions agree with an independent evaluator"
  ;; For concrete inputs pinned by preconditions, the lowered program must
  ;; return exactly what the evaluator computes, and nothing else.
  (define operations
    (list (list "arithmetic.add" arithmetic model-add)
          (list "arithmetic.sub" arithmetic model-sub)
          (list "arithmetic.mul" arithmetic model-mul)
          (list "arithmetic.square_of_sum" arithmetic
                (lambda (lhs rhs width)
                  (model-mul (model-add lhs rhs width) (model-add lhs rhs width) width)))
          (list "second.affine" second
                (lambda (lhs rhs width)
                  (model-sub (model-add (model-mul lhs 2 width) rhs width) 3 width)))
          (list "second.offset" second
                (lambda (lhs _rhs width) (model-add lhs 5 width)))))
  (define (boundaries width)
    (define top (sub1 (expt 2 width)))
    (define sign (expt 2 (sub1 width)))
    (if (= width 1)
        '((0 0) (0 1) (1 0) (1 1)) ; exhaustive
        (list (list 0 0) (list 1 top) (list top top) (list sign sign) (list (sub1 sign) 1)
              (list 0 top) (list top 2) (list (quotient top 3) (quotient top 5)))))
  (for* ([entry (in-list operations)]
         [width '(1 8 64)]
         ;; These models' literals (2, 3, 5) have no one-bit form; see below.
         #:unless (and (= width 1) (member (car entry) '("second.affine" "second.offset"))))
    (define-values (operation owner evaluate) (apply values entry))
    (define type (format "i~a" width))
    (define module
      (program owner (function "f" (list type type) type (call "%r" operation type "%a0" "%a1"))))
    (define x (input "x" width))
    (define y (input "y" width))
    (define result (smt_result width))
    (for ([pair (in-list (boundaries width))])
      (define-values (lhs rhs) (apply values pair))
      (define expected (evaluate lhs rhs width))
      (define pinned (list (same x (literal lhs width)) (same y (literal rhs width))))
      (define label (format "~a at ~a on ~a" operation type pair))
      (check-eq? (status (query owner module "f" (list x y) (same result (literal expected width))
                                pinned))
                 'unsat label)
      ;; Any other value must be refuted, at exactly the pinned inputs.
      (define other (wrap (add1 expected) width))
      (define refuted
        (solve (query owner module "f" (list x y) (same result (literal other width)) pinned)))
      (check-eq? (solver_result_status refuted) 'sat label)
      (check-equal? (solver_result_values refuted) `(("x" ,width ,lhs) ("y" ,width ,rhs)) label)))
  ;; An instance whose width cannot hold a model's literal is rejected while
  ;; lowering, before any solver runs: the literal is never truncated.
  (check-exn #rx"literal 2 in the semantics of 'second.affine' does not fit in 1 bits"
             (lambda ()
               (query second
                      (program second
                               (function "f" '("i1" "i1") "i1"
                                         (call "%r" "second.affine" "i1" "%a0" "%a1")))
                      "f" (list (input "x" 1) (input "y" 1))
                      (same (smt_result 1) (smt_result 1)))))
  ;; The same check through MLIR constants instead of pinned inputs.
  (for ([pair '((4294967295 1) (65536 65536) (2147483648 2147483648) (7 9))])
    (define-values (lhs rhs) (apply values pair))
    (for ([entry (in-list (take operations 3))])
      (define-values (operation owner evaluate) (apply values entry))
      (define module
        (program owner
                 (function "f" '() "i32"
                           (format "%lhs = arith.constant ~a : i32" lhs)
                           (format "%rhs = arith.constant ~a : i32" rhs)
                           (call "%r" operation "i32" "%lhs" "%rhs"))))
      (check-eq? (status (query owner module "f" '()
                                (same r32 (literal (evaluate lhs rhs 32) 32))))
                 'unsat (format "~a on constants ~a" operation pair)))))

(define (rejects pattern dialect module function inputs property [preconditions '()])
  (check-exn (lambda (error)
               (and (exn:fail? error) (regexp-match? pattern (exn-message error))))
             (lambda () (query dialect module function inputs property preconditions))
             (format "~a" pattern)))

(test-case "operations and programs outside the fragment fail explicitly"
  (define trivial (same r32 r32))
  (define module
    (program arithmetic
             (function "opaque" '("i32") "i32" (call "%r" "arithmetic.opaque" "i32" "%a0"))
             (function "standard" '("i32") "i32" "%r = arith.addi %a0, %a0 : i32")
             (function "attributed" '("i32") "i32"
                       "%r = \"arithmetic.add\"(%a0, %a0) {rounding = \"up\"} : (i32, i32) -> i32")
             (function "effect" '("i32") "i32"
                       "%slot = memref.alloca() : memref<i32>"
                       "memref.store %a0, %slot[] : memref<i32>"
                       "%r = memref.load %slot[] : memref<i32>")
             (function "caller" '("i32") "i32" "%r = func.call @opaque(%a0) : (i32) -> i32")
             (function "dead_float" '("i32") "i32"
                       "%unused = arith.constant 1.0 : f32"
                       (call "%r" "arithmetic.add" "i32" "%a0" "%a0"))
             (function "odd_width" '("i7") "i32" "%r = arith.constant 0 : i32")
             (function "index_result" '("i32") "index" "%r = arith.constant 0 : index")
             (function "float_result" '("i32") "f32" "%r = arith.constant 0.0 : f32")
             "  func.func @branch(%a0: i32) -> i32 {\n    cf.br ^next\n  ^next:\n    return %a0 : i32\n  }\n"
             "  func.func @pair(%a0: i32) -> (i32, i32) {\n    return %a0, %a0 : i32, i32\n  }\n"
             "  func.func private @declared(i32) -> i32\n"
             "  func.func @annotated(%a0: i32) -> i32 attributes {pille.note = \"x\"} {\n    return %a0 : i32\n  }\n"
             "  func.func private @hidden(%a0: i32) -> i32 {\n    return %a0 : i32\n  }\n"))
  (define inputs (list x32))
  ;; A schema-only declaration verifies structurally but has no model.
  (rejects #rx"operation 'arithmetic.opaque' has no declared SMT semantics" arithmetic module "opaque" inputs trivial)
  ;; Operations are never interpreted by their names, standard or not.
  (rejects #rx"unsupported operation 'arith.addi'" arithmetic module "standard" inputs trivial)
  (rejects #rx"operation 'arithmetic.add' carries attribute 'rounding'; attribute-dependent semantics are unsupported and attributes are rejected rather than ignored"
           arithmetic module "attributed" inputs trivial)
  (rejects #rx"unsupported operation 'memref.alloca'" arithmetic module "effect" inputs trivial)
  ;; A call is inlined (smt-bounded.rkt), so this is refused for what its callee does.
  (rejects #rx"operation 'arithmetic.opaque' has no declared SMT semantics" arithmetic module "caller" inputs trivial)
  ;; Even an unused value outside the fragment is rejected, not dropped.
  (rejects #rx"unsupported constant of type 'f32'" arithmetic module "dead_float" inputs trivial)
  (rejects #rx"unsupported type 'i7' of argument 0" arithmetic module "odd_width" inputs trivial)
  (rejects #rx"unsupported result type 'index'" arithmetic module "index_result" inputs trivial)
  (rejects #rx"unsupported result type 'f32'" arithmetic module "float_result" inputs trivial)
  (rejects #rx"unsupported control flow: function @branch has 2 blocks" arithmetic module "branch" inputs trivial)
  ;; `result` with no index is the result of a one-result function; a function with
  ;; several is read by index (smt-synthesis.rkt).
  (rejects #rx"function @pair returns 2 values; the query refers to the result of a one-result function"
           arithmetic module "pair" inputs trivial)
  (rejects #rx"function @declared is a declaration without a body" arithmetic module "declared" inputs trivial)
  (rejects #rx"unsupported attribute 'pille.note' on function @annotated" arithmetic module "annotated" inputs trivial)
  (rejects #rx"function @missing was not found" arithmetic module "missing" inputs trivial)
  ;; Visibility does not affect the computed value and is accepted.
  (check-eq? (status (query arithmetic module "hidden" inputs (same r32 x32))) 'unsat)
  ;; Every failure above happened while lowering: no solver ran. A failing
  ;; lowering must not depend on the solver either.
  (check-exn #rx"has no declared SMT semantics"
             (lambda ()
               (parameterize ([current-environment-variables
                               (environment-variables-copy (current-environment-variables))])
                 (putenv "PILLE_Z3" "/pille-test/no-solver-installed")
                 (query arithmetic module "opaque" inputs trivial)))))

(test-case "inputs and the result are checked against the selected function"
  (define x64 (input "x" 64))
  (rejects #rx"function @round_trip has 2 arguments, but 1 inputs were declared"
           arithmetic basics "round_trip" (list x32) (same r32 x32))
  (rejects #rx"function @successor has 1 arguments, but 2 inputs were declared"
           arithmetic basics "successor" (list x32 y32) (same r32 x32))
  (rejects #rx"input 'x' is declared with width 64, but argument 0 of function @successor has type 'i32'"
           arithmetic basics "successor" (list x64) (same (smt_result 32) (smt_result 32)))
  (rejects #rx"the property refers to a 64-bit result, but function @successor returns 'i32'"
           arithmetic basics "successor" (list x32) (same (smt_result 64) (smt_result 64)))
  ;; Identities are checked before any tool runs.
  (rejects #rx"the property refers to input z, which is not among the declared inputs"
           arithmetic basics "successor" (list x32) (same r32 (input "z" 32)))
  (rejects #rx"input x is declared with width 32 but referenced with width 64"
           arithmetic basics "successor" (list x32) (same x64 x64))
  (rejects #rx"duplicate input name x" arithmetic basics "round_trip" (list x32 x32) (same r32 x32))
  (rejects #rx"the result is referenced with conflicting widths: 32, 64"
           arithmetic basics "successor" (list x32)
           (smt_and (list (same r32 r32) (same (smt_result 64) (smt_result 64)))))
  (check-exn #rx"width mismatch: a 32-bit bitvector and a 64-bit bitvector"
             (lambda () (same x32 x64)))
  (check-exn #rx"width mismatch" (lambda () (smt_binary 'add x32 x64)))
  (check-exn #rx"unsupported bitvector width 12" (lambda () (input "x" 12)))
  (check-exn #rx"literal 256 does not fit in 8 bits" (lambda () (literal 256 8)))
  (check-exn #rx"literal -129 does not fit in 8 bits" (lambda () (literal -129 8)))
  (check-equal? (literal -1 8) (literal 255 8))
  ;; Names are printed into SMT-LIB verbatim, so only safe identifiers pass.
  (for ([name '("a b" "1x" "" "x-y" "|x|" "x)")])
    (check-exn #rx"invalid input name" (lambda () (input name 32)) name))
  (for ([name '("and" "true" "let" "bvadd" "bv7" "concat" "assert" "_")])
    (check-exn #rx"reserved by SMT-LIB" (lambda () (input name 32)) name))
  ;; Names resembling the exporter's own temporaries are kept as written.
  (define tmp (input "tmp" 32))
  (define tmp0 (input "tmp_0" 32))
  (define value (query arithmetic basics "round_trip" (list tmp tmp0) (same r32 tmp)))
  (check-equal? (smtlib-declarations (query_smtlib value)) '(("tmp" . 32) ("tmp_0" . 32)))
  (check-eq? (status value) 'unsat)
  (define refuted (solve (query arithmetic basics "round_trip" (list tmp tmp0) (same r32 tmp0))))
  (check-equal? (map car (solver_result_values refuted)) '("tmp" "tmp_0")))

(test-case "descriptors incompatible with the program are rejected by the lowering"
  ;; The public API derives the manifest from the dialect whose IRDL verified
  ;; the module. These manifests bypass it to show the lowering checks for itself.
  (define (manifest . overrides)
    (jsexpr->string
     (for/fold ([base (hasheq 'format "pille-smt-query" 'version 1 'function "round_trip"
                              'inputs (list (hasheq 'name "x" 'width 32) (hasheq 'name "y" 'width 32))
                              'result_width 32
                              'operations
                              (hasheq 'arithmetic.add
                                      (hasheq 'operands '("lhs" "rhs") 'result "out" 'locals '()
                                              'value '("add" ("operand" 0) ("operand" 1)))
                                      'arithmetic.sub
                                      (hasheq 'operands '("lhs" "rhs") 'result "out" 'locals '()
                                              'value '("sub" ("operand" 0) ("operand" 1))))
                              'unmodeled '()
                              'preconditions '()
                              'property '("eq" ("result") ("input" 0)))])
               ([override (in-list overrides)])
       (hash-set base (car override) (cdr override)))))
  (define (lower text) (smt_lower_text basics text))
  (check-regexp-match #rx"smt.solver" (lower (manifest)))
  (define (operations add)
    (cons 'operations
          (hasheq 'arithmetic.add add
                  'arithmetic.sub (hasheq 'operands '("lhs" "rhs") 'result "out" 'locals '()
                                          'value '("sub" ("operand" 0) ("operand" 1))))))
  (check-exn #rx"operation 'arithmetic.add' has 2 operands and 1 results, which is incompatible with its declared semantics \\(3 operands, 1 result\\)"
             (lambda ()
               (lower (manifest (operations (hasheq 'operands '("a" "b" "c") 'result "out" 'locals '()
                                                    'value '("operand" 2)))))))
  (check-exn #rx"reference out of range in the semantics of 'arithmetic.add'"
             (lambda ()
               (lower (manifest (operations (hasheq 'operands '("lhs" "rhs") 'result "out" 'locals '()
                                                    'value '("operand" 5)))))))
  (check-exn #rx"unsupported expression 'shl' in the semantics of 'arithmetic.add'"
             (lambda ()
               (lower (manifest (operations (hasheq 'operands '("lhs" "rhs") 'result "out" 'locals '()
                                                    'value '("shl" ("operand" 0) ("operand" 1))))))))
  (check-exn #rx"literal 300 in the semantics of 'arithmetic.add' does not fit in 8 bits"
             (lambda ()
               (lower (manifest (operations (hasheq 'operands '("lhs" "rhs") 'result "out" 'locals '()
                                                    'value '("const" "300" ("width" 8))))))))
  (check-exn #rx"the semantics of 'arithmetic.add' produce a 8-bit value for result 'out', whose type is 'i32'"
             (lambda ()
               (lower (manifest (operations (hasheq 'operands '("lhs" "rhs") 'result "out" 'locals '()
                                                    'value '("const" "3" ("width" 8))))))))
  (check-exn #rx"malformed SMT query manifest: expected format \"pille-smt-query\" version 1"
             (lambda () (lower (manifest (cons 'version 999)))))
  (check-exn #rx"malformed SMT query manifest: missing a required field"
             (lambda () (lower "{\"format\":\"pille-smt-query\",\"version\":1}")))
  (check-exn #rx"malformed SMT query manifest" (lambda () (lower "[]")))
  (check-exn #rx"malformed SMT query manifest" (lambda () (lower "{not json")))
  (check-exn #rx"unsupported predicate 'implies' in the property"
             (lambda () (lower (manifest (cons 'property '("implies" ("eq" ("result") ("result"))))))))
  ;; A property may not reach into an operation's scope, nor the reverse.
  (check-exn #rx"unsupported expression 'operand' in the property"
             (lambda () (lower (manifest (cons 'property '("eq" ("operand" 0) ("result")))))))
  (check-exn #rx"unsupported expression 'input' in the semantics of 'arithmetic.add'"
             (lambda ()
               (lower (manifest (operations (hasheq 'operands '("lhs" "rhs") 'result "out" 'locals '()
                                                    'value '("input" 0))))))))

(test-case "preconditions make a proof conditional, and inconsistent ones make it vacuous"
  (define false-property (same r32 x32)) ; add(x, 1) == x
  (define zero (same x32 (literal 0 32)))
  (define one (same x32 (literal 1 32)))
  ;; Without assumptions the property is refuted.
  (define unconditional (query arithmetic basics "successor" (list x32) false-property))
  (check-equal? (treelist->list (query_assumptions unconditional)) '())
  (check-eq? (status unconditional) 'sat)
  ;; A consistent assumption does not rescue it, and the model satisfies it.
  (define assumed (solve (query arithmetic basics "successor" (list x32) false-property (list zero))))
  (check-eq? (solver_result_status assumed) 'sat)
  (check-equal? (solver_result_values assumed) '(("x" 32 0)))
  ;; x == 0 and x == 1 cannot both hold. The implication is then vacuously
  ;; true: the solver answers unsat although the property itself is false.
  (define vacuous (query arithmetic basics "successor" (list x32) false-property (list zero one)))
  (check-eq? (status vacuous) 'unsat)
  ;; The result is only meaningful with its assumptions, which stay attached.
  (check-equal? (treelist->list (query_assumptions vacuous))
                '("x == 0x00000000:bv32" "x == 0x00000001:bv32"))
  (check-true (string-contains? (query_smtlib vacuous) "#x00000000"))
  (check-true (string-contains? (query_smtlib vacuous) "#x00000001"))
  (check-equal? (length (regexp-match* #rx"smt.assert" (smt-ir vacuous))) 3)
  ;; Vacuity is detectable: an always-false property has a counterexample
  ;; exactly when the assumptions themselves are satisfiable.
  (define never (smt_not (same r32 r32)))
  (check-eq? (status (query arithmetic basics "successor" (list x32) never (list zero))) 'sat)
  (check-eq? (status (query arithmetic basics "successor" (list x32) never (list zero one)))
             'unsat)
  ;; A genuinely conditional proof: add(x, 1) == 1 only when x == 0.
  (define conditional
    (query arithmetic basics "successor" (list x32) (same r32 (literal 1 32)) (list zero)))
  (check-eq? (status conditional) 'unsat)
  (check-eq? (status (query arithmetic basics "successor" (list x32) (same r32 (literal 1 32))))
             'sat)
  ;; Connectives: !(a) || b, and conjunctions of assumptions.
  (check-eq? (status (query arithmetic basics "successor" (list x32)
                            (smt_or (list (smt_not zero) (same r32 (literal 1 32))))))
             'unsat)
  (check-eq? (status (query arithmetic basics "successor" (list x32)
                            (smt_and (list (smt_not (same r32 x32))
                                           (smt_or (list (smt_not zero) (same r32 (literal 1 32))))))))
             'unsat)
  (check-equal? (render_formula (smt_or (list (smt_not zero) (same r32 (literal 1 32)))))
                "(!(x == 0x00000000:bv32) || result == 0x00000001:bv32)"))

;; (x^3 + y) * (y^3 + x): cheap to state, expensive to invert.
(define hard
  (program arithmetic
           (function "hard" '("i64" "i64" "i64") "i64"
                     (call "%xx" "arithmetic.mul" "i64" "%a0" "%a0")
                     (call "%xxx" "arithmetic.mul" "i64" "%xx" "%a0")
                     (call "%left" "arithmetic.add" "i64" "%xxx" "%a1")
                     (call "%yy" "arithmetic.mul" "i64" "%a1" "%a1")
                     (call "%yyy" "arithmetic.mul" "i64" "%yy" "%a1")
                     (call "%right" "arithmetic.add" "i64" "%yyy" "%a0")
                     (call "%r" "arithmetic.mul" "i64" "%left" "%right"))))

(define hard-query
  (let ([x (input "x" 64)] [y (input "y" 64)] [z (input "z" 64)])
    (query arithmetic hard "hard" (list x y z)
           (smt_not (same (smt_result 64) (literal #x123456789abcdef1 64)))
           (list (same (smt_binary 'add (smt_binary 'mul x x) (smt_binary 'mul y z))
                       (literal #x0fedcba987654321 64))
                 (same (smt_binary 'mul z (smt_binary 'mul z x))
                       (literal #x1111111111111111 64))))))

(test-case "a real solver reports unknown and timeout distinctly from sat and unsat"
  ;; A resource limit makes Z3 itself give up: that is `unknown`.
  (define limited (solve hard-query 30 '("rlimit=1000")))
  (check-eq? (solver_result_status limited) 'unknown)
  (check-equal? (solver_result_values limited) '())
  ;; A wall-clock bound that Z3 cannot meet is a timeout, enforced here by
  ;; terminating the process rather than by trusting the solver.
  (define started (current-inexact-milliseconds))
  (define late (solve hard-query 0.05))
  (check-eq? (solver_result_status late) 'timeout)
  (check-regexp-match #rx"was terminated" (solver_result_diagnostics late))
  (check-true (< (- (current-inexact-milliseconds) started) 5000))
  ;; Neither is a proof, and neither carries a counterexample.
  (check-equal? (solver_result_values late) '())
  ;; Real failures: a missing solver, and a solver that rejects its arguments.
  (define value (query arithmetic basics "add_zero" (list x32) (same r32 x32)))
  (check-eq? (solver_result_status (query_check value "/pille-test/no-such-z3")) 'missing-executable)
  (define rejected (solve value 10 '("-pille-no-such-option")))
  (check-not-false (memq (solver_result_status rejected) '(nonzero-exit malformed-response)))
  (check-true (non-empty-string? (solver_result_diagnostics rejected))))

(test-case "the whole pipeline works from paths containing spaces and leaves nothing behind"
  (define root (make-temporary-file "pille smt spaces ~a" 'directory))
  (dynamic-wind
    void
    (lambda ()
      (define work (build-path root "temporary files"))
      (make-directory work)
      ;; A solver reached through a path with spaces. The wrapper only forwards.
      (define wrapper (build-path root "my z3"))
      (display-lines-to-file (list "#!/bin/sh" (format "exec '~a' \"$@\"" z3)) wrapper)
      (file-or-directory-permissions wrapper #o755)
      (parameterize ([current-temporary-base work])
        (define module
          (program arithmetic
                   (function "successor" '("i32") "i32"
                             "%one = arith.constant 1 : i32"
                             (call "%r" "arithmetic.add" "i32" "%a0" "%one"))))
        (define proved
          (query arithmetic module "successor" (list x32)
                 (same r32 (smt_binary 'add x32 (literal 1 32)))))
        (check-eq? (solver_result_status (query_check proved wrapper)) 'unsat)
        (define refuted
          (query_check (query arithmetic module "successor" (list x32) (same r32 x32)) wrapper))
        (check-eq? (solver_result_status refuted) 'sat)
        (check-equal? (map car (solver_result_values refuted)) '("x"))
        (check-equal? (car (solver_result_command refuted)) (path->string wrapper))
        ;; Failures clean up as well.
        (check-exn #rx"was not found"
                   (lambda () (query arithmetic module "missing" (list x32) (same r32 x32)))))
      (check-equal? (directory-list work) '()))
    (lambda () (delete-directory/files root #:must-exist? #f))))
