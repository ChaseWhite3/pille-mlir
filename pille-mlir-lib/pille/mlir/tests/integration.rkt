#lang racket/base

(require rackunit
         racket/file
         racket/path
         racket/runtime-path
         racket/string
         racket/system
         "../../private/mlir/tools.rkt")

;; These are integration tests: missing MLIR tools are a test failure. Set
;; PILLE_MLIR_PREFIX to the installation being tested, or put mlir-opt on PATH.
(define-runtime-path fixtures "fixtures")
(define (fixture name) (file->string (build-path fixtures name)))
(define definitions (fixture "rhombus.irdl.mlir"))
(define chain (make_toolchain))
(define add-source
  #<<MLIR
module {
  func.func @add(%lhs: i32, %rhs: i32) -> i32 {
    %sum = arith.addi %lhs, %rhs : i32
    return %sum : i32
  }
}
MLIR
  )
(define llvm-pipeline
  "builtin.module(convert-arith-to-llvm,convert-func-to-llvm,reconcile-unrealized-casts)")

(test-case "parse, print, and reparse verified MLIR"
  (define module (parse_module add-source "" chain))
  (check-true (is_module module))
  (check-equal? (module_ir (parse_module (module_ir module) "" chain))
                (module_ir module))
  (check-exn #rx"mlir-opt failed" (lambda () (parse_module "module { broken" "" chain)))
  (check-exn #rx"mlir-opt failed"
             (lambda () (parse_module "module { \"unknown.op\"() : () -> () }" "" chain))))

(test-case "IRDL registration is required and rejects undefined operations"
  (check-exn #rx"mlir-opt failed"
             (lambda () (parse_module (fixture "rhombus-add.mlir") "" chain)))
  (check-exn #rx"mlir-opt failed"
             (lambda ()
               (parse_module "module { \"rhombus.undefined\"() : () -> () }"
                             definitions chain)))
  (define module (parse_module (fixture "rhombus-add.mlir") definitions chain))
  (check-regexp-match #rx"rhombus.add" (module_ir module))
  (define optimized (run_passes module "builtin.module(canonicalize,cse)"))
  ;; A second invocation must register IRDL too, not only the first parse.
  (check-regexp-match #rx"rhombus.add"
                      (module_ir (run_passes optimized "builtin.module(canonicalize)"))))

(test-case "source locations survive parsing and passes"
  (define source
    "module { func.func @origin() { return loc(\"example.rhm\":8:3) } }")
  (define module (parse_module source "" chain))
  (check-regexp-match #rx"example.rhm\":8:3" (module_ir module))
  (check-regexp-match #rx"example.rhm\":8:3"
                      (module_ir (run_passes module "builtin.module(canonicalize)"))))

(test-case "pass file options resolve relative to the caller and outputs survive"
  (define directory (make-temporary-file "pille-mlir-pass-files-~a" 'directory))
  (dynamic-wind
    void
    (lambda ()
      (parameterize ([current-directory directory])
        (define module (parse_module add-source "" chain))
        (define snapshot
          (run_passes module "builtin.module(snapshot-op-locations{filename=snapshot.mlir})"))
        (check-true (file-exists? "snapshot.mlir"))
        (check-regexp-match #rx"func.func @add" (file->string "snapshot.mlir"))
        (check-regexp-match #rx"snapshot.mlir" (module_ir snapshot))
        ;; The output remains a usable module after the subprocess cleans up.
        (check-not-exn (lambda () (parse_module (file->string "snapshot.mlir") "" chain)))))
    (lambda () (delete-directory/files directory))))

(test-case "IRDL verifies operation, custom type, and custom attribute constraints"
  (define module (parse_module (fixture "rhombus-custom-data.mlir") definitions chain))
  (check-regexp-match #rx"!rhombus.word<i32>" (module_ir module))
  (check-regexp-match #rx"#rhombus.mode<\"checked\">" (module_ir module))
  (check-equal? (module_ir (run_passes module "builtin.module(canonicalize)"))
                (module_ir module))
  (for ([name '("rhombus-add-invalid.mlir"
                "rhombus-custom-type-invalid.mlir"
                "rhombus-custom-attribute-invalid.mlir")])
    (check-exn #rx"mlir-opt failed"
               (lambda () (parse_module (fixture name) definitions chain)) name)))

(test-case "passes return a new module and preserve the original on success and failure"
  (define module (parse_module add-source "" chain))
  (define original (module_ir module))
  (define lowered (run_passes module llvm-pipeline))
  (check-false (eq? module lowered))
  (check-regexp-match #rx"llvm.func" (module_ir lowered))
  (check-equal? (module_ir module) original)
  (check-exn #rx"mlir-opt failed"
             (lambda () (run_passes module "builtin.module(no-such-pille-pass)")))
  (check-equal? (module_ir module) original)
  ;; Translation does not invent a lowering pipeline for high-level dialects.
  (check-exn #rx"mlir-translate failed" (lambda () (to_llvm_ir module))))

(test-case "a module retains its selected installation after the environment changes"
  (define module (parse_module add-source "" chain))
  (define missing (make-temporary-file "pille-mlir-capture-~a" 'directory))
  (dynamic-wind
    void
    (lambda ()
      (parameterize ([current-environment-variables
                      (environment-variables-copy (current-environment-variables))])
        (environment-variables-set! (current-environment-variables) #"PILLE_MLIR_PREFIX"
                                    (path->bytes missing))
        (check-exn #rx"cannot find" make_toolchain)
        (check-regexp-match #rx"define i32 @add"
                            (to_llvm_ir (run_passes module llvm-pipeline)))))
    (lambda () (delete-directory/files missing))))

(test-case "lowered arithmetic translates into valid LLVM IR and bitcode"
  (define module (run_passes (parse_module add-source "" chain) llvm-pipeline))
  (check-regexp-match #rx"define i32 @add" (to_llvm_ir module))
  (define bitcode (to_bitcode module))
  (check-true (immutable? bitcode))
  (check-equal? (subbytes bitcode 0 4) #"BC\300\336")
  ;; Decode with the matching installation; a magic-header check alone cannot
  ;; detect invalid or truncated bitcode.
  ;; (the installation the toolchain chose, however it was found)
  (define executable (if (eq? (system-type) 'windows) "llvm-dis.exe" "llvm-dis"))
  (define disassembler (build-path (toolchain_bin chain) executable))
  (define directory (make-temporary-file "pille-mlir-test-~a" 'directory))
  (dynamic-wind
    void
    (lambda ()
      (define input (build-path directory "add.bc"))
      (define output (build-path directory "add.ll"))
      (display-to-file bitcode input #:mode 'binary)
      (check-true (system* disassembler input "-o" output))
      (check-regexp-match #rx"define i32 @add" (file->string output)))
    (lambda () (delete-directory/files directory))))

(test-case "SMT dialect exports a solver query"
  (define smt (to_smtlib (parse_module (fixture "smt.mlir") "" chain)))
  (check-true (string-contains? smt "(set-logic QF_UF)"))
  (check-true (string-contains? smt "(assert "))
  (check-true (string-contains? smt "(not "))
  (check-true (string-contains? smt "(check-sat)")))
