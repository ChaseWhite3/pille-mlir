#lang racket/base

(require racket/file
         racket/format
         racket/list
         racket/string
         racket/treelist
         "../../private/mlir/tools.rkt")

(provide milliseconds measure row basic_source closer_source affine_source
         affine_values plugin)

(define (milliseconds) (current-inexact-monotonic-milliseconds))

(define (measure thunk)
  (define started (milliseconds))
  (define value (thunk))
  (treelist (- (milliseconds) started) value))

(define (number value) (~r value #:precision '(= 3)))
(define (row name n total)
  (printf "~a\t~a\t~a\t~a\n" name n (number total) (number (/ total n)))
  (flush-output))

(define basic_source #<<MLIR
module {
  func.func @identity(%x: i8) -> i8 {
    return %x : i8
  }
  func.func @successor(%x: i8) -> i8 {
    %one = arith.constant 1 : i8
    %next = "batch_arithmetic.add"(%x, %one) : (i8, i8) -> i8
    return %next : i8
  }
}
MLIR
  )

(define (closer_source count)
  (string-append
   "module {\n"
   (string-join
    (for/list ([index (in-range count)])
      (define length (modulo index 31))
      (string-append
       (format "  func.func @chain_~a(%s0: i8) -> i8 {\n" index)
       (string-join
        (for/list ([step (in-range length)])
          (format "    %c~a = arith.constant ~a : i8\n    %s~a = \"closer_strengths.leave\"(%s~a, %c~a) : (i8, i8) -> i8\n"
                  step (modulo (+ index step) 8) (add1 step) step step))
        "")
       (format "    return %s~a : i8\n  }\n" length)))
    "")
   ;; Also exercise every Boolean recipe in the same source module.
   "  func.func @relation(%x: i8) -> i8 {\n"
   "    %zero = arith.constant 0 : i8\n"
   "    %one = arith.constant 1 : i8\n"
   "    %test = \"closer_strengths.is\"(%x, %zero) : (i8, i8) -> i8\n"
   "    %inverse = \"closer_strengths.none\"(%test) : (i8) -> i8\n"
   "    %either = \"closer_strengths.either\"(%test, %inverse) : (i8, i8) -> i8\n"
   "    %both = \"closer_strengths.both\"(%either, %one) : (i8, i8) -> i8\n"
   "    return %both : i8\n  }\n}\n"))

(define (affine_source)
  (string-append
   "module {\n"
   (string-join
    (for/list ([scale '(0 1 2 3 4 7 16 128)] [offset (in-naturals)])
      (format "  func.func @affine_~a(%x: i8) -> i8 {\n    %scale = arith.constant ~a : i8\n    %offset = arith.constant ~a : i8\n    %product = \"batch_arithmetic.mul\"(%x, %scale) : (i8, i8) -> i8\n    %out = \"batch_arithmetic.add\"(%product, %offset) : (i8, i8) -> i8\n    return %out : i8\n  }\n"
              offset scale offset))
    "")
   "}\n"))

;; Independent evaluator, enumerating all 256 i8 inputs using exact host
;; integers rather than the declaration model, lowering, or solver.
(define (affine_values scale offset)
  (list->treelist
   (sort (remove-duplicates
          (for/list ([x (in-range 256)]) (modulo (+ (* scale x) offset) 256))) <)))

(define built #f)
(define (plugin)
  (or (and (getenv "PILLE_MLIR_SMT_PLUGIN") (resolve_smt_plugin))
      built
      (let ([directory (make-temporary-file "pille-smt-benchmark-~a" 'directory)])
        (plumber-add-flush! (current-plumber)
                           (lambda (_handle)
                             (delete-directory/files directory #:must-exist? #f)))
        (set! built (build_smt_plugin directory (make_toolchain)))
        built)))
