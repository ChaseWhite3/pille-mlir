#lang racket/base
;; Top-level operations nobody selects are passed over, whatever they hold.
(require json racket/string
         pille/private/mlir/query pille/private/mlir/schema pille/private/mlir/tools)
(define arithmetic (dynamic-require '(lib "pille/mlir/tests/semantics/valid.rhm") 'arithmetic))
(define module
  (parse_module #<<M
module {
  memref.global "private" constant @table : memref<2xi32> = dense<[1, 2]>
  func.func private @strings() attributes {note = "}) : () -> () \" loc(\\", other = [1, "a>b", {k = "<("}]}
  func.func @affine(%m: memref<8xf32>, %n: index) {
    affine.for %i = 0 to %n {
      affine.if affine_set<(d0) : (d0 - 1 >= 0)>(%i) {
        %v = affine.load %m[%i] : memref<8xf32>
        affine.store %v, %m[%i] : memref<8xf32>
      }
    }
    %t = "arithmetic.anything"(%n, %n) {map = affine_map<(d0, d1) -> (d1, d0)>, cmp = "x -> y >= z", shape = tensor<?x4xf32>} : (index, index) -> index
    return
  }
  func.func @multi(%a: i32) -> (i32, i32) {
    %p, %q = func.call @multi(%a) : (i32) -> (i32, i32)
    return %p, %q : i32, i32
  }
  func.func @chosen(%a: i16, %b: i16) -> i16 {
    %s = "arithmetic.add"(%a, %b) : (i16, i16) -> i16
    %r = "arithmetic.mul"(%s, %s) : (i16, i16) -> i16
    return %r : i16
  }
}
M
                (dialect_irdl arithmetic) (make_toolchain)))
(define x (smt_input "x" 16)) (define y (smt_input "y" 16)) (define r (smt_result 16))
(define (try thunk) (with-handlers ([exn:fail? (lambda (e) (displayln (exn-message e)))]) (displayln (thunk))))
(try (lambda () (query_smtlib (make_smt_query arithmetic module "chosen" (list x y) (smt_eq r (smt_binary 'mul (smt_binary 'add x y) (smt_binary 'add x y))) '()))))
(try (lambda () (make_smt_query arithmetic module "multi" (list (smt_input "x" 32)) (smt_eq (smt_result 32) (smt_result 32)) '())))
(try (lambda () (make_smt_query arithmetic module "affine" (list x) (smt_eq r r) '())))
(try (lambda () (make_smt_query arithmetic module "strings" '() (smt_eq r r) '())))
(try (lambda () (make_smt_query arithmetic module "table" '() (smt_eq r r) '())))
