#lang racket/base
;; Every refusal of the lowering that a manifest or a verified module can reach, sent through
;; both lowerings (PILLE_MLIR_SMT_COMPARE): the manifests bypass the one query.rkt derives.
(require json racket/list racket/string
         pille/private/mlir/query pille/private/mlir/schema pille/private/mlir/tools)
(define arithmetic (dynamic-require '(lib "pille/mlir/tests/semantics/valid.rhm") 'arithmetic))
(define chain (make_toolchain))
(define module
  (parse_module #<<M
module {
  func.func @plain(%a: i32, %b: i32) -> i32 {
    %s = "arithmetic.add"(%a, %b) : (i32, i32) -> i32
    %r = "arithmetic.sub"(%s, %b) : (i32, i32) -> i32
    return %r : i32
  }
  func.func @narrow(%a: i8) -> i8 {
    %r = "arithmetic.add"(%a, %a) : (i8, i8) -> i8
    return %r : i8
  }
  func.func @constant_note(%a: i32) -> i32 {
    %c = "arith.constant"() {value = 1 : i32, note = "x"} : () -> i32
    return %c : i32
  }
  func.func @return_note(%a: i32) -> i32 {
    "func.return"(%a) {note = 1 : i32} : (i32) -> ()
  }
  func.func @overflow(%a: i32) -> i32 {
    %r = arith.addi %a, %a : i32
    return %r : i32
  }
  func.func @region(%a: i32) -> i32 {
    %r = scf.execute_region -> i32 {
      scf.yield %a : i32
    }
    return %r : i32
  }
  func.func @jump(%a: i32) -> i32 {
    cf.br ^next
  ^next:
    return %a : i32
  }
  func.func @loads(%a: i32) -> i32 {
    %slot = memref.alloca() : memref<i32>
    %r = memref.load %slot[] : memref<i32>
    return %r : i32
  }
  func.func @float_result(%a: i32) -> i32 {
    %f = "arithmetic.anything"(%a, %a) : (i32, i32) -> i32
    %g = arith.sitofp %f : i32 to f32
    return %a : i32
  }
  func.func @argument_note(%a: i32 {pille.note = "x"}) -> i32 {
    return %a : i32
  }
  func.func @wide_constants(%a: i64, %b: i1) -> i64 {
    %t = arith.constant true
    %m = arith.constant -1 : i64
    %r = "arithmetic.add"(%a, %m) : (i64, i64) -> i64
    return %r : i64
  }
}
M
                (dialect_irdl arithmetic) chain))

(define (binary tag) (hasheq 'operands '("lhs" "rhs") 'result "out" 'locals '() 'value (list tag '("operand" 0) '("operand" 1))))
(define operations (hasheq 'arithmetic.add (binary "add") 'arithmetic.sub (binary "sub")))
(define base
  (hasheq 'format "pille-smt-query" 'version 1 'function "plain"
          'inputs (list (hasheq 'name "x" 'width 32) (hasheq 'name "y" 'width 32))
          'result_width 32 'operations operations 'unmodeled '() 'preconditions '()
          'property '("eq" ("result") ("input" 0))))
(define (with . changes)
  (let loop ([value base] [changes changes])
    (if (null? changes) value (loop (hash-set value (car changes) (cadr changes)) (cddr changes)))))
(define (without . keys) (for/fold ([value base]) ([key keys]) (hash-remove value key)))
(define (modeled add) (hash-set operations 'arithmetic.add add))
(define (add-model . changes)
  (let loop ([value (binary "add")] [changes changes])
    (if (null? changes) (modeled value) (loop (hash-set value (car changes) (cadr changes)) (cddr changes)))))
(define one8 (list (hasheq 'name "x" 'width 8)))
(define one32 (list (hasheq 'name "x" 'width 32)))
(define (for-function name inputs . changes)
  (apply with 'function name 'inputs inputs 'result_width (json-null) 'property '("eq" ("result") ("result")) changes))

(define cases
  (list
   ;; the document
   "[]" "{not json" "3" (with 'version 3) (with 'format "other") (without 'version)
   (with 'version 2) (with 'version 2 'queries (list 7)) (with 'version 2 'queries (list (without 'operations) "x"))
   ;; one query's fields
   (with 'mode "other") (without 'function) (without 'inputs) (without 'operations) (without 'unmodeled)
   (without 'preconditions) (without 'property) (with 'mode "values")
   (with 'mode "values" 'result_symbol "r" 'defined_symbol "r")
   (with 'mode "values" 'result_symbol "x" 'defined_symbol "d")
   (with 'mode "values" 'result_symbol "r" 'defined_symbol "d")
   (with 'mode "proof") (with 'property (json-null))
   (with 'inputs (list (hasheq 'name "x" 'width 12))) (with 'inputs (list "x")) (with 'inputs (list (hasheq 'name 3 'width 8)))
   (with 'result_width 7) (with 'result_width "x") (with 'result_width (json-null)) (with 'result_width 32.0)
   (with 'unmodeled (list 3)) (with 'unmodeled (list "arithmetic.add"))
   (with 'operations (hasheq 'arithmetic.add 3)) (with 'operations (modeled (hash-remove (binary "add") 'value)))
   (with 'operations (add-model 'operands (list 3 4))) (with 'operations (add-model 'locals (list (list "t"))))
   (with 'operations (add-model 'locals (list (list 3 '("operand" 0)))))
   ;; expressions of a model
   (with 'operations (add-model 'value 3)) (with 'operations (add-model 'value '()))
   (with 'operations (add-model 'value '("operand" "x"))) (with 'operations (add-model 'value '("operand" -1)))
   (with 'operations (add-model 'value '("local" 0)))
   (with 'operations (add-model 'locals (list (list "t" '("operand" 1))) 'value '("add" ("local" 0) ("operand" 0))))
   (with 'operations (add-model 'value '("const" "3" ("width" 12))))
   (with 'operations (add-model 'value '("const" "3" ("like" ("operand" 0)))))
   (with 'operations (add-model 'value '("const" "3" ("like" ("result")))))
   (with 'operations (add-model 'value '("const" "3" ("like" ("add" ("operand" 0) ("const" "1" ("width" 8)))))))
   (with 'operations (add-model 'value '("const" "3" ("like" ("select" ("operand" 0) ("operand" 1) ("operand" 0) ("operand" 1))))))
   (with 'operations (add-model 'value '("const" "3" ("like" ("frob" 1)))))
   (with 'operations (add-model 'value '("const" "3" ("other" 1))))
   (with 'operations (add-model 'value '("const" 3 ("width" 32))))
   (with 'operations (add-model 'value '("const" "3")))
   (with 'operations (add-model 'value '("const" "x3" ("width" 32))))
   (with 'operations (add-model 'value '("const" "-" ("width" 32))))
   (with 'operations (add-model 'value '("const" "123456789012345678901" ("width" 32))))
   (with 'operations (add-model 'value '("const" "4294967296" ("width" 32))))
   (with 'operations (add-model 'value '("const" "-2147483649" ("width" 32))))
   (with 'operations (add-model 'value '("const" "-2147483648" ("width" 32))))
   (with 'operations (add-model 'value '("const" "4294967295" ("width" 32))))
   (with 'operations (add-model 'value '("add" ("operand" 0) ("const" "1" ("width" 8)))))
   (with 'operations (add-model 'value '("mul" ("const" "1" ("width" 8)) ("operand" 0))))
   (with 'operations (add-model 'value '("add" ("operand" 0))))
   (with 'operations (add-model 'value '("select" ("operand" 0) ("const" "1" ("width" 8)) ("operand" 0) ("operand" 1))))
   (with 'operations (add-model 'value '("select" ("operand" 0) ("operand" 1) ("operand" 0) ("const" "1" ("width" 8)))))
   (with 'operations (add-model 'value '("select" ("operand" 0) ("operand" 1) ("operand" 0) ("operand" 1))))
   (with 'operations (add-model 'value '("select" ("operand" 0) ("operand" 1) ("operand" 0))))
   (with 'operations (add-model 'value '("result")))
   ;; what a model requires
   (with 'operations (add-model 'requires (list '("eq" ("operand" 0) ("operand" 1)))))
   (with 'operations (add-model 'requires (list '("or" ("eq" ("operand" 0) ("operand" 1)) ("eq" ("operand" 0) ("const" "0" ("width" 32)))))))
   (with 'operations (add-model 'requires (list '("eq" ("operand" 0) ("const" "1" ("width" 8))))))
   (with 'operations (add-model 'requires (list '("frob"))))
   (with 'operations (add-model 'requires (list 3)))
   (with 'operations (add-model 'requires (list '("eq" ("operand" 0) ("operand" 1)))) 'mode "values" 'result_symbol "r" 'defined_symbol "d")
   (with 'operations (add-model 'requires (list '("eq" ("operand" 0) ("operand" 1)) '("eq" ("operand" 1) ("operand" 1)))) 'mode "values" 'result_symbol "r" 'defined_symbol "d")
   ;; properties and preconditions
   (with 'property 3) (with 'property '()) (with 'property '("eq" ("result")))
   (with 'property '("eq" ("result") ("const" "1" ("width" 8))))
   (with 'property '("not" ("eq" ("result") ("input" 1))))
   (with 'property '("not")) (with 'property '("and")) (with 'property '("and" ("eq" ("result") ("input" 0))))
   (with 'property '("or" ("eq" ("result") ("input" 0)) ("not" ("eq" ("input" 1) ("input" 0))) ("eq" ("input" 1) ("result"))))
   (with 'property '("eq" ("input" 2) ("result"))) (with 'property '("eq" ("result" 0) ("result")))
   (with 'property '("eq" ("local" 0) ("result"))) (with 'property '("eq" ("select" ("input" 0) ("input" 1) ("input" 0) ("input" 1)) ("result")))
   (with 'property '("eq" ("const" "1" ("like" ("input" 0))) ("result")))
   (with 'property '("eq" ("sub" ("input" 0) ("mul" ("input" 1) ("const" "-1" ("width" 32)))) ("result")))
   (with 'preconditions (list '("eq" ("input" 0) ("input" 1)) '("frob")))
   (with 'preconditions (list '("eq" ("input" 0) ("const" "7" ("width" 32))) '("not" ("eq" ("input" 1) ("const" "0" ("width" 32))))))
   ;; the selected function and its body
   (with 'function "missing") (with 'inputs one32) (with 'result_width 64)
   (with 'inputs (list (hasheq 'name "x" 'width 32) (hasheq 'name "y" 'width 64)))
   (for-function "narrow" one8 'result_width 8)
   (for-function "narrow" one8 'operations (add-model 'value '("const" "200" ("like" ("result")))))
   (for-function "narrow" one8 'operations (add-model 'value '("const" "-128" ("like" ("operand" 0)))))
   (for-function "narrow" one8 'operations (add-model 'value '("const" "256" ("like" ("result")))))
   (for-function "constant_note" one32) (for-function "return_note" one32)
   (for-function "overflow" one32) (for-function "overflow" one32 'operations (hasheq 'arith.addi (binary "add")))
   (for-function "overflow" one32 'unmodeled (list "arith.addi"))
   (for-function "region" one32) (for-function "region" one32 'operations (hasheq 'scf.execute_region (hasheq 'operands '() 'result "out" 'locals '() 'value '("const" "0" ("width" 32)))))
   (for-function "jump" one32)
   (for-function "loads" one32 'operations (hasheq 'memref.alloca (hasheq 'operands '() 'result "out" 'locals '() 'value '("const" "0" ("width" 32)))))
   (for-function "float_result" one32 'operations (hasheq 'arithmetic.anything (binary "add")))
   (for-function "float_result" one32 'operations (hasheq 'arithmetic.anything (binary "add") 'arith.sitofp (hasheq 'operands '("in") 'result "out" 'locals '() 'value '("operand" 0))))
   (for-function "argument_note" one32)
   (for-function "wide_constants" (list (hasheq 'name "x" 'width 64) (hasheq 'name "flag" 'width 1)))
   (for-function "wide_constants" (list (hasheq 'name "x" 'width 64)))
   (for-function "wide_constants" (list (hasheq 'name "weird \"name\" \\ here" 'width 64) (hasheq 'name "flag" 'width 1)))
   ;; a batch: a function lowered once and asked again under other names
   (hash-set* (with 'version 2) 'queries
              (list (without 'format 'version 'operations 'unmodeled)
                    (hash-set* (without 'format 'version 'operations 'unmodeled)
                               'inputs (list (hasheq 'name "p" 'width 32) (hasheq 'name "q" 'width 32))
                               'property '("eq" ("result") ("input" 1)))
                    (hash-set* (without 'format 'version 'operations 'unmodeled 'property) 'mode "values" 'result_symbol "r" 'defined_symbol "d")
                    (hash-set* (without 'format 'version 'operations 'unmodeled) 'inputs one32)))))

(for ([entry (in-list cases)] [index (in-naturals)])
  (define text (if (string? entry) entry (jsexpr->string entry)))
  (define outcome
    (with-handlers ([exn:fail? (lambda (error) (car (reverse (string-split (exn-message error) "\n"))))])
      (smt_lower_text module text)
      "lowered"))
  (printf "~a\t~a\n" index outcome))
