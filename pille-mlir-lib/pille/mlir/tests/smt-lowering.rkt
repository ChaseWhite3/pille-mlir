#lang racket/base

(require file/gunzip
         file/sha1
         json
         rackunit
         racket/list
         racket/port
         racket/runtime-path
         racket/string
         "../../private/mlir/generic.rhm"
         "../../private/mlir/query.rkt"
         "../../private/mlir/tools.rkt")

;; The SMT lowering (private/mlir/lower.rhm) replaced a native MLIR pass plugin.
;; Before the plugin was removed, both were run on the same requests and what
;; the plugin made of each was recorded: a refusal's message, or the digests of
;; the verified SMT module and of the SMT-LIB exported from it. This holds the
;; lowering to that record, request by request. It needs MLIR tools and no
;; solver: equal SMT-LIB text is the same question. The SMT-LIB the lowering
;; writes by itself, which is what a query uses, is held to the exporter's
;; text for every request as well.
(define-runtime-path recorded "fixtures/smt-lowering/plugin-recorded.json.gz")

(define record
  (call-with-input-file recorded
    (lambda (in)
      (define-values (unzipped out) (make-pipe))
      (thread (lambda () (gunzip-through-ports in out) (close-output-port out)))
      (read-json unzipped))))

(define chain (make_toolchain))

(define (digest text) (bytes->hex-string (sha256-bytes (string->bytes/utf-8 text))))

;; The diagnostic itself: what follows `error: ` on its line.
(define (diagnostic error)
  (cond
    [(regexp-match #rx"error: ([^\n]*)" (exn-message error)) => cadr]
    [else (exn-message error)]))

(define modules
  (for/vector ([module (in-list (hash-ref record 'modules))])
    (parse_module (hash-ref module 'ir) (hash-ref module 'irdl) chain)))

(test-case "the lowering makes of every recorded request what the native plugin made of it"
  (define requests (hash-ref record 'requests))
  (check-equal? (length requests) 774)
  (define-values (lowered refused)
    (for/fold ([lowered 0] [refused 0]) ([request (in-list requests)] [index (in-naturals)])
      (define module (vector-ref modules (hash-ref request 'module)))
      (define by-plugin (hash-ref request 'plugin))
      (define made
        (with-handlers ([exn:fail? (lambda (error) (hasheq 'refused (diagnostic error)))])
          (define text (smt_lower_text module (hash-ref request 'manifest)))
          ;; Verified with the stock tools alone, then exported by them.
          (define verified (parse_stock_module text module))
          (define smtlib (to_smtlib verified))
          ;; and what the lowering writes itself, with no tool, is that text
          (check-equal? (smt_lower_smtlib module (hash-ref request 'manifest)) smtlib (format "request ~a" index))
          (hasheq 'mlir_sha256 (digest (module_ir verified))
                  'smtlib_sha256 (digest smtlib)
                  'questions (length (regexp-match* #rx"[(]check-sat[)]" smtlib)))))
      ;; Where the two are known to word a refusal differently, the record says
      ;; so and why; everywhere else they are the same.
      (define expected (hash-ref request 'lowering by-plugin))
      (check-equal? made expected (format "request ~a" index))
      (when (hash-has-key? request 'lowering)
        (check-true (hash-has-key? by-plugin 'refused) (format "request ~a" index)))
      (if (hash-has-key? made 'refused)
          (values lowered (add1 refused))
          (values (add1 lowered) refused))))
  (check-equal? (list lowered refused) '(645 129))
  ;; The differences are these and no others: two readers' own words for malformed
  ;; JSON and for an operation with memory effects (three requests, from the port),
  ;; and nine refusals reworded when the fragment grew on 2026-11-20 (arith.cmpi,
  ;; arith.select, several results and inlined calls). Every one is still a
  ;; refusal: eight of the same thing in other words, and one, a call to a
  ;; function whose operation has no model, now of what that function does.
  (check-equal? (sort (remove-duplicates
                       (for/list ([request (in-list requests)]
                                  #:when (hash-has-key? request 'lowering))
                         (hash-ref (hash-ref request 'plugin) 'refused)))
                      string<?)
                (sort
                 (append
                  '("SMT query: operation 'memref.alloca' has known memory effects, which the pure SMT model cannot represent"
                    "malformed SMT query manifest: [1:2, byte=2]: Expected object key"
                    "SMT query: function @pair returns 2 values; exactly one scalar result is supported"
                    "SMT query: function @multi returns 2 values; exactly one scalar result is supported"
                    "SMT query: function @affine returns 0 values; exactly one scalar result is supported")
                  (for/list ([operation '("arith.addi" "memref.alloca" "func.call" "scf.execute_region" "arith.sitofp")])
                    (format "SMT query: unsupported operation '~a'; only arith.constant, func.return, and operations with declared SMT semantics are supported"
                            operation)))
                 string<?))
  ;; and each reworded refusal still refuses, never lowers
  (check-equal? (for/sum ([request (in-list requests)] #:when (hash-has-key? request 'lowering)) 1) 12))

;; The reader of the generic form refuses what it does not read, with the place.
;; The reader takes the text the tools return, which is immutable.
(define (refusal text)
  (with-handlers ([exn:fail? exn-message])
    (read_module (string->immutable-string text))
    #f))

(test-case "text outside the generic form is refused, never read as something else"
  (define generic (module_generic (vector-ref modules 0)))
  (check-false (refusal generic))
  ;; the custom form, as a caller writes it
  (check-regexp-match #rx"generic MLIR reader: line 1, column 1: expected \"builtin.module\""
                      (refusal "module {\n}\n"))
  ;; anything after the module
  (check-regexp-match #rx"expected the end of the module"
                      (refusal (string-append generic "\"builtin.module\"() ({\n}) : () -> ()\n")))
  ;; a module cut short
  (check-regexp-match #rx"generic MLIR reader"
                      (refusal (substring generic 0 (quotient (string-length generic) 2))))
  ;; brackets that do not balance
  (check-regexp-match #rx"expected balanced brackets"
                      (refusal "\"builtin.module\"() ({\n  \"x.y\"() {a = [1, 2)} : () -> ()\n}) : () -> ()\n"))
  ;; a module that is not `() -> ()`
  (check-regexp-match #rx"generic MLIR reader"
                      (refusal "\"builtin.module\"() ({\n}) : () -> (i32)\n")))

(test-case "a selected function outside the grammar is refused by the reader"
  ;; An operation line that is not `[results =] "name"(operands) … : type`.
  (define text
    (string-append-immutable "\"builtin.module\"() ({\n"
                   "  \"func.func\"() <{function_type = (i8) -> i8, sym_name = \"f\"}> ({\n"
                   "  ^bb0(%arg0: i8):\n"
                   "    %0 = smt.bv.add %arg0, %arg0 : i8\n"
                   "    \"func.return\"(%0) : (i8) -> ()\n"
                   "  }) : () -> ()\n"
                   "}) : () -> ()\n"))
  (define module (read_module text))
  (check-regexp-match #rx"generic MLIR reader: line 4, column 10: expected a string"
                      (with-handlers ([exn:fail? exn-message])
                        ((dynamic-require '(lib "pille/private/mlir/lower.rhm") 'lower_text)
                         text
                         (jsexpr->string
                          (hasheq 'format "pille-smt-query" 'version 1 'function "f"
                                  'inputs (list (hasheq 'name "x" 'width 8))
                                  'operations (hasheq) 'unmodeled '() 'preconditions '()
                                  'property '("eq" ("result") ("input" 0)))))))
  (check-true (and module #t)))
