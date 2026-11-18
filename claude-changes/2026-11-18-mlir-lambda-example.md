# Lambdas through MLIR, specified in Redex (2026-11-18)

A test that compiles a small lambda calculus to MLIR and runs it, with a Redex model as its specification. No
public binding of Pille changed.

## What MLIR has, and what this adds

MLIR has function values (`func.constant`, `func.call_indirect`) but no lambda that captures variables. A compiler
gets one by closure conversion: each lambda becomes a code block taking a record, and the record (code address,
then captured values) is built where the lambda is. That is how an assembly program has closures, and it is what
the example does, in MLIR's LLVM dialect.

## Files

- `pille/pille/tests/lambda/model.rkt`: Redex. The source language Λ (numbers, variables, `λ`, application, `+`,
  call by value) and its reduction relation; the converted language Λc (code blocks, `closure`, `env-ref`, `call`)
  and its own reduction relation; `convert` between them; and `conversion_holds`, which checks that a program and
  its conversion come to the same answer (a number, a procedure, or stuck) on random terms.
- `pille/pille/tests/lambda/emit.rhm`: a converted program as MLIR text. Every value is an i64 (a number or a
  record's address). Records live in one global array with a bump pointer, so the module needs no outside symbol;
  nothing is freed, and each entry point starts the heap over. There are no tags: a program the model calls stuck
  has no meaning in the machine code, so only programs that come to a number are run.
- `pille/pille/tests/mlir_lambda.rhm`: verifies one module of all the programs through `pille/mlir`, turns it into
  bitcode, compiles and runs it with Pille's ORC JIT (as `tests/mlir.rhm` does), and holds each answer to the model's.
  Seven named examples (an adder, twice, compose, Church multiplication, shadowing, the 64-bit wrap) and 24 random
  programs.
- `pille/info.rkt`: `redex-lib` added to `build-deps`, for the test.

## Random terms

Redex's generator from the grammar rarely produced a lambda that captures a variable (5 in 1,200), and its
generator from a type judgment never produced a record of two values (800 terms, sizes 4 to 10). With only those, a
conversion that stored a record's values in the wrong order passed every check. The model therefore also draws
well-typed terms by hand, biased toward the variables in scope, half of them with a record of two values or more.
Reduction is still Redex's. The test was checked against two deliberate faults, a record read one word off in the
emitter and a reversed record in the conversion: each makes it fail.

## For the manual

Nothing here is public API. If the manual describes `pille/mlir` with examples, this is one: a frontend that
closure-converts and emits the LLVM dialect, verified and run through the existing bridge.
