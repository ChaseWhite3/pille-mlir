# A second vocabulary: Pille's expressions read into MLIR (2026-11-19, prototype)

A prototype, in tests only, of what Culpepper, Felleisen, Flatt and Krishnamurthi call a vocabulary of micros
("From Macros to DSLs: The Evolution of Racket", SNAPL 2019): the same source text read by Pille's own expression
space and lowered to LLVM, and read by a second space and lowered to MLIR. No public binding of Pille changed.

## What Pille already has

Each `pille_expr` macro is close to a micro. It expands to a builder, not to the value's code: `if` expands to a
call of `concretize_if`, which checks and specializes (a Boolean test, the branches' types unified, a test known at
compile time choosing its branch) and returns an `Expr` holding a type and a `lower` closure that writes LLVM. That
is the paper's two vocabularies, type-check and compile, in one Output. The checking runs at concretization, when
the builders are run (in hosted mode, the first call of each specialization), not at Rhombus expansion.

## The prototype

- `pille/pille/tests/vocabulary/mlir.rhm`: a space, `mlir_expr`, beside `pille_expr`, with integer and Boolean
  literals, parentheses, `+`, `*`, `<`, `==` and `if`, and `mlir_fun name(x :: Int(N), ...): body`. Each form's
  expansion builds an `MExpr`: a Pille `Type` and an emitter of MLIR (arith, scf, func). The type side is Pille's:
  its `Type` values, `eval_unify` and folding of compile-time values. Only emission is new; its coercions are the
  widenings unification gives (sign or zero extension). A function is concretized, lowered to MLIR, verified and
  lowered through `pille/mlir`, and compiled and run by Pille's ORC JIT on its first call.
- `pille/pille/tests/mlir_vocabulary.rhm`: each program written once and read by both spaces (`both`), with both
  answers checked: arithmetic with literals, nested `if`, Pille's widening of `Int(8)` with `Int(32)` and of
  `UInt(8)` with `Int(8)` (to `Int(9)`, which MLIR takes as `i9`), folding, and a non-Boolean test failing to
  concretize in both. A swapped zero/sign extension in the emitter makes three of its checks fail.

Left out: Pille's undefined-behavior policies (the MLIR vocabulary wraps where Pille's default policy panics; a
check records the difference), floats, mutation, loops, calls, and every form not listed. A form not defined in
the second space is unbound there; no vocabulary defers to another.

## A Pille repair found by it

`IntType`'s `read_from_rhombus` (`pille-lib/pille/private/kernel/core_types.rhm`) took the sign of a hosted result
from the top bit of its bytes, not of its width, so a negative `Int(9)` came back as 511. It and `UIntType`'s now
read only the low `width` bits. Widths that are whole bytes read as before. `pille/pille/tests/interop.rhm` has
checks for widths 9 and 12. This was committed on its own.

## For the manual

Nothing here is public API. The repair changes what hosted Pille returns for a negative integer of a width that is
not a multiple of 8: it is now that integer.
