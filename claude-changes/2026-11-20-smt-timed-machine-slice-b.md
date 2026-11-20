# SMT queries: calls, scopes, objectives on a session (2026-11-20)

Slice B of `CLOSER_TIMED_MACHINE_WORK_ORDER.md`. Everything is in `pille/mlir/smt` and `pille/mlir/dialect`. A query
that could be written before means what it meant.

## Calls

`func.call` to a function of the same module is lowered: the callee's one block is lowered where the call stands,
with its arguments bound to the call's operands, so a step function is written once and called K times. The callee
is held to the fragment a selected function is. These are refused before any solver runs, each naming the call and
its place: a function that would call itself, directly or through another; a call to a symbol that is not a
`func.func` with a body; an attribute on the call other than `callee`; a callee with an unmodeled operation, control
flow or function attributes outside the allowed three.

MLIR's own `inline` pass is not used. On LLVM 23.1.5 it leaves a call to a function that uses an operation
registered through IRDL, since such an operation has no inliner interface.

Six entries of the frozen lowering record changed with this, each with its reason in the record: requests that the
removed plugin refused as "an operation outside the fragment (`func.call`)" are now lowered, or refused for what
the callee holds.

## New binding in `pille/mlir/dialect`

- `Dialect.smt_scope(session :: smt.Session, module, ~function:, ~inputs:) :: smt.Scope`.

## New bindings in `pille/mlir/smt`

- `Scope`, with `assert(formula)`, `push()`, `pop()`, `check(property, ~timeout: 10) :: Outcome`, `close()`, and
  the properties `function`, `dialect`, `inputs`, `assumptions`, `is_open`.
- `Session.check` accepts an `ObjectiveQuery` and gives `Optimum` or `Infeasible`, as the query's own `check` does.

## How a scope behaves

- Opening one declares the function's inputs once in the session's solver. An assertion stays until its frame is
  popped; `close()` pops everything.
- `check(property)` gives `Proved` or `Counterexample` (inputs in argument order). It runs in a frame of its own, so
  it leaves the scope as it found it.
- Each question lowers its formula over the function anew, through `mlir-opt` and `mlir-translate`; what a scope
  saves is the solver's process and what the solver has learned of the assertions it holds. The work order asked
  for no re-lowering; the lowering is what turns a claim about results into SMT, so only the solver side is kept.
- While a scope is open the session's `check` and `values` are refused. A timeout or solver failure ends the
  solver process and the scope with it.
- A scope takes plain formulas. Names, cores and `Infeasible` belong to `Query`; assumptions that cannot hold
  together make every claim in a scope `Proved`.
- An outcome's `smtlib` is one script (what the solver held, then the goal) that gives the same answer by itself.
- An objective on a session resets the solver first, since Z3's optimizer state is not kept apart from a
  solver's.

## Many inputs

Counterexamples of functions with 200 inputs report every input in argument order within the default timeout, at
widths 8 and 32. The work order says width 3; that is not a width this fragment has (1, 8, 16, 32, 64), and none
was added.

## Tests

`pille-mlir-lib/pille/mlir/tests/smt-bounded.rkt` (calls, scopes, session objectives, 200 inputs, a stepped machine
against an evaluator, and the acceptance: twelve symbolic messages proved for the sound machine, a counterexample
with an on and then a disconnect for the altered one, replayed on the evaluator, and deepening 1 to 12 in one scope
agreeing with fresh queries). `machine-fixture.rkt` holds the machine. `smt-api.rhm` has the Rhombus-side cases.

## Documentation

`pille-mlir-lib/README.md`'s "Verifying properties with declared SMT semantics" was rewritten at the user's request
to match the code: the plugin it described was removed on 2026-11-14. The Scribble manual has nothing on
`pille/mlir` and was not touched.
