# SMT queries: asked together in a scope, and built without the MLIR tools (2026-11-20)

Two changes for speed in `pille/mlir`. Measured on the Mac with the tools' cache off, a 32-bit round trip:

| | before | after |
| --- | --- | --- |
| build a query | 28 ms | under 1 ms |
| build and check on a session | 28 ms | under 1 ms |
| `scope.check`, a claim | 27 ms | under 1 ms |
| twelve claims in a scope | about 320 ms | 5 ms with `check_all` |
| build a batch of 20 | 37 ms | 1 ms |

## `Scope.check_all`

`scope.check_all([property, ...], ~timeout: 10) :: List.of(Outcome)`: each claim answered as `check` answers one,
in order, their formulas lowered together. A timeout or failure ends the scope, and the claims after it are a
`Failure` of kind `#'closed_session`. This is the only new public binding.

## The lowering writes the SMT-LIB

Nearly all of a query's time was starting `mlir-opt` to verify the lowered SMT module and `mlir-translate` to
export it. `private/mlir/lower.rhm` now writes, beside the module, the SMT-LIB the exporter gives for it,
character for character (`smtlib_of`), and a query uses that. The exporter's rules, found by comparing texts:

- a declaration where it stands; a constant in hexadecimal where its width is a multiple of 4, binary otherwise;
- an assertion binds each operation of its formula with a `let`, once, an operation after its operands, and of an
  operation's operands the last first;
- the bound names are `tmp`, `tmp_0`, `tmp_1`, ..., going on from one assertion to the next within a solver, and
  passing over a name a declared symbol has.

`PILLE_MLIR_SMT_EXPORT` (or the parameter `smt_export_mode` of `private/mlir/query.rkt`) chooses: `direct` (the
default), `tools` (verified and exported by the tools, as before), `both` (both, and an error where the texts
differ). `Query.module`, `Batch.module` and `ObjectiveQuery.module` are verified by stock `mlir-opt` when first
asked for.

What `direct` gives up: stock MLIR no longer checks the lowered module of the question at hand when the query is
built. What holds it instead: the solver-backed test files run in `both`, so each of their questions is made both
ways and compared; `smt-lowering.rkt` compares the two texts for each of the 645 recorded questions the lowering
accepts. The first run of that comparison found the passing-over rule above (an input named `tmp`).

Nothing a caller sees changes: the SMT-LIB of every query is the text it was. Closer's `closer_exports/mlir`
check passes unchanged.

## Documentation

`pille-mlir-lib/README.md` says this under "How the SMT-LIB is made" and lists `check_all`. The Scribble manual
has nothing on `pille/mlir`.
