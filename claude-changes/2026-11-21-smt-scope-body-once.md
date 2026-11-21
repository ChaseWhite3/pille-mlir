# SMT scopes: the function's body is sent once (2026-11-21)

Decided by the owner: most readers will not be reading the MLIR, so a scope need not send what the exporter writes.

## What changed

Opening a scope (`Dialect.smt_scope`) lowers the function's body once and sends it to the session's solver with the
input declarations: one `(define-fun pille_vN () sort (op operands...))` for each operation of the body, in order
(`private/mlir/lower.rhm` `scope_begin`). `assert`, `check` and `check_all` then lower their formula in the same
context (`scope_lower`) and send it written over those names, so a question's text holds its own formula and none
of the body.

- The names begin `pille_v`, with `_` added until no input's name begins the same way.
- An operation's requirements are part of the body and are still shown with every claim.
- An outcome's `smtlib` holds the declarations, the definitions, the assumptions and the goal, and gives the same
  answer run by itself.
- `PILLE_MLIR_SMT_EXPORT=tools` keeps the earlier behaviour: each question whole, exported by `mlir-translate`.
  In `direct` and `both` a scope sends the body once; `both` has nothing of the exporter's to compare a scope's
  text with.

No binding changed.

## Time

The fixture's stepped machine, cache off, deepening from 1 step to all of them with `check_all`, solving included:

| | 12 steps | 48 steps |
| --- | --- | --- |
| each claim whole, through the tools (2026-11-20) | 63 ms | 1,262 ms |
| each claim whole, written by the lowering | 30 ms | 454 ms |
| the body once | 6 ms | 79 ms |

## Tests

`smt-bounded.rkt`: the same claims, with and without assumptions, of a scope that sends the body once and of one
that sends each question whole give the same answers, for the sound machine and the faulty one, and each
question's script run by hand gives its answer; a claim's text does not grow with the body; inputs named
`pille_v0` and `pille_v_1`; an operation with a requirement, unproved where it may fail and proved where the scope
assumes it. With the definitions' operands written in the wrong order, three of these fail.

## Documentation

`pille-mlir-lib/README.md`, "Scopes". The Scribble manual has nothing on `pille/mlir`.
