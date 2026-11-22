# SMT objectives: found by halving, and askable in a scope (2026-11-22)

From the Windows report: a minimize or maximize over a 98-step function took about 10 s each, so Closer asked only
for the durations in conflict.

## What changed

- **How an optimum is found.** `ObjectiveQuery.check` and `Session.check` of an objective no longer run Z3's
  `(minimize s)` / `(maximize s)`, which searches a bitvector's value slowly. The assertions go to the solver once
  and the value is found by halving (`private/mlir/session.rkt` `best-value`): each step asks, in a frame of its
  own, whether the symbol can be on the better side of the middle of what is left; a model moves the bound to the
  value it has, no model moves the other bound past the middle. At most one question for each bit after the first.
  `~timeout` bounds the whole search.
- A standalone `check` of an objective starts a solver process for the search and ends it.
- `ObjectiveQuery.to_smtlib()` and `Optimum.smtlib` are unchanged: the script with Z3's objective in it. Run by
  hand it prints the same value; its inputs may be others that reach it.
- **New: `Scope.minimize(term, ~signed: #false, ~timeout: 10)` and `Scope.maximize(...)`.** The least or greatest
  value of a term under what the scope assumes: `Optimum`, or `Infeasible` with no core. The body and the
  assumptions are the solver's already, so objectives of one scope share them. Not available where
  `PILLE_MLIR_SMT_EXPORT=tools`.

## Time (Mac, the fixture's stepped machine, 98 steps, amounts free below 10)

| | before | now |
| --- | --- | --- |
| one objective, a query of its own | 0.5 to 0.9 s | 0.3 to 0.7 s |
| six objectives (least and greatest of three durations) | about 4 s | 3.0 s as six queries, 1.3 s in one scope |

The Mac case is not the Windows page; what it takes there is to be measured there. Most of an objective's time is
the solver's first answer over the function and the few questions nearest the optimum, which a scope shares.

## For Closer

Open one scope for the page's function, assert the page's expectations, and ask `minimize` and `maximize` of each
duration there. A named conflict is still a `Query`'s to report (`Infeasible.core`): a scope's assumptions are not
named.

## Tests

`smt-bounded.rkt`, "an objective in a scope is the query's, and the solver's own optimizer's, and leaves the scope
as it was": scope objectives against standalone ones and against z3's optimizer run on the outcome's script;
signed; infeasible; an input named as the symbol would be; the machine's durations.

## Documentation

`pille-mlir-lib/README.md`, "Objectives" and "Scopes". The Scribble manual has nothing on `pille/mlir`.
