# SMT queries: an Infeasible core none of whose names can be left out (2026-11-20)

Reported from Closer: for "escalation after 5 s" against a page's settings, `Infeasible.core` named three durations
where the initial duration alone conflicted. Pille asked Z3 to minimize its core (`smt.core.minimize`) and passed
on what it got; Z3's minimizing is its best effort. That case was not reproduced on the Mac with Z3 5.3.3, so the
test uses a solver that names every asserted name.

## What changed

`Infeasible.core` is now shrunk in Pille (`private/mlir/solver.rkt` `shrink-core`): each name of the solver's core
is left out in turn and the feasibility question asked again without that precondition; where the rest still
cannot hold together the name is dropped, and a smaller core the solver gives on the way is taken. This is done
wherever a core is: `Query.check`, `Batch.check`, `Session.check`, and objectives.

- At most one further question for each name the solver gave, and only where the answer is `Infeasible`. Standalone
  each is a run of the solver; on a session it is the same process.
- A further question that is not decided in time keeps its name, so a core is always a set that cannot hold
  together. On a session such a question ends the solver's process, which the next question starts again; the
  answer is still `Infeasible`.
- Where one name conflicts with preconditions that have no name, it is the whole core; where those without a name
  conflict alone, the core is empty, as before.
- `Infeasible.smtlib`, run by hand, still answers `unsat`; the core Z3 prints for it is its own and may hold more
  names than `core`.

No binding changed. Closer's own step that drops each name and asks again is no longer needed.

## Test

`smt-synthesis.rkt`, "a core is shrunk until no name can be left out, whatever the solver named": Z3 behind a
wrapper that answers every `(get-unsat-core)` with all the names asserted; four named preconditions of which two
conflict give those two, standalone, on a session, in a batch and for an objective. With the shrinking taken out
the test fails.
