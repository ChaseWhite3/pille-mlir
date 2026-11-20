# Work order for timed state machines in Pille's SMT layer, for Closer

Add the generic primitives Closer needs to ask Z3 questions about a small timed state machine: comparisons,
selection, several results, composition, overflow guards, objectives, unsat cores and incremental scopes. Closer
writes the machine and decides what the answers mean; Pille supplies only what any declared dialect could use.

This is an implementation handoff for an AI working on Pille. Deliver code, focused tests, and notes as
"Deliverables" says. Complete Slice A before starting Slice B. Slice C is independent.

Amended on review, 2026-11-20. The amendments are marked **Amended** where they stand, and listed at the end.

## Repository and working rules

**Amended.** The target is the Pille checkout (`C:/GitProj/pille-mlir` on Windows), branch **`main`**. The `mlir`
branch this order first named was merged into `main` and deleted on 2026-11-20; a checkout still on it switches
with `git fetch chase --prune` and `git switch main`, which loses nothing, since `main` holds everything `mlir`
had. Commit on `main` and push to the `chase` remote (`ChaseWhite3/pille-mlir`); make no feature branch, and never
push to `origin`. Start from commit `7659c9e` or later: it changed `pille-mlir-lib/pille/private/mlir/tools.rkt`
(the MLIR tools are found without `PILLE_MLIR_PREFIX`) and the integration tests' tool lookup.

Read `CLAUDE.md` first. Closer's checkout (`C:/GitProj/anote`) uses this one as `PILLE_HOME` and snapshots it for
its checks, so keep the branch building and the existing tests passing at every commit; Closer's
`closer_exports/mlir/smt.rhm` must keep working unchanged. Run `raco pille doctor` first on a new machine: it says
whether Racket, LLVM, the MLIR tools and Z3 are usable there. Rebuild with `raco make` before `raco test`, which
does not rebuild a module whose dependencies changed.

Extend `pille-mlir-lib/pille/mlir/smt.rhm`, `pille/private/mlir/query.rkt`, `lower.rhm` and `session.rkt`. Do not
add a parallel query system. Keep the existing policy of `SMT_WORK_ORDER.md`: exact widths, no implicit conversions,
no inferred signedness, SMT Booleans distinct from `i1`, and unsupported constructs rejected with a diagnostic that
names the operation and its location. Nothing here may know about alarms, phases or Closer; the example below is
Closer's, used only as an acceptance fixture.

## Why Closer needs this

Closer models how a server takes an alarm through phases over time: idle, initial, escalation, re-escalation 1, 2,
..., auto-disconnect. The phases are left after configurable durations (initial `I`, escalation `E`, re-escalation
`R`, auto-disconnect `A`), and messages (on, off, disconnect, respond, a unit of time) drive the machine. The
machine exists today as a PLT Redex model and as Rhombus, and is checked by enumerating every message sequence up to
four messages with fixed small durations.

Closer wants to ask two questions that enumeration cannot answer:

1. **Parameter synthesis.** A test page expects certain phases at certain lines (for example re-escalation 2 after
   65 seconds). For which durations `I`, `E`, `R`, `A` do all of the page's expectations hold? What is each
   duration's least and greatest admissible value given the others? When no durations satisfy them all, which
   expectations conflict?
2. **Bounded model checking.** Do the ordering claims (an alarm never enters auto-disconnect; a response stops
   re-escalation; nothing is overdue) hold for every sequence of up to K symbolic messages, K well beyond 4? If not,
   what sequence breaks one?

Both reduce to bitvector formulas over a step function unrolled a known number of times, with durations and
messages as inputs.

## Current implementation (as read on 2026-11-20)

`pille/mlir/smt` builds terms over bitvector inputs and a function's result (`input`, `result`, `const`, `add`,
`sub`, `mul`), Boolean formulas (`eq`, `not`, `and`, `or`), and queries of the form `preconditions && !property`
over one straight-line, single-block `func.func` with one scalar result, whose operations carry declared SMT
semantics. Outcomes are `Proved`, `Counterexample` (one assignment per argument), `Unknown`, `Timeout` and
`Failure`. `Batch` runs several queries; `ValuesSpec` enumerates a function's possible results; `Session` keeps one
solver process and uses `push`/`pop` internally for each query. The lowering accepts `arith.constant`,
`func.return` and declared operations only.

(Checked against the code on review: this is accurate. `select` exists only inside declared semantics, not as
`arith.select`.)

## Slice A: parameter synthesis

**A1. Comparisons.** Formula builders `ult`, `ule`, `ugt`, `uge`, `slt`, `sle`, `sgt`, `sge` over terms of equal
width, and lowering of `arith.cmpi` with every predicate to the matching SMT bitvector comparison. A `cmpi` result
is an `i1` value in the body; where it is used as a predicate, the conversion is explicit (`i1 == 1`), as today.

**A2. Selection.** Lowering of `arith.select` to SMT `ite`, and a term builder `ite(formula, then, else)` over terms
of equal width. A step function's branches (stay in a phase, or enter the next) are selects.

**A3. Several results.** Functions returning several scalars (`func.return %a, %b, …`), with
`result(index, ~width:)` naming each in properties, preconditions and counterexamples. Closer's state is several
fields (phase, level, entered at, responded, clock), and one function may compute every expected line's phase. Keep
`result(~width:)` meaning the single result of a one-result function.

**A4. Overflow guards.** Formula builders saying an addition, subtraction or multiplication of unsigned or signed
terms does not overflow (`no_overflow_add(a, b, ~signed:)` and the like, lowered to the SMT idiom of comparing in a
wider width). Durations are summed (`I + E + 2R`), so a synthesis query must exclude answers that hold only by
wrapping. Do not change the wrapping meaning of `add`.

> **Amended.** MLIR's `smt` dialect has no extend operation (checked on LLVM 23.1.5: its bitvector operations are
> add, and, ashr, cmp, concat, constant, extract, lshr, mul, neg, not, or, repeat, sdiv, shl, smod, srem, udiv,
> urem, xor). Widen with `smt.bv.concat`: zeros in front for unsigned, and for signed the sign bit taken with
> `smt.bv.extract` and copied with `smt.bv.repeat`. Multiplication needs twice the width, not one bit more.

**A5. Named preconditions and unsat cores.** Each precondition may carry a name
(`~named: "event-phases.md:22"`). When the preconditions are inconsistent, a new outcome
`Infeasible(core :: List.of(String))` names a set whose conjunction is unsatisfiable, from Z3's `get-unsat-core`.
Today an inconsistent query is `Proved` vacuously; keep that behaviour where no precondition is named, so existing
callers are unaffected.

> **Amended.** Two things Z3 needs, both easy to miss:
> - `produce-unsat-cores` has to be set before the first assertion of the solver process. A `Session` reuses one
>   process across queries, so set it when the session starts, not in the query that names a precondition.
> - Z3's core is not minimal by default. Set `smt.core.minimize` to true, so that the acceptance test ("two named
>   expectations … report `Infeasible` naming both") does not depend on which core Z3 happens to find. Say in the
>   comments that the core is minimal as Z3 minimizes it, not smallest.

**A6. Objectives.** A query may ask for the least or greatest value of one term subject to its preconditions:
`Optimum(value)`, `Unbounded`, or `Infeasible(core)`, unsigned or signed as asked. MLIR's `smt` dialect has no
objective, so append Z3's `minimize`/`maximize` to the exported SMT-LIB and say so in `Outcome.smtlib`. If that
proves unreliable, an acceptable fallback is extending `ValuesSpec` to enumerate an input within stated bounds.

> **Amended.** Z3's `minimize` and `maximize` order bitvectors as unsigned. For a signed objective, optimize the
> term with its sign bit flipped (xor with the minimum signed value of its width), and flip the answer back; as
> written, a signed query would be given unsigned bounds with no error. Add a test whose signed and unsigned optima
> differ (a term that may be negative). A bitvector objective is always bounded, so say in the comments when
> `Unbounded` can be the answer, or leave it out.
>
> Where the preconditions are inconsistent, get the core from a plain check first, then run the objective only
> when they are satisfiable: the two need not share one solver call.

**Acceptance for Slice A.** Write the fixture dialect in the test, not in the library: a step function over
`(phase, level, since, clock)` as `i32`, with durations and messages as inputs, unrolled by hand in the function
body for six messages. Then:

- with `I = 10`, `E = 30`, and the phase after `on` and 65 time units constrained to re-escalation 2, the objectives
  give `R` least 13 and greatest 25: escalation is entered at 10, re-escalation 1 at 40, re-escalation 2 at
  `40 + R` and re-escalation 3 at `40 + 2R`, so `40 + R ≤ 65 < 40 + 2R`;
- two named expectations that cannot both hold report `Infeasible` naming both;
- an addition that only satisfies its property by wrapping is excluded when the overflow guard is given, and found
  when it is not;
- every outcome's `smtlib` reproduces the answer when run through `z3` by hand.

> **Amended.** For the last point, the exported text must carry everything the answer depended on: the
> `produce-unsat-cores` and `smt.core.minimize` options, the assertion names, the `minimize`/`maximize` line with
> any sign flip, and `get-unsat-core` or `get-objectives` after `check-sat`. (The arithmetic of the first point was
> checked on review: `R` is 13 to 25.)

## Slice B: bounded model checking

**B1. Calls inlined.** Lowering of `func.call` to a non-recursive function of the same module, inlined at each call,
so a step function is written once and an unrolled function calls it K times. Reject recursion and calls to unknown
symbols with a diagnostic.

> **Amended.** Do not write an inliner. Run MLIR's own `inline` pass over the module before lowering
> (`run_passes("builtin.module(inline)")`; checked on LLVM 23.1.5, it inlines a `func.call` to a private function
> of the module). A call it cannot inline (recursion, a declaration with no body) is left in place, and the
> lowering then rejects it by name as it rejects any unsupported operation today. Add a fixture for each of those
> two, checking the diagnostic names the call and its location.

**B2. Incremental scopes.** A public scope on `Session`: `push()`, `assert(formula)`, `check()`, `pop()`, sharing
inputs declared once, so Closer can deepen K from 1 upward and ask one question per claim without re-lowering or
restarting Z3. Preserve the existing per-query isolation for `Query` and `Batch`.

**B3. Witness sequences.** Counterexamples for functions with many inputs, reported in argument order, as today;
confirm that 200 inputs of width 3 and 32 report correctly and within the timeout.

**Acceptance for Slice B.** With the Slice A fixture's step function called K = 12 times on symbolic messages: the
property "the phase never equals auto-disconnect" for the alarm kind is `Proved`; with the step function's alarm
branch altered to enter auto-disconnect on a disconnect, it is a `Counterexample` whose message inputs contain a
disconnect after an on. Deepening K = 1…12 in one session gives the same answers as fresh queries.

## Slice C: SPMD overflow under the check policy

Closer runs its SPMD code (`closer_exports/frame/spmd.rhm`) with `PILLE_UB_POLICY=suppress`, because under `check`
an overflow check on varying integer arithmetic yields a vector of booleans where one is expected. Make `check` work
on `Varying(Int(N))` arithmetic (panic if any active lane overflows, naming the operation), with a test in
`pille/pille/tests/spmd/`. Closer would then move its exhaustive enumeration of message sequences onto an SPMD gang,
one sequence a program instance, which already needs nothing else (`par_for`, varying `div`/`mod`, pointer gather
and scatter all work there today).

> **Amended.** Find the failure before sizing this: it was not located on review, and "small" is unconfirmed.
> Pille's checked arithmetic already handles a plain `Simd` value (`pille-lib/pille/private/int.rhm`, `$add` and its
> siblings: the overflow flags of the lanes are reduced with `any()`), so the gap is in how `pille-spmd-lib`'s
> `Varying` reaches it. Whatever the fix, only **active** lanes may count: an inactive lane holds whatever was
> there, and counting it gives a panic for an overflow no program instance had. Test both ways: an overflow in an
> active lane panics, and one in a masked-off lane does not.

## What stays in Closer

Encoding the machine from its Rhombus and Redex definitions, holding that encoding to the Redex model by sampling,
turning a page's `- phase:` rows into named preconditions, and showing admissible durations, conflicts and
counterexample sequences in the editor (counterexamples are replayed through the Redex stepper). None of this
belongs in Pille.

## Deliverables

- **Amended.** The primitives above, described in `pille/mlir/smt.rhm`'s comments and in a dated note under
  `claude-changes/`. Do not edit `pille-mlir-lib/README.md`, the repository README, or anything under
  `pille/pille/scribblings/`: `CLAUDE.md` keeps the documentation human-written. Instead, name in the note and in
  the report each binding added or changed and what the README's "Verifying properties" section should say of it.
- Tests under `pille-mlir-lib/pille/mlir/tests/`: builder tests, lowering fixtures for `cmpi`, `select`, several
  results and `call`, and the Slice A and B acceptance fixtures as integration tests against Z3.
- A short note in `SMT_WORK_ORDER.md`'s "First supported fragment" saying what is now supported.
- Each slice in its own commits, with the full Pille test suite passing. **Amended:** "passing" is judged on a
  Racket snapshot, as CI runs it (`.github/workflows/test.yml`). On the Racket 9.3 release the seven checks of
  `pille/pille/tests/rhombus_callback.rhm` fail whatever is changed, since that Racket cannot call back into
  Rhombus; they are not this order's to fix.

## Amendments of 2026-11-20

1. The branch is `main`, not `mlir`; no feature branches; start from `7659c9e` or later.
2. Documentation is comments and a `claude-changes` note; READMEs and the manual are not edited.
3. A4: widen with `concat`, `extract` and `repeat`, the dialect having no extend; multiplication at twice the width.
4. A5: `produce-unsat-cores` at session start; `smt.core.minimize` on.
5. A6: a signed objective needs its sign bit flipped; the core first, then the objective.
6. Slice A's last acceptance point: what the exported SMT-LIB must carry.
7. B1: MLIR's `inline` pass before lowering, not a new inliner.
8. Slice C: locate the failure first; count active lanes only.
9. "Passing" means on a Racket snapshot; the callback checks cannot pass on 9.3.

This file was written into the repository from photographs of the order as it stood on the Windows checkout, where
it had not been committed. If the two differ beyond the amendments, the wording there is the original.
