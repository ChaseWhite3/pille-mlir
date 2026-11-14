# Work order: many SMT questions at the cost of one

Make `pille/mlir`'s SMT queries fast when a caller asks many of them. Today every
question starts four processes. The goal is that a batch of N questions costs one
lowering and one solver run, and that a caller can keep one solver open and ask
it questions as they come.

Work in `/Users/chasewhite/gitStuff/pille`, branch `mlir`. Do not push.
Read the repository's `CLAUDE.md` first. It forbids editing the Scribble docs
under `pille/pille/scribblings/` and the README. Where your change should be
documented there, say so in your report and in the commit message instead.
`pille-mlir-lib/SMT_WORK_ORDER.md` is the order that built what you are
extending; its constraints still hold unless this order changes them.

## Who needs this, and why

Closer (`~/Documents/gitStuff/anote-java-clojure`, branch `rhombus-model`)
judges what a page's steps guarantee by asking Z3, through this package, whether
a declared function gives a value for every input its preconditions allow
(`closer-exports/closer_exports/mlir/strengths.rhm`). One example project asks
449 such questions, and they take about 41 seconds. The questions themselves are
trivial: the time goes in process starts.

Measured on 2026-11-12 (Racket 9.3, LLVM/MLIR 23.1 at `/opt/homebrew/opt/llvm`,
Z3 at `/opt/homebrew/bin/z3`), one question:

| Step | What runs | Time |
| --- | --- | --- |
| `Dialect.module(source)` | one `mlir-opt` (verify against IRDL) | ~23 ms, once per module |
| `smt_query(...)` | `mlir-opt` with the plugin (lowers the **whole** module), `mlir-opt` again (stock verify), `mlir-translate` (export) | ~65 ms per question |
| `Query.check()` | one `z3` process | ~14 ms per question |

The size of the module hardly matters (1, 50 and 400 functions all cost about
the same), so nearly all of it is process start and process I/O.

**Target:** a batch of 1000 questions over one module in under 1 second
end to end, and under 0.5 ms per question asked of an open session. The Closer
project above should go from 41 s to under 1 s.

## Required result

### A. Batches

Add a batch query that lowers and solves many questions together.

- `dialect.smt_batch(module, specs, ~plugin)` returns a `Batch`. Each spec is
  what `smt_query` takes today: `~function`, `~inputs`, `~property`,
  `~preconditions`. Validate each spec exactly as `smt_query` does, and name
  the spec's index in any error.
- One `mlir-opt` run lowers every spec, with a manifest that lists them all
  (manifest version 2; keep version 1 readable). The plugin must lower each
  selected function once even when several specs use it.
- The result is one verified SMT dialect module that asks every question in
  order. Each question must be isolated, with `smt.push`/`smt.pop` or one
  `smt.solver` per question, so one question's declarations and assertions
  cannot leak into another's. Choose after checking what MLIR 23.1's
  `mlir-translate --export-smtlib` actually emits for each option, and record
  the evidence in your report.
- `Batch.check(~timeout, ~solver, ~arguments)` runs **one** solver process and
  returns a `List.of(Outcome)` in spec order, with the same classes and meaning
  as today (`Proved`, `Counterexample`, `Unknown`, `Timeout`, `Failure`). Only
  `unsat` proves. Each `Counterexample` has its own question's assignments.
- Timeouts: a per-question bound (for example SMT-LIB
  `(set-option :timeout …)` before each check) and an overall bound on the
  process. A question that times out is that question's `Timeout`. Where the
  solver output cannot be attributed to a question, the batch fails with
  diagnostics naming the first question it could not read.
- `Batch.to_smtlib()` gives the exact script. Each question's own SMT-LIB text
  stays available, so a single question can be reproduced alone.
- A batch of one must give the same `Outcome` as `smt_query(...).check()` for
  every outcome class.

### B. A session

Add `smt.Session`, one solver process kept open (`z3 -in`) that answers
questions as they come.

- `Session(~solver, ~arguments)`, `session.check(query_or_batch, ~timeout)`
  and `session.close()`. It must also close when its custodian is shut down.
- Every question is asked inside its own push/pop scope, so the session's
  state after a question is what it was before.
- A timeout kills and restarts the process, and the question gets `Timeout`.
  The next question must work.
- Communication is line-based and robust: match each answer to its question,
  for example with `(echo "…")` markers, and turn any unexpected output into a
  `Failure` with diagnostics.
- A session is not safe to use from several threads at once. Say so, or guard
  it.

### C. The values a result can take

Add a question that returns every value the selected function's result can
take under the preconditions. This turns "is the result always v?" for each
candidate v into a single question.

- `session.values(query_spec, ~limit)` returns `Values(values :: List.of(Int),
  complete :: Boolean)`. Enumerate by `check-sat`, `get-value` and asserting
  the value excluded, inside one push/pop scope, until `unsat` or `~limit`
  values are found.
- A result always equal to v is exactly `Values([v], #true)`. No values at all
  (`Values([], #true)`) means the preconditions are inconsistent; report that,
  and never read it as a proof.
- Test it against brute force over all `i8` inputs.

### D. Optional, after A to C pass: Z3 in-process

A backend for `Session` that calls Z3's C API through the Racket FFI
(`/opt/homebrew/opt/z3/lib/libz3.dylib`), with the same interface and outcomes.
Do it only if A to C pass and a session still costs more than about 0.5 ms a
question. Keep the process backend as the default, and make the choice
explicit. Do not move MLIR in-process: with batches, lowering is a cost per
batch, not per question.

### E. Optional: an on-disk cache

An opt-in cache of outcomes, keyed by sha256 of the exact SMT-LIB text, the
solver's version and its arguments, in a directory the caller names. It is off
by default. A cached `Counterexample` must carry its assignments.

## Constraints

- An outcome means what it means today. Nothing may turn a `sat` or an
  `unknown` into a proof, or quietly fall back to another solver or path.
- Results are deterministic and in spec order.
- Do not build a global registry keyed by operation name. The supplied
  dialect selects the model.
- Importing these modules must still work without MLIR or Z3 installed.
- Clean up temporary files and child processes on success, failure, timeout and
  custodian shutdown. Paths containing spaces must work.
- The existing package tests must still pass, and `smt_query` and `Query`
  keep their behaviour.

## Acceptance tests

1. Batch fidelity: over several hundred generated questions mixing `Proved`,
   `Counterexample` (with values) and preconditions, a batch gives exactly
   what each question gives alone.
2. Isolation: questions whose declarations share names, and one whose
   preconditions are inconsistent, do not affect the questions after them.
3. Timeouts: one question in a batch that times out (use a deliberately hard
   question, or a fake solver) is `Timeout`, and the rest are answered. A
   session restarts after a timeout and answers the next question.
4. Failures: missing executable, nonzero exit, malformed output, an output
   short of answers and bad model data each give a `Failure` with diagnostics,
   in a batch and in a session. Fake executables are fine for these.
5. Values: `session.values` agrees with brute force over every `i8` input on
   generated functions, including inconsistent preconditions and `~limit`
   reached (`complete` false).
6. Benchmark: `pille/mlir/examples/bench-batch.rhm` prints per-question time
   for N = 1, 10, 100 and 1000 questions over one module, asked one at a time
   (today's path), as a batch, and of a session. Report the numbers. The
   targets above are the bar.
7. A Closer-shaped case. Use a dialect with
   `leave(before, state) -> after`, meaning `after = state`, and
   `is`/`both`/`either`/`none` over 0 and 1 built with `schema.if_equal`
   (Closer's `strength_dialect`). Build 500 chains of up to 30 `leave`s, and for
   each ask "result == v" for every v of an 8-value domain, under
   preconditions "start is one of the 8". Time it batched, and as a session
   using `values`.

## Commands

```sh
cd /Users/chasewhite/gitStuff/pille
export PLTCOLLECTS="$PWD/pille-mlir-lib:${PLTCOLLECTS:-}"
export PILLE_MLIR_PREFIX=/opt/homebrew/opt/llvm
raco test pille-mlir-lib/pille/mlir/tests
racket pille-mlir-lib/pille/mlir/examples/bench-batch.rhm
```

The query plugin must be rebuilt after changing
`pille/mlir/native/smt-query-plugin.cpp`: `smt.build_plugin(DIR)` builds it
against the toolchain's own MLIR installation.

## Report

List:
- the files changed;
- the commands you ran and their results;
- which isolation you chose and the `mlir-translate` evidence for it;
- the benchmark table;
- anything left unsupported;
- each change the human-written docs should get, naming the binding and what
  changed.

Commit on `mlir` with short imperative subjects, and do not push.
