# One SMT lowering, in Rhombus, and no native plugin: acceptance record

2026-11-14, macOS (Darwin 25.6), Racket 9.3, Homebrew LLVM/MLIR 23.1.5 at
`/opt/homebrew/opt/llvm`, Z3 on the PATH.

The native pass plugin (`pille/mlir/native/smt-query-plugin.cpp`) is replaced by
`pille/private/mlir/lower.rhm`, which reads the verified module through
`pille/private/mlir/generic.rhm`. Both were run on the same requests before the
plugin was deleted. This folder holds what was compared, the scripts as they
were run, and their results.

Commits: `b977ff9` adds the lowering beside the plugin, with two temporary
switches for the comparison (`PILLE_MLIR_SMT_COMPARE=DIR`,
`PILLE_MLIR_SMT_LOWERING=plugin`). The next commit deletes the plugin and both
switches. To rerun any comparison here, check out `b977ff9`.

## B. What `mlir-opt` 23.1 prints in the generic form

Command, as `tools.rkt` `module_generic` runs it (the module on standard input):

```
mlir-opt --irdl-file=DIALECT.mlir --verify-each --mlir-print-op-generic \
         --mlir-print-local-scope --mlir-print-debuginfo
```

For one of Closer's strength modules (`generic-form/strength-module.mlir`, its
dialect `strength-dialect.irdl.mlir`), the whole output is
`generic-form/strength-module.generic.mlir`. Its first lines:

```
"builtin.module"() ({
  "func.func"() <{function_type = (i8, i8, i8) -> i8, sym_name = "derived_0"}> ({
  ^bb0(%arg0: i8 loc("<stdin>":2:24), %arg1: i8 loc("<stdin>":2:33), %arg2: i8 loc("<stdin>":2:42)):
    %0 = "closer_strengths.none"(%arg1) : (i8) -> i8 loc("<stdin>":3:11)
    %1 = "arith.constant"() <{value = 1 : i8}> : () -> i8 loc("<stdin>":4:11)
    %2 = "closer_strengths.leave"(%arg2, %1) : (i8, i8) -> i8 loc("<stdin>":5:11)
    …
    "func.return"(%22) : (i8) -> () loc("<stdin>":26:5)
  }) : () -> () loc("<stdin>":2:3)
}) : () -> () loc("<stdin>":1:1)
```

This is the shape the work order sketched. What the sketch did not show, each
seen in `generic-form/shapes-module.generic.mlir`:

- The module is itself an operation: `"builtin.module"() ({ … }) : () -> ()`.
- Inherent attributes are in `<{…}>` after the operands; other attributes are
  in `{…}` after the regions (`}) {pille.note = "x"} : () -> ()`).
  `sym_visibility = "private"` is inherent; so is `arith.addi`'s
  `overflowFlags` and `memref.alloca`'s `operandSegmentSizes`.
- A declaration is a `func.func` with an empty region: `({\n  })`.
- An `i1` constant prints `value = true`; others print the type after the
  digits, `-1 : i64` included; negative values print signed.
- A block after the first has its label and a comment: `^bb1:  // pred: ^bb0`.
  Successors are `"cf.br"()[^bb1]`.
- SSA names are numbered over the whole module (`%arg4`, `%6`), not per
  function. The reader keeps them as text.
- `--mlir-print-local-scope` puts every location in place (`loc("<stdin>":3:11)`)
  and prints no alias table. I added it and `--mlir-print-debuginfo` to the
  flag the order names, so that a refusal is reported at the source position
  the plugin reported and each SMT operation carries the location the plugin
  gave it.

The lowering's own output for that module is
`generic-form/strength-lowered.generic.mlir`. After the stock `mlir-opt` it has
the same operations as the plugin's (`strength-plugin-lowered.mlir`), and its
exported SMT-LIB is the same bytes (`strength-plugin.smt2`).

## E1 and E4. Same answers, same text

`query.rkt` at `b977ff9` ran both lowerings on every request and recorded both
results. `tools/compare.py` compares the records: refusal messages, the
verified MLIR text, the exported SMT-LIB (whole, per question, and per question
after normalizing names and `let`), and, with `--solve`, Z3's status on both
sides, each counterexample pinned into the other side's question, and the
value set of every values question by enumeration.

| Requests from | Requests | Lowered by both | Refused by both | Questions | Verified MLIR equal | SMT-LIB equal (bytes) | Proof statuses equal | Counterexamples cross-checked | Value sets equal |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| every test in `pille/mlir/tests` (`results/e1-pille-tests.json`) | 666 (655 distinct) | 627 | 38 | 933 (922 proof, 11 values) | 627 of 627 | 933 of 933 | 913 of 913 (334 sat, 579 unsat) | 668 of 668 | 11 of 11 |
| a sweep of every refusal a manifest or a verified module can reach (`tools/refusals.rkt`, `results/e1-refusals.json`) | 114 | 26 | 88 | 26 (23 proof, 3 values) | 26 of 26 | 26 of 26 | 23 of 23 (10 sat, 12 unsat, 1 solver error on both) | 20 of 20 | 3 of 3 |
| a module whose unselected operations are awkward to pass over (`tools/skipped.rkt`, `results/e1-skipped.json`) | 5 | 1 | 4 | 1 | 1 of 1 | 1 of 1 | 1 of 1 | — | — |

Statuses are counted once per distinct request. The one solver error is a
deliberately invalid input name (`weird "name" \ here`) that only a hand-written
manifest can carry; both lowerings write it identically.

**E4 has no finding:** not one question differs, before normalization or after.

**Refusals: every one the plugin's tests expect, the lowering gives with the
same message.** Over all three sets, 130 requests were refused by both; 127
carry the same message (97 distinct messages). The differences, all of them:

1. `{not json` (twice, once from the tests and once from the sweep).
   Plugin: `malformed SMT query manifest: [1:2, byte=2]: Expected object key`.
   Lowering: `malformed SMT query manifest: string::2: string->jsexpr: non-string value used for json object key`.
   The prefix is shared; what follows is each JSON reader's own words. Only a
   hand-written manifest reaches it. The test matches the prefix.
2. A hand-written manifest that models `memref.alloca` (sweep).
   Plugin: `operation 'memref.alloca' has known memory effects, which the pure SMT model cannot represent`.
   Lowering: `operation 'memref.alloca' carries attribute 'operandSegmentSizes'; …`.
   The plugin asks MLIR whether a registered operation has effects. A module's
   text does not say, so the lowering refuses such an operation at the next
   check that applies. No operation a dialect declares through IRDL has the
   effect interface, so a manifest made from a `Dialect` cannot reach this
   branch in either lowering.

One record is neither: the test "the plugin must be selected explicitly"
deselected the plugin, so the plugin side has no lowering to compare. That test
is removed with the plugin.

Two things a native pass asks MLIR that text cannot answer, and what the
lowering does instead:

- **Is this operation a terminator?** The lowering takes "has successors, or is
  last in its block". In a verified module these are the same operations: the
  verifier requires a block to end in a terminator and a terminator to be last.
- **Does it have memory effects?** Not asked; see 2 above.

### Kept after the plugin is gone

`pille/mlir/tests/smt-lowering.rkt` replays the 774 distinct requests of the
three sets against `tests/fixtures/smt-lowering/plugin-recorded.json.gz`: the
plugin's refusal message, or the SHA-256 of its verified MLIR and of its
SMT-LIB (645 lowered, 951 questions; 129 refused). The three records above that
differ say so and why. It needs MLIR and no solver, and runs in about 30 s. The
fixture cannot be regenerated: the plugin that wrote it is deleted.

## E2. Closer's questions

`tools/e2.sh` ran ten of Closer's check files three times: with the plugin's
lowering, with the Rhombus lowering, and with both compared
(`results/e2-results.txt`).

| Check | Plugin | Rhombus |
| --- | --- | --- |
| `mlir/check.rhm` | 285 passed | 285 passed |
| `mlir/assumptions_check.rhm` | 22 | 22 |
| `checked_check.rhm` | 80 | 80 |
| `requirement_rules_check.rhm` | 26 | 26 |
| `semantics_check.rhm` | 61 | 61 |
| `run/try_check.rhm` | 25 | 25 |
| `refinement/check.rhm` | 144 | 144 |
| `role_identity_check.rhm` | 50 | 50 |
| `editor_check.rhm` | 6 | 6 |
| `neighborhood_check.rhm` | 49 | 49 |

In the compared run Closer made 1,249 lowering requests (1,000 distinct) holding
6,058 questions (867 proof, 5,191 values). Every request's verified MLIR and
SMT-LIB are byte-identical; where the plugin wrote standalone query modules
(1,232 batches) they are identical too. Solved once per distinct request: 716
proof statuses equal (423 sat, 293 unsat), 846 counterexamples cross-checked,
5,008 value sets equal. No refusals, no differences (`results/e2-closer.json`).

After the plugin was deleted and Closer patched, Closer's whole suite was run
again; its result is in the section "After D".

## E3. Same speed

`tools/e3.sh`: `examples/bench-batch.rhm` and the strengths of Closer's
`examples/rhombus-safetynet` (the 449-question project;
`tools/closer-e3.rhm`), three rounds each, alternating
(`results/e3-results.txt`). Milliseconds; three rounds each, the one-at-a-time
baseline once.

| Row | Questions | Plugin | Rhombus | Target |
| --- | --- | --- | --- | --- |
| batch, end to end | 1000 | 709, 721, 744 | 692, 688, 688 | under 1000 |
| batch, lowering only | 1000 | 126, 125, 127 | 92, 101, 100 | |
| session question | 1000 | 224, 233, 234 (0.22 to 0.23 each) | 223, 232, 233 (0.22 to 0.23 each) | under 0.5 each |
| session with lowering | 1000 | 365, 375, 377 | 339, 348, 349 | |
| batch, end to end | 100 | 133, 134, 133 | 131, 116, 119 | |
| batch, end to end | 10 | 73, 76, 76 | 65, 59, 59 | |
| batch, end to end | 1 | 66, 68, 66 | 59, 64, 69 | |
| one at a time | 1000 | 53,929 | 38,544 | |
| Closer-shaped batch, lowering only | 4000 over 500 functions | 1264, 1287, 1287 | 1292, 1298, 1304 | |
| Closer-shaped batch, end to end | 4000 | 4518, 4541, 4534 | 4516, 4541, 4593 | |
| Closer-shaped values, lowering only | 500 | 239, 238, 238 | 175, 177, 178 | |
| Closer-shaped values, end to end | 500 | 704, 697, 698 | 631, 639, 635 | |
| Closer `rhombus-safetynet`, all strengths | 449 | 110, 110, 110 | 109, 109, 129 | under 1000 |

Both targets are met by both. The Rhombus lowering is faster or level
everywhere except lowering 4,000 questions over 500 functions at once, where it
is 1 to 2 percent slower (about 15 ms in 1,300); end to end that case is level.
One at a time it is faster because a module's generic form is asked for once
and kept, so a second question over the same module costs two processes
(verify, export) where the plugin cost three.

Process count for a batch is as before: one `mlir-opt` to print (in place of
the one that ran the pass), one stock verify, one export, then the solver.

## D. What was removed

- `pille/mlir/native/` (`smt-query-plugin.cpp`, `CMakeLists.txt`).
- `tools.rkt`: `build-smt-plugin`, `resolve-smt-plugin`, `run-smt-query-pass`,
  `run-smt-batch-pass`, `quote-pass-option`, the plugin's instructions and
  source path, and `run-tool`'s `#:pass-plugins`, `#:in-directory` and
  `#:read-output`, which only they used.
- `smt.build_plugin`.
- `PILLE_MLIR_SMT_PLUGIN`.
- The `~plugin` argument of `smt_query`, `smt_batch`, `smt_values_batch` and
  `smt_values_query`, and the optional `plugin` argument of the `make_smt_…`
  builders in `query.rkt`.
- `tests/smt-support.rkt` (it built the plugin for the tests), the two tests of
  selecting a plugin, and the plugin from `examples/bench-batch.rhm`,
  `bench-batch-support.rkt` and `verify.rhm`.
- The two temporary comparison switches.

`Toolchain`'s `~dialect_plugins:` and `~pass_plugins:` and the example lowering
plugin (`examples/lower-add-plugin.cpp`) are a different feature and stay.

## After D

- `raco test pille-mlir-lib/pille/mlir/tests`, with no plugin built and
  `PILLE_MLIR_SMT_PLUGIN` unset: **3,498 tests passed**, in 73 s. (It took
  several minutes before, most of it building the plugin.)
- `raco setup --pkgs pille-mlir-lib` was not run: the package is not installed
  on this computer (the collections are found through `PLTCOLLECTS`). Every
  module, test and example was compiled from clean with `raco make` instead.
- `examples/bench-batch.rhm` again, with the plugin gone
  (`results/e3-after-d.txt`): batch of 1000 end to end 670 ms; session question
  0.24 ms; Closer-shaped batch of 4000 4,439 ms; values 639 ms.
  `examples/verify.rhm` runs.
- Closer, patched (`closer.patch`), whole suite
  (`raco test models closer-exports closer-lang/kinds.rhm`): **7,891 of 7,893**.
  The two failures are `reader/astar_serve.rhm` and `reader/tagger_serve.rhm`,
  which fail the same way before this change and ask the solver nothing.
- **Windows was not run.** There is no Windows here. What the order asks there
  (conda-forge `mlir` 23.1.5, Closer's `mlir/check.rhm`, the strength checks and
  `run/try_check.rhm`) is still to do. Nothing in the lowering is specific to
  an operating system: it starts `mlir-opt` and `mlir-translate` through
  `run-tool`, as module verification already does.

## The Closer patch

`closer.patch` (against `rhombus-model` at `83d4026f`; 18 files) removes the
`~plugin:` parameter and argument everywhere it was threaded, not only at the
six files the order names, since each of them passed it on: `strengths.rhm`,
`kripke.rhm`, `rules.rhm`, `smt.rhm`, `requirements.rhm`, `compile.rhm`,
`checked.rhm`, `checked_main.rhm`, `checked_check.rhm`, `kripke_view.rhm`,
`serve.rhm`, `bench.rhm`, `reader/pages_cli.rhm`, `mlir/survey.rhm`,
`mlir/assumptions_check.rhm` and `mlir/check.rhm`. The five `smt.build_plugin`
calls and the three places that looked for `PilleSmtQuery.so` go with it, and
two notes (`closer-exports/README.md`, `SOLVER_STRENGTHS_PLAN.md`) say so.

Closer cannot compile against this Pille without the patch (`~plugin:` is no
longer an argument), so it is applied in the Closer checkout.

## Choices worth knowing

- **The sidecar is a value.** The plugin wrote the standalone query modules to
  the path the manifest gave as `query_modules`. The lowering returns them
  beside the module, and `query.rkt` no longer writes that key. They are still
  each solver as a module of its own, verified lazily as before.
- **A refusal's wrapper changed.** It was `mlir-opt failed:` and the pass's
  diagnostic with a source excerpt; it is `SMT lowering failed:` and the same
  diagnostic line (`<stdin>:4:10: error: …`). The excerpt showed a line of the
  reprinted module rather than the source line the location names.
- **The final structural check is the writer.** The plugin's `checkResult`
  walked the module for residual operations and types. The lowering writes
  only the fifteen allowed operations and never copies a source operation, and
  the stock `mlir-opt` verifies the result with no IRDL and no plugins.
- **Nothing outside `pille-mlir-lib` changed in Pille** except one note,
  `claude-changes/2026-11-14-smt-lowering-in-rhombus.md`.

## Where the human-written documents should change

Not edited, by the repository's rule. The passages are listed in
`claude-changes/2026-11-14-smt-lowering-in-rhombus.md`: in
`pille-mlir-lib/README.md` the plugin requirement row, the section "Building
the query plugin", `~plugin: path` and `smt.build_plugin` under "Queries", the
plugin lines of the commands, and the tests table; in
`pille-mlir-lib/DECLARATIONS.md` the `.smt_query(…, ~plugin: path)` row and
"need the query plugin and Z3". The Scribble manual does not mention the
plugin.
