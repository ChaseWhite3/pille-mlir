# The SMT lowering is Rhombus; the native plugin is gone (2026-11-14)

Notes on API changed by Claude, kept apart from the human-written docs. The
package guides (`pille-mlir-lib/README.md`, `pille-mlir-lib/DECLARATIONS.md`)
still describe the plugin; the passages to change are listed at the end.

Source: the work order "one SMT lowering, in Rhombus, and no native plugin".
Its acceptance record is `pille-mlir-lib/acceptance/2026-11-14-smt-lowering/`.

## What changed for callers of `pille/mlir`

`Dialect.smt_query`, `smt_batch`, `smt_values_batch` and `smt_values_query`
need only the stock `mlir-opt` and `mlir-translate` of the toolchain. Nothing
is built, and nothing is loaded into `mlir-opt`.

Removed:

- the `~plugin:` argument of those four methods;
- `smt.build_plugin(directory, ~toolchain: chain)`;
- the environment variable `PILLE_MLIR_SMT_PLUGIN`;
- `pille-mlir-lib/pille/mlir/native/` (`smt-query-plugin.cpp`, `CMakeLists.txt`)
  and `PilleSmtQuery.so`.

A call that still passes `~plugin:` is an error at expansion (no such keyword
argument). Delete the argument.

Unchanged: the term language, how a question is encoded, the SMT-LIB a solver
sees (still written by `mlir-translate --export-smtlib`), `Toolchain`'s
`~dialect_plugins:` and `~pass_plugins:`, and the example lowering plugin under
`pille/mlir/examples/`.

## What a refusal looks like now

A lowering refusal used to arrive as `mlir-opt failed:` followed by the pass's
diagnostic and a source excerpt. It is now

```
pille/mlir: SMT lowering failed:
<stdin>:4:10: error: SMT query: unsupported operation 'arith.addi'; only …
```

The diagnostic line (location, `error:`, message) is the same text as before.
The excerpt under it is gone; it showed a line of the reprinted module, not of
the source the location names.

Two messages differ from the plugin's:

- Malformed manifest JSON: `malformed SMT query manifest: ` is followed by
  Racket's JSON reader's words, where it was LLVM's. Only hand-written
  manifests reach this.
- A hand-written manifest that models a *registered* operation with memory
  effects (for example `memref.alloca`) was refused for "known memory effects".
  A module's text does not say which operations have effects, so such an
  operation is now refused by the next check that applies to it (its
  attributes, operands or result). No operation a dialect declares has effects,
  so manifests made from a `Dialect` never reach this.

## Where it lives

- `pille/private/mlir/generic.rhm`: reads the generic form `mlir-opt` prints
  (`--mlir-print-op-generic --mlir-print-local-scope --mlir-print-debuginfo`).
  A closed grammar; anything else is refused with line and column.
- `pille/private/mlir/lower.rhm`: the lowering (`lower`, `lower_text`), a port
  of the plugin over the same manifest (versions 1 and 2).
- `pille/private/mlir/tools.rkt`: `module_generic` asks the toolchain for a
  module's generic form, once per module.
- `pille/private/mlir/query.rkt`: `smt_lower_text` lowers a manifest given as
  JSON text, for tests of what the lowering itself checks.
- `pille/mlir/tests/smt-lowering.rkt` holds the lowering to what the plugin
  made of 774 requests, recorded before the plugin was removed
  (`tests/fixtures/smt-lowering/plugin-recorded.json.gz`; never regenerate it).

## Passages the human-written guides should change

`pille-mlir-lib/README.md`:

- the requirements table row "The `PilleSmtQuery` plugin, built with CMake and
  a C++17 compiler …": no longer a requirement;
- the section "Building the query plugin": remove; say instead that queries are
  lowered in Rhombus from the module's generic form and need only the stock
  tools;
- under "Queries": the signature `dialect.smt_query(…, ~plugin: path)` loses
  `~plugin: path`; the table row for `smt.build_plugin` goes; "The SMT module
  is produced by the pass" becomes "by the lowering";
- under the commands: the lines that build and select the plugin before
  `examples/verify.rhm`;
- the tests table: `smt-integration.rkt`, `smt-api.rhm` need MLIR and Z3 only;
  add `smt-batch.rhm` (MLIR and Z3) and `smt-lowering.rkt` (MLIR only); the
  paragraph "The SMT tests use `PILLE_MLIR_SMT_PLUGIN` if it is set …" goes.

`pille-mlir-lib/DECLARATIONS.md`:

- the `.smt_query(…, ~plugin: path)` row loses `~plugin: path`;
- "they and `examples/verify.rhm` need the query plugin and Z3" becomes "need
  Z3".

The Scribble manual under `pille/pille/scribblings/` does not mention any of
this.
