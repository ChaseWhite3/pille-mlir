# MLIR from Rhombus

`pille/mlir` lets a Rhombus language implementation generate MLIR, register its
own dialect through IRDL, verify programs, and run compiler passes. The package
uses `mlir-opt`, `mlir-translate`, and `llvm-as` as subprocesses; it does not load
MLIR native handles into Racket. Module values contain immutable, verified MLIR
text and retain their IRDL definitions and selected toolchain across passes.

Pille's existing frontend continues to emit LLVM directly. This package is the
MLIR entry point for a frontend that generates its own IR. It does not infer
dialect definitions or lowering rules from arbitrary Rhombus macros.

For automatic IRDL generation from Rhombus declarations, use
[`pille/mlir/dialect`](DECLARATIONS.md). Its extensible declaration and constraint
spaces expand into a validated schema, including custom types, attributes, and
operation signatures. This removes the need to maintain corresponding IRDL by
hand. The lower-level `Module(..., ~irdl: text)` API remains available.

An operation declaration can also state its SMT meaning. A program using such
operations can then be lowered to MLIR's SMT dialect, exported as SMT-LIB, and
checked with Z3; see [Verifying properties](#verifying-properties-with-declared-smt-semantics).

## Installation

Install Racket/Rhombus as described in the repository README, then:

```sh
raco pkg install pille-mlir-lib/
export PILLE_MLIR_PREFIX=/path/to/llvm-23.1
```

The implementation is tested with Racket 9.3 and LLVM/MLIR 23.1.5 on aarch64
macOS. MLIR APIs, pass names, and IRDL syntax change between releases. Other
versions and platforms have not been validated.

Required tools in the installation's `bin` directory:

| Tool | Used for |
| --- | --- |
| `mlir-opt` | Parsing, verification, runtime IRDL registration, and passes |
| `mlir-translate` | LLVM IR and SMT-LIB export |
| `llvm-as` | LLVM bitcode output |
| `llvm-dis` | Bitcode validation in the integration tests |

The build must include MLIR with the dialects and passes you use. On Homebrew,
the tested `llvm@23` installation includes these tools. No native MLIR C API
shared library is required. Importing `pille/mlir` does not invoke any tools.
Constructing a toolchain requires `mlir-opt`; other tools are required when used.

SMT verification has two further, optional requirements. Neither is needed to
import any module, expand declarations, or obtain IRDL:

| Requirement | Used for |
| --- | --- |
| The `PilleSmtQuery` plugin, built with CMake and a C++17 compiler against the same installation | `dialect.smt_query(...)` |
| Z3 (tested with 5.3.3) | `query.check(...)` |

Tool selection follows this order:

1. An explicit `mlir.Toolchain(~prefix: path)`.
2. `PILLE_MLIR_PREFIX`.
3. `PILLE_LLVM_PREFIX`.
4. `mlir-opt` on `PATH`.

An explicit or environment prefix must work; it does not silently fall back.
The selected `bin` directory is captured, and all tools are resolved there so
later environment changes do not switch an existing module's compiler.

## Standard dialects to LLVM

```rhombus
#lang rhombus/static
import:
  pille/mlir

def source = mlir.Module(@str|{
  module {
    func.func @add(%lhs: i32, %rhs: i32) -> i32 {
      %sum = arith.addi %lhs, %rhs : i32
      return %sum : i32
    }
  }
}|)

def lowered = source.run_passes(
  "builtin.module(convert-arith-to-llvm,convert-func-to-llvm,reconcile-unrealized-casts)"
)
println(lowered.to_llvm_ir())
```

Use Rhombus's `@str|{...}|` text form to keep MLIR `@symbol` names literal.
Frontends can construct these strings from their resolved declarations and
programs. This boundary accepts arbitrary registered MLIR dialects; it has no
operation-specific parser or dispatch table.

Pass pipelines use MLIR's normal anchored syntax, such as
`builtin.module(func.func(canonicalize),cse)`. Construction and every pass run
invoke the real MLIR parser/verifier. Unknown operations are rejected. Printing
normalizes formatting and SSA names and retains source locations, including
explicit `loc("source.rhm":line:column)` locations supplied by the frontend.
Implicit locations refer to `<stdin>`, the submitted text. Transformations
may change or combine locations according to each pass's semantics.

`run_passes` returns a new module; the original remains usable even when a pass
fails. MLIR diagnostics are included in raised exceptions. Lowering is explicit:
the example pipeline handles arithmetic/functions, while tensors, memory,
control flow, and GPUs need appropriate additional passes and target settings.
Relative file paths in pass options resolve against the caller's current working
directory, just as when invoking the tools directly.

## Runtime dialects through IRDL

Pass one IRDL module containing your dialect definitions to the constructor:

```rhombus
def custom = mlir.Module(program_text, ~irdl: dialect_definition_text)
def optimized = custom.run_passes("builtin.module(canonicalize)")
```

The definitions are registered using `mlir-opt --irdl-file` on every invocation.
They are retained as text rather than as a path to a temporary file. Definitions
may contain multiple dialects, operations, types, and attributes. The tests
demonstrate equal operand/result constraints, a parameterized custom type, and
a custom attribute with restricted values. Invalid inputs fail verification;
no allow-unregistered option is used.

See [examples/irdl.rhm](pille/mlir/examples/irdl.rhm) and the more complete
[IRDL fixture](pille/mlir/tests/fixtures/rhombus.irdl.mlir).

IRDL describes structure and constraints. It does not supply executable meaning,
effect analysis, optimizations, or lowering. Such behavior belongs in frontend
analysis, registered passes, or MLIR extensions. Native plugins can be supplied:

```rhombus
def toolchain = mlir.Toolchain(
  ~prefix: "/path/to/llvm-23.1",
  ~dialect_plugins: ["/path/to/dialect-plugin.so"],
  ~pass_plugins: ["/path/to/lowering-plugin.so"],
)
def custom = mlir.Module(program_text,
  ~irdl: dialect_definition_text,
  ~toolchain: toolchain)
```

Plugin paths are made absolute and retained with the toolchain. Plugins must be
built for the selected MLIR installation; they execute native code in the tool
process. Plugin options are forwarded to `mlir-opt`. Stock `mlir-translate`
does not load these plugins or IRDL definitions, so custom operations and types
must be lowered to supported dialects before LLVM or SMT-LIB export.

The optional [example pass](pille/mlir/examples/lower-add-plugin.cpp) gives
`rhombus.add` wrapping integer-addition semantics by rewriting it to `arith.addi`.
It demonstrates the complete custom dialect → standard dialect → LLVM path.
Build it with the same MLIR development installation used by the tools:

```sh
cmake -S pille-mlir-lib/pille/mlir/examples -B /tmp/pille-lower-add \
  -DMLIR_DIR="$PILLE_MLIR_PREFIX/lib/cmake/mlir" -DCMAKE_BUILD_TYPE=Release
cmake --build /tmp/pille-lower-add
PILLE_MLIR_ADD_PLUGIN=/tmp/pille-lower-add/PilleLowerAdd.so \
  racket pille-mlir-lib/pille/mlir/examples/irdl.rhm
```

These commands are for the tested Unix/macOS setup and require CMake, a C++
compiler, and the MLIR/LLVM shared development libraries. The normal package does
not require building this plugin. Without `PILLE_MLIR_ADD_PLUGIN`, the IRDL
example prints verified custom IR. With the plugin, it prints LLVM IR. This pass
handles only the example operation; a language must supply its own semantics.

## API

| Form | Result |
| --- | --- |
| `Toolchain(~prefix: path = #false, ~dialect_plugins: paths = [], ~pass_plugins: paths = [])` | Captured installation and optional plugin paths |
| `Module(source, ~irdl: definitions = "", ~toolchain: chain = Toolchain())` | Verified module |
| `module.to_ir()` | Stored MLIR text; no subprocess |
| `module.run_passes(pipeline)` | New verified module retaining definitions/toolchain |
| `module.to_llvm_ir()` | LLVM IR text; input must already be lowered |
| `module.to_bitcode()` | LLVM bitcode as `ImmutableBytes`; input must already be lowered |
| `module.to_smtlib()` | SMT-LIB text from exportable SMT operations |

The SMT verification API is listed [above](#queries).

There are no native handles to dispose. Each operation uses a private temporary
directory, invokes executables directly without a shell, and removes the
temporary files on success or failure.

## Existing LLVM backend

`lowered.to_bitcode()` can be passed to the existing
`llvm.Module.from_bitcode(context, bytes)` from `pille/llvm`. Use matching LLVM
versions for the producer tools and the native LLVM consumer; this package does
not check the consumer's version. The resulting LLVM module has the usual native
lifetime rules. Target triples, data layouts, ABI decisions, and memory
management remain the frontend/backend's responsibility.

The umbrella package's [bridge test](../pille/pille/tests/mlir.rhm) exercises
this boundary, verifies the native module, and compiles and runs integer addition
through Pille's existing LLVM object/ORC APIs.

## SMT dialect export

[examples/smt.rhm](pille/mlir/examples/smt.rhm) is the low-level entry point. It
writes an SMT dialect query by hand, asking whether 32-bit wrapping addition
violates `x + 0 == x`, and exports SMT-LIB:

```sh
racket pille-mlir-lib/pille/mlir/examples/smt.rhm
# If Z3 is installed:
racket pille-mlir-lib/pille/mlir/examples/smt.rhm | z3 -in
```

The second command returns `unsat` for the example. `Module.to_smtlib()` only
exports; it never runs a solver.

## Verifying properties with declared SMT semantics

A dialect author can declare an operation's structure and its SMT meaning in
one place, and then check properties of ordinary programs that use it:

```text
Rhombus operation declaration with an smt: clause
    -> expansion validates and records the schema and the semantic model
    -> IRDL registers the operation and verifies each instance's structure
    -> dialect.smt_query lowers a function and a property to the SMT dialect
    -> query.to_smtlib() exports SMT-LIB with the existing exporter
    -> query.check() runs Z3: proved, counterexample, or inconclusive
```

```rhombus
#lang rhombus/static/and_meta
import:
  pille/mlir/dialect open
  pille/mlir/smt

constraint Integer:
  same("T", i32 || i64)

dialect arithmetic("arithmetic"):
  operation add(lhs: Integer, rhs: Integer) -> (sum: Integer):
    smt:
      sum = bv.add(lhs, rhs)
  operation sub(lhs: Integer, rhs: Integer) -> (difference: Integer):
    smt:
      difference = bv.sub(lhs, rhs)

def program = arithmetic.module(@str|{
  module {
    func.func @round_trip(%x: i32, %y: i32) -> i32 {
      %sum = "arithmetic.add"(%x, %y) : (i32, i32) -> i32
      %difference = "arithmetic.sub"(%sum, %y) : (i32, i32) -> i32
      return %difference : i32
    }
  }
}|)

def x = smt.input("x", ~width: 32)
def y = smt.input("y", ~width: 32)
def result = smt.result(~width: 32)

def query = arithmetic.smt_query(program,
                                 ~function: "round_trip",
                                 ~inputs: [x, y],
                                 ~property: smt.eq(result, x))
println(query.to_smtlib())           // export only
println(query.check().describe())    // runs Z3
```

[examples/verify.rhm](pille/mlir/examples/verify.rhm) is the complete runnable
version: it proves this property and reports a counterexample to a false one.
It contains no handwritten SMT MLIR or SMT-LIB. The `smt:` clause and its
expression forms are described in the
[declaration guide](DECLARATIONS.md#smt-semantics).

### What a proof means

IRDL verification is structural: it checks that each instance has the declared
operands, results, attributes, and types. It says nothing about what an
operation computes. The `smt:` clause supplies a mathematical model, and a
`Proved` outcome means that the property holds *for that model*, for the
selected function, under the stated preconditions.

Attaching semantics declares the operation pure, deterministic, and total. IRDL
cannot establish this, and a dynamically registered operation has no MLIR effect
interfaces, so the declaration is trusted: an operation is not rejected for
lacking those interfaces, an operation without a model is never assumed pure,
and an operation that reports memory effects is rejected. A proof also does not
establish that an independent lowering, such as the example `rhombus.add` to
`arith.addi` pass, implements the same model.

### Supported fragment

| Aspect | Supported |
| --- | --- |
| Types | Signless `i1`, `i8`, `i16`, `i32`, `i64` |
| Type mapping | `iN` becomes `!smt.bv<N>` of exactly the same width; SMT-LIB `(_ BitVec N)` |
| Modeled operations | Fixed arity, exactly one result, no attributes, regions, or successors |
| Requirements | `requires a == b \|\| ...` in a model; each use's requirement is proved along with the property, so a counterexample may be a use outside what an operation's model covers. Ask the property `smt.eq(result, result)` to check the requirements alone |
| Semantic expressions | Operand and local references, literals, wrapping `bv.add`, `bv.sub`, `bv.mul`, and the choice `bv.if(a == b, then, else)` |
| Functions | `func.func` with one block, typed arguments, `arith.constant`, modeled operations, and `return` of one value |
| Properties | Inputs, the result, typed literals, `add`/`sub`/`mul`, and `eq`, `not`, `and`, `or` |
| Logic | `QF_BV` |

A declaration may accept several widths; its model is instantiated at each
instance's actual types. Widths are never converted, and are never assumed
equal: an instance that mixes widths where the model needs equal ones is
rejected while lowering. `bv.sub(a, b)` is emitted as `a + (-b)`, which is
exactly wrapping subtraction (the SMT dialect has no subtraction operation).
`bv.if(a == b, then, else)` is emitted as `smt.ite` over `smt.eq`. A comparison
is written only there, as the test of a choice; it is not a value of the
meaning language.

`i1` is a one-bit bitvector. Predicates are SMT Booleans (`!smt.bool`), a
separate sort produced only by `smt.eq`; a one-bit term cannot be used as a
predicate, and predicates cannot be compared with `smt.eq`. There are no signed
or unsigned comparisons, no unbounded integers, and no overflow flags.

A literal for width *w* must lie in [-2^(w-1), 2^w - 1], the range MLIR accepts
for an `iN` constant. A negative literal denotes its two's complement residue,
so `-1` and `0xffffffff` are the same 32-bit value. Anything outside the range
is an error; nothing is truncated.

Everything else fails with a diagnostic, before any solver runs: other
operations (including standard ones such as `arith.addi`), operations without a
model, other types (`index`, floats, other widths, custom types), control flow,
calls, memory operations, regions, multiple results, declarations without a
body, and unused values outside the fragment. Attributes are rejected rather
than ignored, because the model cannot observe them: any attribute on a modeled
operation instance, any attribute on `arith.constant` other than `value`, and
any function attribute other than `sym_name`, `function_type`, and
`sym_visibility`. Declaring `attributes(...)` together with `smt:` is an
expansion error for the same reason. Functions other than the selected one are
not part of the query and are not inspected.

### Building the query plugin

Lowering is done by one native pass that reads a declarative manifest generated
from the `Dialect` value. It contains no operation names: a new or renamed
operation, another namespace, or a different model needs no native changes and
no rebuild. Build it once, with the same installation that supplies `mlir-opt`:

```sh
cmake -S pille-mlir-lib/pille/mlir/native -B /tmp/pille-smt-query \
  -DMLIR_DIR="$PILLE_MLIR_PREFIX/lib/cmake/mlir" -DCMAKE_BUILD_TYPE=Release
cmake --build /tmp/pille-smt-query
export PILLE_MLIR_SMT_PLUGIN=/tmp/pille-smt-query/PilleSmtQuery.so
```

This requires CMake 3.20 or later, a C++17 compiler, and the MLIR/LLVM shared
development libraries (`libMLIR`, `libLLVM`), as for the example plugin above.
`smt.build_plugin(directory, ~toolchain: chain)` runs the same two commands
against the toolchain's own installation and returns the plugin's path. The
plugin is never built or searched for implicitly. `smt_query` uses, in order,
its `~plugin:` argument and then `PILLE_MLIR_SMT_PLUGIN`; a selection that does
not exist is an error.

### Queries

`dialect.smt_query(module, ~function: name, ~inputs: [...], ~property: formula,
~preconditions: [...], ~plugin: path)` returns an immutable `smt.Query`.

- The module must have been verified against this dialect's generated IRDL, as
  `dialect.module(...)` does. A module holds only MLIR and IRDL text, so the
  semantic model always comes from the `Dialect` value passed here. Identical
  IRDL can carry different meanings, and there is no registry of operation
  names: two dialect values with the same namespace and operation names are
  independent.
- The function is selected by symbol name. `~inputs` lists one `smt.input` per
  argument, in argument order; position is the identity, and the name is only
  how counterexamples are reported. Printed SSA names are never consulted.
  `smt.result` denotes the returned value. Widths are checked against the
  function's actual types.
- Input names become SMT-LIB symbols verbatim, so they must be identifiers
  (`[A-Za-z_][A-Za-z0-9_]*`) that are not reserved by SMT-LIB or its bitvector
  theory.
- The query asserts each precondition and the negation of the property, then
  checks satisfiability. No other assumption is added.

| Form | Result |
| --- | --- |
| `smt.input(name, ~width: n)`, `smt.result(~width: n)`, `smt.const(value, ~width: n)` | A bitvector `smt.Term` |
| `smt.add(a, b)`, `smt.sub(a, b)`, `smt.mul(a, b)` | Wrapping arithmetic on terms of equal width |
| `smt.eq(a, b)` | An `smt.Formula`: equality of two terms of equal width |
| `smt.not(p)`, `smt.and(p, ...)`, `smt.or(p, ...)` | Formulas over formulas |
| `query.module` | The verified SMT dialect `mlir.Module`; it contains no custom operations |
| `query.to_smtlib()` | The SMT-LIB text, from the existing exporter; no solver runs |
| `query.function`, `.dialect`, `.inputs`, `.property`, `.assumptions` | What the query asks, as data and text |
| `query.check(~solver: path = #false, ~timeout: seconds = 10, ~arguments: [])` | An `smt.Outcome` from running the solver |
| `smt.build_plugin(directory, ~toolchain: chain)` | Path of a freshly built plugin |

The SMT module is produced by the pass and then verified again by stock
`mlir-opt` with no IRDL definitions and no plugins, which is exactly what
`mlir-translate` accepts. A residual custom operation would fail there.

### Running a solver

`query.check()` is the only operation that starts a solver. The solver is the
`~solver:` argument if given, else `PILLE_Z3`, else `z3` on `PATH`; an explicit
or environment selection that does not exist is a failure, not a fallback. It
is run directly, without a shell, as `solver [arguments...] query.smt2` in a
private temporary directory that is removed afterwards. `~timeout:` is a
required finite bound in seconds, 10 by default. When it elapses the solver's
process group is terminated, as it is if the calling thread is interrupted.

The exported text is run unchanged. If the answer is `sat`, the solver is run
once more on the same commands through `(check-sat)` followed by the standard
`(get-value (...))` for the inputs, because the exported script ends with
`(reset)` and `get-value` is only legal after `sat`. Both runs share the bound.

| Outcome | Solver result | Meaning |
| --- | --- | --- |
| `smt.Proved` | `unsat` | No input satisfies the preconditions and violates the property, under the declared model |
| `smt.Counterexample` | `sat` with a complete model | A violating input exists; `.values` holds an `Assignment(name, width, value)` per argument |
| `smt.Unknown` | `unknown` | The solver could not decide |
| `smt.Timeout` | none in time | The bound elapsed and the solver was terminated |
| `smt.Failure` | none usable | `.kind` is `#'missing_executable`, `#'nonzero_exit`, `#'malformed_response`, or `#'bad_model` |

Only `unsat` produces `Proved`, and `outcome.is_proved` is true for nothing
else. A `sat` answer without a complete, well-formed model of the right widths
is a `Failure`, never a counterexample and never a success. Every outcome keeps
`.smtlib` (the exact query text), `.command`, `.diagnostics`, `.assumptions`,
and a `.describe()` summary, which is enough to reproduce a failure by hand.

A proof with preconditions is an implication. If the preconditions are
inconsistent, no input satisfies them, the solver answers `unsat`, and the
implication holds vacuously whatever the property says. `Proved` therefore
carries its assumptions: `.is_unconditional` is true only when there were none,
and `.describe()` reads "proved only under N assumption(s) [...]" otherwise. To
detect vacuity, check that the preconditions alone are satisfiable, for example
by querying the property `smt.not(smt.eq(result, result))` under them and
expecting a counterexample.

Diagnostics from lowering name the operation or function at fault. Their
`<stdin>` line numbers refer to the module text that was originally parsed.

## Checks and examples

From the repository root, without installing the package:

```sh
export PLTCOLLECTS="$PWD/pille-mlir-lib:${PLTCOLLECTS:-}"
export PILLE_MLIR_PREFIX=/path/to/llvm-23.1
raco make pille-mlir-lib/pille/mlir.rhm pille-mlir-lib/pille/mlir/dialect.rhm \
  pille-mlir-lib/pille/mlir/smt.rhm
raco test pille-mlir-lib/pille/mlir/tests
racket pille-mlir-lib/pille/mlir/examples/add.rhm
racket pille-mlir-lib/pille/mlir/examples/irdl.rhm
racket pille-mlir-lib/pille/mlir/examples/declarations.rhm
racket pille-mlir-lib/pille/mlir/examples/smt.rhm | z3 -in
# After building the query plugin as described above:
PILLE_MLIR_SMT_PLUGIN=/tmp/pille-smt-query/PilleSmtQuery.so \
  racket pille-mlir-lib/pille/mlir/examples/verify.rhm
# Requires the existing Pille LLVM dependencies and PILLE_LLVM_PREFIX too:
raco test pille/pille/tests/mlir.rhm
```

Keep the trailing separator in `PLTCOLLECTS` so that Racket's default
collections remain visible. With the package installed, the first line is
unnecessary. Compiling first matters only for speed.

The suite is not divided into optional parts: a missing tool is a failure, not a
skip. What each file needs:

| Tests | Requirements |
| --- | --- |
| `schema.rkt`, `semantics.rkt`, `smt-declarations.rkt`, `solver.rkt`, `toolchain.rkt` | None. They also assert that descriptors, expansion, and IRDL generation work with MLIR and Z3 absent |
| `api.rhm`, `declarations.rkt`, `integration.rkt` | MLIR |
| `smt-integration.rkt`, `smt-api.rhm` | MLIR, Z3, and the query plugin |

The SMT tests use `PILLE_MLIR_SMT_PLUGIN` if it is set. Otherwise they build the
plugin from this package's sources against the toolchain under test, into a
temporary directory removed at exit, which needs CMake and a C++ compiler and
takes a few seconds. They find Z3 through `PILLE_Z3` or `PATH`, and
`smt-integration.rkt` stops with "these tests require Z3" when there is none.
To run only the solver-backed tests:

```sh
raco test pille-mlir-lib/pille/mlir/tests/smt-integration.rkt \
  pille-mlir-lib/pille/mlir/tests/smt-api.rhm
```

`solver.rkt` covers the solver protocol with deterministic fake executables:
every outcome, malformed and incomplete models, termination on timeout and
interruption, cleanup, and paths containing spaces. `smt-integration.rkt`
repeats the semantic outcomes with real Z3, including a real `unknown` (under a
resource limit) and a real timeout, and compares lowered expressions with an
independent evaluator.

Upstream references: [IRDL](https://mlir.llvm.org/docs/Dialects/IRDL/),
[mlir-opt](https://mlir.llvm.org/docs/Tutorials/MlirOpt/),
[LLVM IR target](https://mlir.llvm.org/docs/TargetLLVMIR/),
[SMT dialect](https://mlir.llvm.org/docs/Dialects/SMT/).
