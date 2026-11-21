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

SMT verification has one further, optional requirement: Z3 (tested with 5.3.3),
which answers a `check` or a session's question. It is not needed to import any
module, expand declarations, obtain IRDL, or build and export a query. Nothing
is compiled: the lowering to the SMT dialect is written in Rhombus.

Tool selection follows this order:

1. An explicit `mlir.Toolchain(~prefix: path)`.
2. `PILLE_MLIR_PREFIX`.
3. `PILLE_LLVM_PREFIX`.
4. The usual places an LLVM installation is put (Homebrew's `llvm@23` and
   `llvm`, `/usr/lib/llvm-23`, and the like), where one of them has `mlir-opt`.
5. `mlir-opt` on `PATH`.

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

The SMT verification API is listed [below](#api-summary).

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
one place, and then ask questions of ordinary programs that use it:

```text
Rhombus operation declaration with an smt: clause
    -> expansion validates and records the schema and the semantic model
    -> IRDL registers the operation and verifies each instance's structure
    -> dialect.smt_query lowers a function and a property to the SMT dialect,
       and writes the SMT-LIB MLIR's exporter gives for it
    -> query.to_smtlib() is that text
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

The lowering is written in Rhombus (`pille/private/mlir/lower.rhm`) and is
driven by a manifest generated from the `Dialect` value. It names no custom
operation: a new or renamed operation, another namespace, or a different model
needs no change to it. Nothing is built. Building a query runs no tool at all;
`mlir-opt` verifies a module once, and Z3 answers a question.

There are four kinds of question, each over one function of a module:

| Question | Built with | Answer |
| --- | --- | --- |
| Does a property hold for every input that satisfies the preconditions? | `dialect.smt_query` | `Proved`, `Counterexample`, or `Infeasible` where named preconditions conflict |
| Which values can the result take? | `dialect.smt_values_query` | `Values` |
| What is the least or greatest value of a term? | `dialect.smt_objective` | `Optimum`, or `Infeasible` |
| Many claims under assumptions that are kept | `dialect.smt_scope` | `Proved` or `Counterexample`, one a claim |

### What a proof means

IRDL verification is structural: it checks that each instance has the declared
operands, results, attributes, and types. It says nothing about what an
operation computes. The `smt:` clause supplies a mathematical model, and a
`Proved` outcome means that the property holds *for that model*, for the
selected function, under the stated preconditions.

Attaching semantics declares the operation pure, deterministic, and total. IRDL
cannot establish this, and a dynamically registered operation has no MLIR effect
interfaces, so the declaration is trusted: an operation is not rejected for
lacking those interfaces, and an operation without a model is never assumed
pure. A proof also does not establish that an independent lowering, such as the
example `rhombus.add` to `arith.addi` pass, implements the same model.

### Supported fragment

| Aspect | Supported |
| --- | --- |
| Types | Signless `i1`, `i8`, `i16`, `i32`, `i64` |
| Type mapping | `iN` becomes `!smt.bv<N>` of exactly the same width; SMT-LIB `(_ BitVec N)` |
| Modeled operations | Fixed arity, exactly one result, no attributes, regions, or successors |
| Requirements | `requires a == b \|\| ...` in a model; each use's requirement is proved along with the property, so a counterexample may be a use outside what an operation's model covers. Ask the property `smt.eq(result, result)` to check the requirements alone |
| Semantic expressions | Operand and local references, literals, wrapping `bv.add`, `bv.sub`, `bv.mul`, and the choice `bv.if(a == b, then, else)` |
| Functions | `func.func` with one block and typed arguments, returning one scalar or several |
| Operations in a body | Modeled operations; `arith.constant`; `arith.cmpi` with every predicate; `arith.select`; `func.call` to a function of the same module |
| Properties and preconditions | Inputs, results, typed literals, `add`/`sub`/`mul`, `ite`; `eq`, the orderings, the overflow guards, `not`, `and`, `or` |
| Logic | `QF_BV` |

A declaration may accept several widths; its model is instantiated at each
instance's actual types. Widths are never converted, and are never assumed
equal: an instance that mixes widths where the model needs equal ones is
rejected while lowering. `bv.sub(a, b)` is emitted as `a + (-b)`, which is
exactly wrapping subtraction (the SMT dialect has no subtraction operation).

`i1` is a one-bit bitvector. Predicates are SMT Booleans (`!smt.bool`), a
separate sort; a one-bit term cannot be used as a predicate, and a predicate is
not a term. Each crossing is explicit: `arith.cmpi` gives the one-bit value 1
where its comparison holds and 0 where it does not, and `arith.select` chooses
its first value where its `i1` condition `== 1`. There are no unbounded
integers.

Signedness is never inferred. A term has none; an ordering says which it means
(`ult` or `slt`), as `arith.cmpi`'s predicate does, and an overflow guard or an
objective is unsigned unless given `~signed: #true`.

A `func.call` is inlined: the callee's block is lowered where the call stands.
The callee is held to the same fragment as a selected function. A function that
would call itself, directly or through another, and a call to a declaration
with no body are refused, since there is nothing to inline. (MLIR's own
`inline` pass is not used: an operation registered through IRDL has no inliner
interface, so the pass leaves a callee that uses one in place.)

A literal for width *w* must lie in [-2^(w-1), 2^w - 1], the range MLIR accepts
for an `iN` constant. A negative literal denotes its two's complement residue,
so `-1` and `0xffffffff` are the same 32-bit value. Anything outside the range
is an error; nothing is truncated.

Everything else fails with a diagnostic that names the operation or function
and its place, before any solver runs: other operations (including standard
ones such as `arith.addi`), operations without a model, other types (`index`,
floats, other widths, custom types), control flow, memory operations, regions,
and unused values outside the fragment. Attributes are rejected rather than
ignored, because the model cannot observe them: any attribute on a modeled
operation instance, any attribute on `arith.constant` other than `value`, on
`arith.cmpi` other than `predicate`, or on `func.call` other than `callee`, and
any function attribute other than `sym_name`, `function_type`, and
`sym_visibility`. Declaring `attributes(...)` together with `smt:` is an
expansion error for the same reason. A function that is neither selected nor
called is not part of the question and is not inspected.

### Terms and formulas

A `smt.Term` is a bitvector of an exact width. A `smt.Formula` is an SMT
Boolean. Builders check sorts and widths, so a mistake names both operands.

| Form | Result |
| --- | --- |
| `smt.input(name, ~width: n)` | A function argument. Its position in `~inputs` is its identity; the name is how it is reported |
| `smt.result(~width: n)` | The value a one-result function returns |
| `smt.result(index, ~width: n)` | One of the values a function with several returns, from 0 |
| `smt.const(value, ~width: n)` | A typed literal |
| `smt.add(a, b)`, `smt.sub(a, b)`, `smt.mul(a, b)` | Wrapping arithmetic on terms of equal width |
| `smt.ite(formula, then, else)` | A term: `then` where the formula holds, else `else` |
| `smt.eq(a, b)` | Equality of two terms of equal width |
| `smt.ult`, `ule`, `ugt`, `uge` `(a, b)` | Unsigned orderings |
| `smt.slt`, `sle`, `sgt`, `sge` `(a, b)` | Signed (two's complement) orderings |
| `smt.no_overflow_add(a, b, ~signed: #false)`, `no_overflow_sub`, `no_overflow_mul` | That the operation, on the numbers the terms stand for, does not wrap |
| `smt.not(p)`, `smt.and(p, ...)`, `smt.or(p, ...)` | Formulas over formulas |
| `smt.precondition(formula, ~named: name)` | A named precondition, for a `~preconditions` list |
| `term.width`, `term.describe()`, `formula.describe()` | The width, and the text an outcome shows |

`add`, `sub` and `mul` wrap, as the machine's do. An overflow guard says of one
use that it did not: with `no_overflow_add(a, b)` among a query's
preconditions, an answer that holds only because `a + b` wrapped is excluded.
The SMT dialect has no extend operation, so a guard does the operation one bit
wider (twice as wide for a product), built from `concat`, `extract` and
`repeat`, and compares it with its own low bits widened again.

Input names become SMT-LIB symbols verbatim, so they must be identifiers
(`[A-Za-z_][A-Za-z0-9_]*`) that are not reserved by SMT-LIB or its bitvector
theory. A precondition's name becomes a quoted symbol: any nonempty string
without bars, backslashes or line breaks, distinct within a query.

### Queries

`dialect.smt_query(module, ~function: name, ~inputs: [...], ~property: formula,
~preconditions: [...])` returns an immutable `smt.Query`. Constructing one
lowers and exports; it never runs a solver.

- The module must have been verified against this dialect's generated IRDL, as
  `dialect.module(...)` does. A module holds only MLIR and IRDL text, so the
  semantic model always comes from the `Dialect` value passed here. Identical
  IRDL can carry different meanings, and there is no registry of operation
  names: two dialect values with the same namespace and operation names are
  independent.
- The function is selected by symbol name. `~inputs` lists one `smt.input` per
  argument, in argument order. Printed SSA names are never consulted. Widths
  are checked against the function's actual types.
- The query asserts each precondition and the negation of the property (with
  every modeled operation's requirements), then checks satisfiability. No other
  assumption is added.

| Form | Result |
| --- | --- |
| `query.module` | The SMT dialect `mlir.Module`, verified by stock `mlir-opt` when it is first asked for; it contains no custom operations |
| `query.to_smtlib()` | The SMT-LIB text; no solver runs |
| `query.feasibility_smtlib()` | The question asked first where a precondition is named, else `#false` |
| `query.function`, `.dialect`, `.inputs`, `.property`, `.assumptions` | What the query asks, as data and text |
| `query.check(~solver: path = #false, ~timeout: seconds = 10, ~arguments: [])` | An `smt.Outcome` from running a standalone solver |

**How the SMT-LIB is made.** The lowering writes two things for a question:
the SMT dialect module, and the SMT-LIB that `mlir-translate --export-smtlib`
gives for that module, character for character. A query uses the second, so
building one starts no process: under a millisecond, where verifying the
module with `mlir-opt` and exporting it with `mlir-translate` takes about 28.
`PILLE_MLIR_SMT_EXPORT` chooses for a process:

| Value | What a query's SMT-LIB is |
| --- | --- |
| `direct` (the default) | The lowering's own text. The SMT module is verified only when `query.module` is asked for |
| `tools` | The module is verified by stock `mlir-opt`, with no IRDL definitions and no plugins, and exported by `mlir-translate` |
| `both` | Both are made, and it is an error where the two texts differ |

The tests run in `both`, so every question they ask is made both ways and
compared, and `smt-lowering.rkt` holds the lowering's own text to the
exporter's for each of its 645 recorded questions. What `direct` gives up is
that check on the question at hand: a fault in the lowering that stock MLIR
would have refused is no longer refused when the query is built. Use `tools`
or `both` where that matters more than the time.

**Named preconditions.** A proof with preconditions is an implication. If the
preconditions are inconsistent, no input satisfies them, the solver answers
`unsat`, and the implication holds vacuously whatever the property says. Naming
preconditions is how to be told instead: where any precondition of a query is
named, `check` first asks whether the preconditions can hold together, and
where they cannot the outcome is `smt.Infeasible`, whose `.core` names a set of
them that conflict.

```rhombus
def outcome:
  arithmetic.smt_query(program, ~function: "round_trip", ~inputs: [x, y],
                       ~property: smt.eq(result, x),
                       ~preconditions: [
                         smt.precondition(smt.ult(x, smt.const(10, ~width: 32)), ~named: "page.md:22"),
                         smt.precondition(smt.ugt(x, smt.const(20, ~width: 32)), ~named: "page.md:31"),
                       ]).check()
// smt.Infeasible, with outcome.core holding "page.md:22" and "page.md:31"
```

The solver is given `produce-unsat-cores` and `smt.core.minimize`, so a core
holds no name that could be left out; it is minimal as Z3 minimizes it, and a
different or smaller conflicting set may exist. Preconditions without a name
are asserted but never named, so a core may be empty where they alone conflict.
A query none of whose preconditions is named is unchanged: it has no
feasibility question, and inconsistent preconditions make it `Proved`. `Proved`
carries its assumptions either way: `.is_unconditional` is true only when there
were none.

### Objectives

`dialect.smt_objective(module, ~function: name, ~inputs: [...], ~minimize: term,
~preconditions: [...])`, or `~maximize: term`, returns an `smt.ObjectiveQuery`:
the least or greatest value of one term over the inputs that satisfy the
preconditions and keep every operation within its model's requirements. The
term is read as an unsigned number, or with `~signed: #true` as a two's
complement one. Its `check` gives `smt.Optimum`, whose `.value` is that number
and whose `.values` are inputs that reach it, or `smt.Infeasible` where no input
satisfies the preconditions.

```rhombus
// the greatest x for which x + y does not wrap, with y at least 5
arithmetic.smt_objective(program, ~function: "round_trip", ~inputs: [x, y], ~maximize: x,
                         ~preconditions: [smt.no_overflow_add(x, y),
                                          smt.uge(y, smt.const(5, ~width: 32))]).check()
```

MLIR's SMT dialect has no objective. The term is bound to a fresh symbol in the
verified SMT module, and Z3's `(minimize s)` or `(maximize s)` is written into
the exported SMT-LIB before its `(check-sat)`; `to_smtlib()` is that text. Z3
orders bitvectors as unsigned numbers, so a signed objective's symbol is the
term with its sign bit flipped, which keeps the signed order, and `.value` is
flipped back. A bitvector objective always has a bound, so there is no outcome
for an unbounded one. Without an overflow guard an optimum may be a value that
only wrapping arithmetic reaches; that is what the function computes, and a
guard among the preconditions excludes it.

`objective.function`, `.dialect`, `.inputs`, `.assumptions`, `.direction`,
`.is_signed`, `.describe()`, `.to_smtlib()` and `.feasibility_smtlib()` say what
is asked.

### Batches and sessions

Starting a solver is most of what a small question costs. Two forms avoid it.

`dialect.smt_batch(module, [smt.Spec(~function:, ~inputs:, ~property:,
~preconditions:), ...])` lowers and exports every question once and returns an
`smt.Batch`; `batch.check(~solver:, ~timeout:, ~arguments:, ~overall_timeout:)`
answers them with one solver process and gives one outcome a spec, in order.
`batch.queries` are the questions as `smt.Query` values. A diagnostic says
which spec it is about, by its index from 0.

`smt.Session(~solver:, ~arguments:)` keeps one solver process for as long as it
is wanted. `session.check(value, ~timeout:, ~overall_timeout:)` takes a
`Query`, a `Batch` or an `ObjectiveQuery` and gives what its own `check` gives.
The process starts with the first question, is restarted after a timeout, and
ends with `session.close()` or its custodian. A session serializes concurrent
callers.

### Scopes

A scope keeps assumptions in a session's solver from one question to the next,
for many claims about one function: checking a bounded number of steps, then one
more.

```rhombus
def session = smt.Session()
def scope = arithmetic.smt_scope(session, program, ~function: "round_trip", ~inputs: [x, y])
scope.assert(smt.ult(x, smt.const(10, ~width: 32)))   // for every question from here
scope.check(smt.ult(result, smt.const(10, ~width: 32)))   // smt.Proved
scope.push()
scope.assert(smt.eq(y, smt.const(0, ~width: 32)))     // for this frame only
scope.check(smt.eq(result, x))
scope.pop()
scope.close()
session.close()
```

| Form | Meaning |
| --- | --- |
| `dialect.smt_scope(session, module, ~function: name, ~inputs: [...])` | Opens a scope: the function's inputs are declared once in the session's solver |
| `scope.assert(formula)` | An assumption, for every question until its frame is popped |
| `scope.push()`, `scope.pop()` | A new frame of assumptions, and its end |
| `scope.check(property, ~timeout: seconds = 10)` | `Proved` where the property holds for every input satisfying what is assumed, `Counterexample` with inputs for which it does not |
| `scope.check_all([property, ...], ~timeout: seconds = 10)` | The same for each claim, in order, their formulas lowered together |
| `scope.assumptions`, `.inputs`, `.function`, `.dialect`, `.is_open` | What the scope holds |
| `scope.close()` | Ends it; the session takes other questions again |

Each question is asked in a frame of its own that is popped again, so it leaves
the scope as it found it. Each lowers its formula over the function anew, and
the solver keeps its process and what it has learned of the assertions it
holds. `check_all` lowers several claims together, which matters where the
tools export them (`PILLE_MLIR_SMT_EXPORT=tools`): one pass for all of them. A
timeout or failure ends the scope, and the claims after it are a `Failure` of
kind `#'closed_session`. To deepen a bounded check, select a function that returns what each step
gives (a step function called once for each step), assert what holds
throughout, and check one claim for each depth.

While a scope is open the session's `check` and `values` are refused: they
would be answered under the scope's assumptions, or would reset the solver. A
timeout or a solver failure ends the solver process and the scope with it. An
outcome's `.smtlib` is the question as one script, what the solver held and the
goal, and gives the same answer run by itself. Assumptions that cannot hold
together make every claim `Proved`, as a query's do; a scope's assertions are
not named.

### Possible values

`dialect.smt_values_query(module, ~function: name, ~inputs: [...],
~preconditions: [...])` returns an `smt.ValuesQuery` over a one-result function,
and `session.values(query, ~limit: n, ~timeout: seconds = 10)` enumerates the
values its result can take: an `smt.Values` whose `.values` are unsigned
residues in order and whose `.complete` says whether the limit was reached
first. An empty complete set means the preconditions are inconsistent
(`.is_inconsistent`), never a proof. Where some admitted input uses an operation
outside what its model requires, the answer is a `Failure` of kind
`#'requirements_not_satisfied`, so enumeration cannot hide a partial function.
`dialect.smt_values_batch(module, [smt.ValuesSpec(...), ...])` builds several at
once.

### Running a solver

Nothing but a `check` or `values` starts a solver. The solver is the `~solver:`
argument if given, else `PILLE_Z3`, else `z3` on `PATH`; an explicit or
environment selection that does not exist is a failure, not a fallback. A
standalone check runs it directly, without a shell, as
`solver [arguments...] query.smt2` in a private temporary directory that is
removed afterwards. `~timeout:` is a finite bound in seconds, 10 by default.
When it elapses the solver's process group is terminated, as it is if the
calling thread is interrupted.

A query's exported text is run unchanged. If the answer is `sat`, the solver is
run once more on the same commands through `(check-sat)` followed by the
standard `(get-value (...))` for the inputs, because the exported script ends
with `(reset)` and `get-value` is only legal after `sat`. Both runs share the
bound.

| Outcome | Solver result | Meaning |
| --- | --- | --- |
| `smt.Proved` | `unsat` | No input satisfies the preconditions and violates the property, under the declared model |
| `smt.Counterexample` | `sat` with a complete model | A violating input exists; `.values` holds an `Assignment(name, width, value)` per argument, in argument order |
| `smt.Infeasible` | `unsat` for the preconditions alone | The named preconditions cannot hold together; `.core` names a conflicting set. For an objective: no input satisfies the preconditions |
| `smt.Optimum` | `sat` with the objective's value | `.value` is the least or greatest value asked for; `.values` are inputs that reach it |
| `smt.Unknown` | `unknown` | The solver could not decide |
| `smt.Timeout` | none in time | The bound elapsed and the solver was terminated |
| `smt.Failure` | none usable | `.kind` is `#'missing_executable`, `#'nonzero_exit`, `#'malformed_response`, `#'bad_model`, `#'closed_session`, or `#'requirements_not_satisfied` |

Only `unsat` for the whole question produces `Proved`, and `outcome.is_proved`
is true for nothing else. A `sat` answer without a complete, well-formed model
of the right widths is a `Failure`, never a counterexample and never a success.
A counterexample reports inputs only; a function's results are whatever those
inputs give.

Every outcome keeps `.smtlib`, `.command`, `.diagnostics`, `.assumptions`, and a
`.describe()` summary. `.smtlib` is the text that reproduces the answer when it
is run through `z3` by hand: the query for most outcomes, the feasibility
question (the preconditions, `(check-sat)` and `(get-unsat-core)`) for
`Infeasible`, and the script with its objective for `Optimum`.

Diagnostics from lowering name the operation or function at fault. Their
`<stdin>` line numbers refer to the module text that was originally parsed.

### API summary

On a `Dialect` value:

| Form | Result |
| --- | --- |
| `dialect.smt_query(module, ~function:, ~inputs:, ~property:, ~preconditions:)` | `smt.Query` |
| `dialect.smt_objective(module, ~function:, ~inputs:, ~minimize:` or `~maximize:, ~signed:, ~preconditions:)` | `smt.ObjectiveQuery` |
| `dialect.smt_batch(module, [smt.Spec(...), ...])` | `smt.Batch` |
| `dialect.smt_scope(session, module, ~function:, ~inputs:)` | `smt.Scope` |
| `dialect.smt_values_query(module, ~function:, ~inputs:, ~preconditions:)` | `smt.ValuesQuery` |
| `dialect.smt_values_batch(module, [smt.ValuesSpec(...), ...])` | `smt.ValuesBatch` |

In `pille/mlir/smt`:

| Binding | What it is |
| --- | --- |
| `Term`, `Formula`, `Precondition` | A bitvector, an SMT Boolean, a named precondition |
| `input`, `result`, `const` | Terms for an argument, a returned value, a literal |
| `add`, `sub`, `mul`, `ite` | Terms from terms |
| `eq`, `ult`, `ule`, `ugt`, `uge`, `slt`, `sle`, `sgt`, `sge` | Comparisons |
| `no_overflow_add`, `no_overflow_sub`, `no_overflow_mul` | Overflow guards |
| `not`, `and`, `or` | Formulas from formulas |
| `precondition(formula, ~named:)` | Names a precondition |
| `Query`, `ObjectiveQuery`, `ValuesQuery` | One question; `to_smtlib()`, and `check(...)` on the first two |
| `Spec`, `Batch`, `ValuesSpec`, `ValuesBatch` | Several questions lowered together |
| `Session` | One solver process: `check`, `values`, `close` |
| `Scope` | Kept assumptions in a session: `assert`, `push`, `pop`, `check`, `check_all`, `close` |
| `Outcome` | What every answer is: `Proved`, `Counterexample`, `Infeasible`, `Optimum`, `Unknown`, `Timeout`, `Failure` |
| `Assignment(name, width, value)` | One input of a counterexample or an optimum |
| `Values(values, complete)` | A result's possible values |

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
racket pille-mlir-lib/pille/mlir/examples/verify.rhm   # needs Z3
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
| `schema.rkt`, `schema-api.rhm`, `semantics.rkt`, `smt-declarations.rkt`, `solver.rkt`, `sessions.rkt`, `toolchain.rkt` | None. They also assert that descriptors, expansion, and IRDL generation work with MLIR and Z3 absent |
| `api.rhm`, `declarations.rkt`, `integration.rkt`, `smt-lowering.rkt` | MLIR |
| `smt-integration.rkt`, `smt-synthesis.rkt`, `smt-bounded.rkt`, `smt-api.rhm`, `smt-batch.rhm` | MLIR and Z3 |

The tests find the tools as the library does. They find Z3 through `PILLE_Z3`
or `PATH`, and the `.rkt` files that need it stop with "these tests require Z3"
when there is none. To run only the solver-backed tests:

```sh
raco test pille-mlir-lib/pille/mlir/tests/smt-integration.rkt \
  pille-mlir-lib/pille/mlir/tests/smt-synthesis.rkt \
  pille-mlir-lib/pille/mlir/tests/smt-bounded.rkt \
  pille-mlir-lib/pille/mlir/tests/smt-api.rhm \
  pille-mlir-lib/pille/mlir/tests/smt-batch.rhm
```

`solver.rkt` and `sessions.rkt` cover the solver protocol with deterministic
fake executables: every outcome, malformed and incomplete models, termination
on timeout and interruption, cleanup, and paths containing spaces.
`smt-integration.rkt` repeats the semantic outcomes with real Z3, including a
real `unknown` (under a resource limit) and a real timeout, and compares lowered
expressions with an independent evaluator. `smt-lowering.rkt` holds the lowering
to a frozen record of 774 requests, with each difference from it written down
and explained. `smt-synthesis.rkt` checks comparisons, selection, overflow
guards, named preconditions and objectives against answers worked out by hand.
`smt-bounded.rkt` checks calls, scopes and a timed machine: a function that
steps a small state machine through twelve symbolic messages is proved to keep
its property, an altered one gives a counterexample that an evaluator replays,
and deepening a check one step at a time in a scope agrees with asking each
depth afresh.

Upstream references: [IRDL](https://mlir.llvm.org/docs/Dialects/IRDL/),
[mlir-opt](https://mlir.llvm.org/docs/Tutorials/MlirOpt/),
[LLVM IR target](https://mlir.llvm.org/docs/TargetLLVMIR/),
[SMT dialect](https://mlir.llvm.org/docs/Dialects/SMT/).
