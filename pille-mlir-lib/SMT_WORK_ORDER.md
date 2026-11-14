# Work order for declaration driven SMT verification

Implement the missing path from Rhombus dialect declarations to SMT verification
in Pille. A language author must be able to declare an operation's structure and
SMT meaning together, compile a program using that operation into MLIR's SMT
dialect, export SMT-LIB, and check a property with Z3. Complete the implementation,
tests, runnable examples, and documentation described below.

Work in `/Users/chasewhite/gitStuff/pille`. Preserve existing changes: the MLIR
package and its declaration layer are currently present as uncommitted work.
Inspect the working tree and any repository instructions before editing. This
order authorizes implementation in the checkout; it does not request publishing
or committing changes.

## Current implementation

The following already works and should be extended:

| File relative to this package | Responsibility |
| --- | --- |
| `pille/mlir/dialect.rhm` | Extensible Rhombus `declaration` and `constraint` enforestation spaces; the `dialect` definition form; public `Dialect` methods |
| `pille/private/mlir/schema.rkt` | Immutable schema descriptors, validation, versioned JSON serialization, deterministic IRDL generation |
| `pille/mlir.rhm` | Public `Toolchain` and immutable verified `Module` values |
| `pille/private/mlir/tools.rkt` | MLIR subprocess invocation, IRDL registration, pass execution, LLVM and SMT-LIB export |
| `pille/mlir/examples/declarations.rhm` | Custom types, attributes, operations, and convenience macros generating IRDL |
| `pille/mlir/examples/smt.rhm` | Direct SMT dialect example, exported through `.to_smtlib()` |
| `pille/mlir/examples/lower-add-plugin.cpp` | Example native pass lowering `rhombus.add` to wrapping `arith.addi` |
| `pille/mlir/tests/` | Schema, macro expansion, hygiene, toolchain, and real MLIR integration tests |

The package suite passed 34 tests before this order. The direct SMT example was
also run through Z3 and returned `unsat` for the counterexample query to
32-bit wrapping `x + 0 == x`. These checks establish the existing export path;
they do not establish custom-dialect SMT lowering.

`Dialect.module()` currently passes only generated IRDL and the toolchain to
`Module`. A module retains MLIR text, IRDL text, and its toolchain; it does not
retain the declaration descriptors or semantic rules. Account for this boundary
explicitly when adding the new API.

## Required result

Deliver this complete workflow:

```text
Rhombus operation declaration with an SMT meaning
    -> expansion validates and records schema plus semantic descriptors
    -> IRDL registers and verifies custom operation instances
    -> verified program and property become an SMT dialect query
    -> existing Module.to_smtlib() exports the query
    -> Z3 returns proved, counterexample, or an inconclusive outcome
```

IRDL defines structural constraints. The new semantic clause supplies the
operation's mathematical model. A proof is relative to that model and its
assumptions; it does not automatically prove an independent LLVM lowering
correct.

For this fragment, attaching semantics explicitly declares a pure, total model
of the custom operation. IRDL does not establish purity, and a dynamically
registered operation may lack MLIR effect interfaces. Do not reject a modeled
operation solely for lacking those interfaces, or infer purity for unmodeled
operations. Reject known effects and any semantic contract outside this fragment.

## First supported fragment

Finish a useful, explicitly bounded first version:

- Pure, deterministic, total operations with fixed arity and one scalar result.
- Concrete signless integer types `i1`, `i8`, `i16`, `i32`, and `i64`, mapped to
  SMT bitvectors of exactly the same width. A declaration may accept several
  widths; instantiate its semantics at the actual verified operand/result types.
- Semantic expressions containing operand references, bitvector constants, and
  wrapping addition, subtraction, and multiplication. Expressions must compose
  and permit reuse of operands and intermediate results.
- Straight-line `func.func` bodies with one block, typed arguments,
  `arith.constant`, supported declared operations, and one returned scalar.
- Properties over function inputs and the returned value, using equality,
  Boolean negation, conjunction, and disjunction. Support explicit preconditions.
- SMT-LIB export and an explicit Z3 invocation with a finite timeout and
  counterexample values for supported input types.

Keep SMT Boolean predicates distinct from numeric `i1`/one-bit bitvectors. Do
not infer signed comparisons, integer arithmetic, overflow flags, or implicit
width conversions. Define literal range/normalization behavior explicitly.

Other operations, types, control flow, regions inside custom operations,
multi-result operations, memory/effects, floating point, `index`, recursion,
quantifiers, and attribute-dependent semantics may remain unsupported. Reject
them with useful diagnostics at the relevant boundary. Ordinary schema-only
declarations must continue to work; absence of SMT semantics becomes an error
when the selected program uses that operation for an SMT query.

Automatic extraction of semantics from arbitrary Rhombus code, IRDL-to-SMT
schema analysis, a new LLVM backend, and proving general compiler correctness
are outside this order.

## Declaration and descriptor changes

Add an optional semantic clause to operation declarations. The following is
illustrative proposed syntax, not a currently available API:

```rhombus
constraint Integer:
  same("T", i32 || i64)

dialect arithmetic("arithmetic"):
  operation add(lhs: Integer, rhs: Integer) -> (sum: Integer):
    smt:
      sum = bv.add(lhs, rhs)
```

Choose idiomatic final syntax and document it. Retain the existing `attributes`
body form and reject duplicate or conflicting clauses. Parse semantic
expressions through a dedicated extensible binding/enforestation space, with
packed structured descriptors like the existing constraint space. Convenience
macros must expand normally, preserve definition-site bindings, and resolve
operand references hygienically before reducing them to descriptor identities.
Do not infer meaning from an operation's spelling or scan printed Rhombus code.

Extend the immutable model with a small typed semantic expression tree. Validate
unknown operand/result references, expression arity, duplicate assignments,
result coverage, and sort/width relationships. Diagnose errors during expansion
when the declaration provides enough information; otherwise validate at concrete
instantiation before invoking Z3. A schema that permits mixed widths must not
silently acquire a same-width assumption in its solver model.

Serialize and deserialize semantics deterministically with validation. Keep
existing version 1 schema-only descriptors readable, with absent semantics.
If the format changes, introduce a version deliberately and update unsupported
version tests accordingly. Importing declarations, expanding macros, and
obtaining IRDL must continue to work without MLIR or Z3 installed. Do not launch
tools, build plugins, or write registration files during expansion.

## Program lowering and query API

Prefer a dialect-owned query/lowering API that receives the verified module,
selected function, property, and optional preconditions. The `Dialect` value
retains the semantic descriptors and should supply them explicitly. If a
module-owned API is chosen instead, add immutable semantic metadata and preserve
it through module construction and pass results. In either design, validate
compatibility between the supplied program's dialect definitions and semantic
descriptors. Do not use a global registry keyed only by operation name.

Structural compatibility covers names and signatures. Identical IRDL can have
different attached meanings, so IRDL equality cannot establish semantic identity.
With a dialect-owned API, the explicitly supplied dialect selects the model;
with retained module metadata, detect and reject conflicting semantic models.

Provide a structured property builder so callers do not have to write SMT MLIR
or SMT-LIB. Input and result references must have checked identities and sorts.
Select the function by symbol and bind inputs by argument position, with
caller-supplied display names; bind the result to the selected return value.
Do not depend on printed SSA names, which MLIR may normalize. Include typed
literals in the property builder.
The API must expose the generated verified SMT `Module` and its SMT-LIB text
independently of running a solver.

Lower actual instances of declared custom operations in the verified MLIR
program. Preserve SSA dataflow, constants, operand order, repeated uses, and
return-value identity. Support several instances and different declared
operations in one function. A second namespace and a differently named
operation with the same semantic expression must work without native code edits.

Use MLIR's structured parser and transformation APIs for this lowering. A native
pass/helper consuming a validated declarative semantics manifest is a reasonable
fit for the existing tool-based architecture. Reuse existing mechanisms where
available, and verify APIs against the installed MLIR release. Do not implement
the bridge with regex rewriting, hardcoded `rhombus.add` dispatch, or a separate
SMT-LIB emitter that bypasses the verified SMT dialect and existing exporter.
Building a reusable helper at runtime setup/build time is acceptable; requiring
new handwritten C++ for every user operation is not.

Build a fresh SMT solver query from the selected function. Declare symbolic
inputs and assert `preconditions AND NOT(property)`, then check satisfiability.
For the supported total fragment, add no hidden assumptions. Use `QF_BV` for
these bitvector queries. An inconsistent precondition makes the implication
vacuously true; document this and report the actual assumptions with the result.

Before export, ensure the query contains only supported exportable operations
and types. `mlir-translate` currently receives neither IRDL definitions nor
custom plugins, so merely retaining custom operations in the output cannot
work. Unknown operations must fail instead of being erased, ignored, or treated
as unconstrained functions. Define an explicit policy for unsupported operation
attributes so potential semantic information is not silently dropped.

## Solver integration

Keep `.to_smtlib()` export-only. Add a separate opt-in solver API, with an
explicit executable override and documented executable discovery. Reuse the
existing direct-process style: pass arguments without a shell, isolate temporary
files, preserve diagnostics, and clean up on success, failure, or cancellation.
The current MLIR process helper is synchronous; solver execution additionally
needs bounded waiting and child-process termination on timeout.

Return structured outcomes with these distinctions:

| Solver outcome | Public meaning |
| --- | --- |
| `unsat` | No counterexample under the supplied model and assumptions |
| `sat` | Counterexample exists; return caller-visible input names, widths, and values |
| `unknown` | Solver could not determine the answer |
| Timeout | Execution exceeded the requested bound |
| Missing executable, nonzero exit, malformed response | Operational failure with diagnostics |

Only `unsat` may produce a proved result. Missing or invalid model data must not
turn `sat` into success. Obtain and parse counterexample assignments through a
supported solver protocol, such as SMT-LIB `get-value`, after a satisfiable
result; verify how this interacts with the current MLIR exporter. Preserve query
text and enough diagnostics to reproduce failures. Document that proofs concern
the declared semantic model.

## Acceptance tests

Use pure tests for descriptors and expansion, real MLIR tests for lowering and
verification, and real Z3 tests for semantic outcomes. Solver protocol tests may
use deterministic fake executables for error paths; they do not replace real
solver checks.

1. Existing package tests and examples still pass. Schema-only imports and
   descriptor round trips work with MLIR and Z3 absent from the environment.
2. An exported semantic macro retains definition-site bindings when a consumer
   shadows a same-spelled binding. Nested macro expansion also works.
3. Malformed semantics produce useful source-located errors. Cover unknown
   references, wrong primitive arity, wrong result assignments, and invalid
   widths/sorts. Unsupported concrete instances fail before solver execution.
4. A declaration accepting `i32` and `i64` produces correctly sized SMT for
   separate instances of both types. Mixed-width instances are rejected rather
   than coerced or assumed equal. Smoke-test every supported width, including
   `i1` becoming `!smt.bv<1>` while property predicates use `!smt.bool`.
5. With symbolic `x`, prove `add(x, 0) == x` and `sub(add(x, y), y) == x` for
   wrapping arithmetic. The second property must lower composed custom
   operation instances with shared SSA values.
6. Refute the false property `add(x, 1) == x`. Parse the counterexample and
   replay it with an independent finite-width evaluator. Validate supplied
   preconditions as well as the violated property.
7. Verify overflow behavior: for 32-bit inputs, `add(0xffffffff, 1) == 0` is
   proved, while `add(0xffffffff, 1) == 0xffffffff` is refuted. Also exercise
   multiplication. Do not encode these as unbounded mathematical integers.
8. Rename the operation and namespace and add a second operation using a
   different expression. The same lowering machinery handles both without a
   new handwritten native pattern. Test same-spelled operations in separate
   dialect values to catch accidental global semantic lookup.
9. Compare the supported expressions against an independent evaluator across
   exhaustive small-width inputs or representative boundary cases. These checks
   test translation fidelity; solver consistency alone is insufficient.
10. Missing semantics, unknown operations, unsupported control flow/effects,
    unsupported types/attributes, and incompatible descriptors fail explicitly.
    The verified SMT output contains no residual custom operations.
11. Test preconditions, including a deliberately inconsistent precondition, and
    document implication/vacuity behavior. An `unsat` result must not be
    presented as an unconditional property when assumptions were supplied.
12. Distinguish `sat`, `unsat`, `unknown`, timeout, missing executable, nonzero
    exit, malformed output, and bad model data. Confirm a timeout terminates the
    child and cleans temporary resources. Also test paths containing spaces.

If solver tests are separated from the default suite, provide a documented
command that requires Z3 and fails clearly when it is missing. Run that suite
before claiming this order complete; skipped solver tests are not completion.

## Environment and verification commands

The previous successful checks used Racket 9.3, LLVM/MLIR 23.1.5 on aarch64
macOS, the prefix `/opt/homebrew/opt/llvm@23`, and Z3 at
`/opt/homebrew/bin/z3`. Rediscover and report actual versions in the execution
environment. Keep installation paths configurable in production code.

From the repository root, the existing baseline can be run without installing
this package globally:

```sh
export PLTCOLLECTS="$PWD/pille-mlir-lib:${PLTCOLLECTS:-}"
export PILLE_MLIR_PREFIX=/opt/homebrew/opt/llvm@23
raco test pille-mlir-lib/pille/mlir/tests
racket pille-mlir-lib/pille/mlir/examples/declarations.rhm
racket pille-mlir-lib/pille/mlir/examples/smt.rhm > /tmp/pille-smt-baseline.smt2
z3 -in < /tmp/pille-smt-baseline.smt2
```

The last command should print `unsat`. Follow the package README for native
plugin build requirements. Any new native component must have a reproducible
build using the same MLIR installation as the tools. Do not depend on temporary
build artifacts from the previous session. Keep the existing LLVM/ORC bridge
test intact; run it if changes affect that boundary and its dependencies are
available.

## Deliverables and completion

Deliver the implementation, focused tests, and one runnable Rhombus example
that declares semantics, constructs an ordinary custom-dialect program, exports
an SMT query, proves a true property, and reports a counterexample to a false
one. The example must not contain handwritten SMT MLIR or SMT-LIB.

Update `README.md` and `DECLARATIONS.md` in this package with the final syntax,
supported fragment, type mapping, build requirements, solver configuration,
result meanings, and exact verification commands. Explain the difference
between IRDL structural verification and proof under declared SMT semantics.
Preserve the original direct SMT example as a low-level example.

In the implementation handoff, list changed files, actual commands run, test
results, observed true/false query outcomes, and remaining unsupported features.
Complete the end-to-end workflow before reporting success. A new clause parser,
generated schema, or another manually authored SMT example alone does not
complete this order.

## References

- [Existing declaration guide](DECLARATIONS.md)
- [Existing MLIR tool and plugin guide](README.md)
- [Upstream IRDL dialect](https://mlir.llvm.org/docs/Dialects/IRDL/)
- [Upstream SMT dialect](https://mlir.llvm.org/docs/Dialects/SMT/)
