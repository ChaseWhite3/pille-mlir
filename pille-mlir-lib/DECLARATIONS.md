# Generating IRDL through Rhombus expansion

`pille/mlir/dialect` provides extensible declaration and constraint spaces. A
`dialect` form enforests and expands its body, collects the resulting compiler
descriptors, validates their relationships, and generates IRDL. No MLIR
installation is needed for this expansion or for obtaining the generated text.
MLIR is required when the generated schema is registered to verify a program.

```rhombus
#lang rhombus/static/and_meta
import:
  pille/mlir/dialect open

constraint Integer:
  same("T", i32 || i64)

declaration.macro 'binary $(name :: Identifier)':
  'operation $name(lhs: Integer, rhs: Integer) -> (sum: Integer)'

dialect arithmetic("rhombus"):
  binary add

println(arithmetic.to_irdl())
```

This produces an `irdl.dialect @rhombus` containing an `irdl.operation @add`.
Its two operands and result use the same IRDL constraint variable, selecting
either `i32` or `i64`. The author writes the signature once. There is no separate
handwritten IRDL definition and no generator case for the `binary` convenience
form.

The complete [example](pille/mlir/examples/declarations.rhm) also generates a
parameterized custom type and attribute, then registers the generated dialect
and verifies a program using its `rhombus.add` operation.

## Expansion and bindings

`declaration`, `constraint`, and `semantic` (for [SMT semantics](#smt-semantics))
are `space.enforest` spaces, with parsed packers/unpackers and `Parsed` syntax
classes. Their primitive macros produce
packed compiler descriptors. Convenience macros can return further syntax in
the same space and let normal expansion continue. The enclosing `dialect` form
consumes the fully parsed declarations and embeds a versioned, portable schema
description in the compiled module. Runtime reconstruction validates that
description and deterministically regenerates its IRDL text.

The shared descriptor model is used at expansion and runtime. It has explicit
constraint, type, attribute, and operation records. It neither scans printed
Rhombus source nor attempts to recover declarations from fully lowered Racket
code. There is no global registration table or expansion-time file output.

`constraint Integer: ...` is a definition form binding a resolved constraint in
the constraint space. It can be exported and imported. Declaration and
constraint macros retain Rhombus's lexical binding behavior: an imported macro
continues to use its definition-site aliases even if a consumer defines a
same-spelled alias. Qualified imports can avoid ordinary name-shadowing issues
with open imports.

The quoted namespace in `dialect arithmetic("rhombus")` is the explicit MLIR
identity. Member names are explicit names within that namespace. Renaming an
import of `arithmetic` does not change those names. This release does not derive
globally unique MLIR namespaces from module paths or merge separately generated
dialects with the same namespace.

## Declaration forms

```rhombus
dialect example("example"):
  type word(element: i32 || i64)
  attribute mode(value: attr_is("\"checked\"") || attr_is("\"wrapping\""))
  operation annotate(value: type_ref("word", i32)) -> (result: type_ref("word", i32)):
    attributes(mode: attr_ref("mode", any))
```

Supported forms are:

| Form | Schema |
| --- | --- |
| `type name(parameter: constraint, ...)` | Parameterized type; `()` for no parameters |
| `attribute name(parameter: constraint, ...)` | Parameterized attribute |
| `operation name(operand: constraint, ...) -> (result: constraint, ...)` | Fixed-arity operation; `()` for no operands/results |
| An operation body clause `attributes(name: constraint, ...)` | Required named attributes |
| An operation body clause `smt:` followed by statements | The operation's [SMT semantics](#smt-semantics) |

An operation body holds at most one clause of each kind, in either order. A
repeated clause, an unknown clause, or `smt:` combined with a non-empty
`attributes(...)` is an expansion error.

All declarations within a dialect share one member namespace. Duplicate names,
unknown local references, wrong reference kinds or parameter counts, duplicate
port names, and conflicting equality constraints fail during expansion. Emitted
MLIR names must begin with a lowercase letter and contain lowercase letters,
digits, and single underscores. These restrictions follow the supported IRDL
definition rules; invalid names are diagnosed rather than silently renamed.
Operand and result names must also be distinct from each other.

Definitions may refer to types or attributes declared later in the same dialect.
`type_ref` and `attr_ref` refer to that dialect's explicit member names; they are
not Rhombus identifier lookups. A Rhombus constraint alias can wrap either form.
Cross-dialect parametric references are not currently supported by this model.

## Constraint forms

| Form | Meaning |
| --- | --- |
| `i1`, `i8`, `i16`, `i32`, `i64`, `index`, `f32`, `f64` | Exact builtin type |
| `type_is("MLIR type text")` | Exact type, using MLIR syntax |
| `attr_is("MLIR attribute text")` | Exact attribute, using MLIR syntax |
| `any` | Unrestricted IRDL constraint |
| `a || b`, `any_of(a, b, ...)` | Union of constraints |
| `a && b`, `all_of(a, b, ...)` | Intersection of constraints |
| `(constraint)` | Grouping; `&&` otherwise binds more tightly than `||` |
| `same("T", constraint)` | Reuse one constraint variable throughout a member |
| `type_ref("name", parameter_constraint, ...)` | Local custom type with constrained parameters |
| `attr_ref("name", parameter_constraint, ...)` | Local custom attribute with constrained parameters |

Repeated constraints are independent by default. Two ports constrained by
`i32 || i64` may choose different types. Using the same `same("T", ...)` key
requires them to choose the same type. Keys are scoped to each member definition
and must have structurally identical constraints wherever repeated. They are
explicit schema equality labels, not Rhombus bindings. Different aliases using
the same key within one operation intentionally share it.

MLIR's runtime loader restricts unions: alternatives must have a bounded
discriminating constraint and cannot overlap on the same parametric
type/attribute base. An `any` alternative is unbounded. These
cases are diagnosed during expansion. For example, write
`type_ref("word", i32 || i64)` instead of
`type_ref("word", i32) || type_ref("word", i64)`. The loader uses the first
constraint of an intersection to discriminate a union alternative, so place
a restricting constraint first: `all_of(i32, any) || i64` is supported, while
`all_of(any, i32) || i64` is rejected.

Raw `type_is` and `attr_is` payloads are checked for nonempty single-line text;
the MLIR parser validates their complete literal syntax when the schema is
loaded. `attr_is` takes MLIR text, so a string attribute includes escaped quotes,
as shown above. Structural schema validation does not require calling MLIR.

## SMT semantics

An `smt:` clause gives an operation a mathematical model next to its structure:

```rhombus
constraint Integer:
  same("T", i32 || i64)

dialect arithmetic("arithmetic"):
  operation add(lhs: Integer, rhs: Integer) -> (sum: Integer):
    smt:
      sum = bv.add(lhs, rhs)
  operation scaled_sum(lhs: Integer, rhs: Integer) -> (out: Integer):
    smt:
      let sum = bv.add(lhs, rhs)
      out = bv.mul(sum, bv.const(3, ~like: sum))
```

The clause does not change the generated IRDL. IRDL states which instances are
well formed; the clause states what a well-formed instance computes. Declaring
it asserts that the operation is pure, deterministic, and total, which IRDL
cannot check. The [MLIR guide](README.md#verifying-properties-with-declared-smt-semantics)
describes how the model is used to verify programs, and what a proof under it
does and does not mean.

### Statements and expressions

| Statement | Meaning |
| --- | --- |
| `let name = expression` | Bind an intermediate value for the statements that follow |
| `requires a == b \|\| c == d ...` | What the model requires of its operands: at least one comparison holds. A query proves this of every use of the operation, together with its property; it is never assumed |
| `result = expression` | Define the operation's result |

| Expression | Meaning |
| --- | --- |
| an operand or `let` name | That value; any name may be used any number of times |
| `bv.add(a, b)`, `bv.sub(a, b)`, `bv.mul(a, b)` | Wrapping (modular) arithmetic on two values of equal width |
| `bv.if(a == b, then, else)` | `then` where `a` equals `b`, `else` elsewhere; `a` and `b` have equal widths, as do the two arms. A comparison is written only here |
| `bv.const(value, ~width: n)` | A literal of width `n`, one of 1, 8, 16, 32, 64 |
| `bv.const(value, ~like: expression)` | A literal as wide as `expression`, or as the result when given the result's name |
| `(expression)` | Grouping |

Operations are modeled over fixed-width bitvectors: an operand or result of
type `iN` is a bitvector of exactly `N` bits, for `i1`, `i8`, `i16`, `i32`, and
`i64`. There are no implicit conversions, no signed or unsigned interpretation,
no unbounded integers, and no overflow flags. A bare literal such as `1` is an
error because it has no width. `~like:` uses only the width of its argument,
never its value, and it is the one place where the result's own name may
appear.

A literal for width *w* must lie in [-2^(w-1), 2^w - 1]. A negative literal
denotes its two's complement residue, so `bv.const(-1, ~width: 8)` and
`bv.const(255, ~width: 8)` are the same descriptor. A literal that does not fit
is an error at expansion when its width is known there, and otherwise when an
instance fixes the width; it is never truncated.

### Names and macros

Semantic expressions are parsed in their own extensible space, `semantic`.
`bv.add` and the other primitives are macros in that space, and so are
convenience forms:

```rhombus
semantic.macro 'twice($(value :: semantic_meta.Parsed))':
  'bv.add($value, $value)'

declaration.macro 'binary $(name :: Identifier): $meaning':
  'operation $name(lhs: Integer, rhs: Integer) -> (out: Integer):
     smt:
       out = $meaning(lhs, rhs)'

dialect arithmetic("arithmetic"):
  binary add: bv.add
  binary sub: bv.sub
```

Operand, result, and `let` names are real bindings. The `operation` form binds
them in the semantic space for the extent of its `smt:` clause, so a reference
resolves by Rhombus's ordinary lexical scope before it is reduced to a
descriptor identity:

- An imported semantic or declaration macro keeps its definition-site bindings
  when a consumer defines same-spelled names.
- An operand introduced by a macro is not captured by a same-spelled name that
  the macro's user writes; that reference is an unknown-reference error. When
  the user supplies both the operand names and the expression, they match.
- An operand shadows a same-spelled semantic macro inside its own clause.
- A `let` name is visible only to later statements, and may not repeat an
  operand, result, or earlier `let` name.

Nothing is inferred from how an operation or operand is spelled.

### Validation

These are reported during expansion, at the offending source location: unknown
references, the wrong number of arguments to a primitive, assigning to an
operand or an unknown name, assigning a result twice, leaving the result
unassigned, reading the result, an unsupported literal width or out-of-range
literal, and width or sort errors that the declaration alone decides.

Widths are compared through the declared constraints. Ports whose constraint is
the same `same("T", ...)` variable always agree. Ports with exact types are
compared directly, so adding an `i32` operand to an `i64` operand is an error.
A port that admits no supported type at all, such as `f32`, cannot have a model.

Independent constraints may or may not agree: with `lhs: i32 || i64` and
`rhs: i32 || i64`, IRDL accepts an instance of type `(i32, i64)`. Such a model
is accepted at expansion, and each concrete instance is then checked when it is
lowered, before any solver runs. A mixed-width instance is rejected there. It is
never coerced, and the model never gains a hidden assumption that the widths
are equal. The same holds for `any`, and for a literal whose `~like:` width is
only known per instance.

This first fragment requires exactly one result and no declared attributes: the
model cannot observe an attribute, so accepting both would let an attribute
carry meaning that every proof ignores. Regions, multiple results,
attribute-dependent semantics, and effects are outside it.

### Descriptors

The model is an immutable typed expression tree stored with its operation. It
is embedded in the compiled module with the rest of the schema and validated
again when the `Dialect` value is reconstructed at run time. The serialized
schema is versioned JSON. Version 2 adds an optional semantics field to each
operation, which is `null` for a schema-only declaration. Version 1 descriptors,
which have no such field, remain readable and yield operations without
semantics; descriptors are always written as version 2, and any other version
is rejected. Serialization is deterministic, and semantics never affect the
generated IRDL: two dialects can have identical IRDL and different models.

Declaring semantics, importing such a module, and obtaining IRDL need neither
MLIR nor a solver, and expansion starts no tools and writes no files.

## Using the result

`dialect` binds an immutable `Dialect` value:

| Member | Result |
| --- | --- |
| `.name` | Explicit MLIR namespace |
| `.operation_names` | List of fully qualified operation names |
| `.operation_name("add")` | A checked operation identity, such as `"rhombus.add"` |
| `.smt_operation_names` | The operations that declare SMT semantics |
| `.to_irdl()` | Generated IRDL text |
| `.module(source, ~toolchain: mlir.Toolchain())` | Registered and verified `mlir.Module` |
| `.smt_query(module, ~function: name, ~inputs: [...], ~property: formula, ~preconditions: [...], ~plugin: path)` | A verified [`smt.Query`](README.md#queries) for one function |

The latter is equivalent to `mlir.Module(source, ~irdl: dialect.to_irdl(), ...)`.
Use the returned module's existing pass and export methods. The optional native
`pille-lower-add` example plugin can lower an `add` operation declared in the
`rhombus` namespace with the signature shown above. Build it following the
[MLIR guide](README.md#runtime-dialects-through-irdl), then set
`PILLE_MLIR_ADD_PLUGIN` when running `examples/declarations.rhm` to print LLVM
IR after registering and lowering the generated dialect.

### Building a dialect from data

A program that already holds its declarations as data, such as another
language's own declaration model, can build the same `Dialect` at run time with
`pille/mlir/schema` instead of the `dialect` form:

```rhombus
import:
  pille/mlir/schema

def integer = schema.same("T", schema.any_of([schema.type_is("i32"), schema.type_is("i64")]))
def arithmetic:
  schema.make_dialect(
    "arithmetic",
    [schema.operation("add",
                      ~operands: [["lhs", integer], ["rhs", integer]],
                      ~results: [["sum", integer]],
                      ~smt: schema.semantics("sum", schema.add(schema.operand("lhs"),
                                                                 schema.operand("rhs"))))])
```

| Function | Counterpart |
| --- | --- |
| `type_is`, `attr_is`, `any`, `any_of([...])`, `all_of([...])`, `same(key, c)` | The constraint forms |
| `type_ref(name, [c, ...])`, `attr_ref(name, [c, ...])` | References to the dialect's own types and attributes |
| `type(name, ports)`, `attribute(name, ports)` | `type` and `attribute` declarations; ports are `[[name, constraint], ...]` |
| `operation(name, ~operands:, ~results:, ~attributes:, ~smt:)` | An `operation` declaration |
| `operand(name)`, `local(index)`, `const(value, ~width:)`, `const(value, ~like:)`, `const(value, ~like_result:)`, `add`, `sub`, `mul` | Semantic expressions |
| `semantics(result, expression, ~lets: [[name, expression], ...])` | An `smt:` clause |
| `make_dialect(namespace, members)` | The `dialect` form |

The constructors run the same validation as the declaration forms and raise
ordinary errors, since there is no source location to report. A dialect built
either way generates identical IRDL and supports the same queries.

An operation's attribute names may be dotted (`"closer.name"`), as MLIR
attribute keys usually are; each segment follows the naming rules above.
Operand, result, type and operation names may not.

A module holds only MLIR and IRDL text, not descriptors. `smt_query` therefore
takes the semantic model from the `Dialect` value it is called on, and requires
the module to have been verified against that dialect's generated IRDL. An
operation without an `smt:` clause remains fully usable for registration and
verification; using it in a function selected for a query is an error at that
point.

This first fragment covers fixed-arity signatures, type/attribute parameters,
required attributes, logical constraints, shared constraint variables, and SMT
semantics for single-result bitvector operations. It does not yet describe
regions, successors, optional/variadic ports, interfaces, or effects. IRDL does
not supply execution semantics, and an SMT model is not a lowering: producing
LLVM still needs a pass, and a proof about the model does not by itself prove
that pass correct. Semantics are not extracted from arbitrary Rhombus code.
Pille's existing expression compiler is not automatically retargeted by
importing this module.

## Verification

From the repository root with the package installed and MLIR configured:

```sh
raco test pille-mlir-lib/pille/mlir/tests
racket pille-mlir-lib/pille/mlir/examples/declarations.rhm
```

The tests expand imported macros without an installed toolchain, check invalid
schemas at expansion, and verify the generated definitions with real MLIR.
They also test operator precedence, grouping, definition-site bindings, custom
type/attribute validation, and the difference between shared and independent
constraint variables.

For SMT semantics, `tests/semantics.rkt` and `tests/smt-declarations.rkt` cover
descriptors, serialization versions, hygiene, and source-located expansion
errors without MLIR or a solver. `tests/smt-integration.rkt` and
`tests/smt-api.rhm` lower real programs and check them with Z3; they and
`examples/verify.rhm` need the query plugin and Z3, as the
[MLIR guide](README.md#checks-and-examples) explains.
