# Work order for checked propositions from Markdown in Closer

Implement one complete path from a Markdown sentence to a checked proposition,
its source occurrence, a context-dependent judgment, and an existing Closer graph
view. The result must preserve the identities of the language declarations and
Materials instances the sentence refers to. A statement that is meaningful but
false, unestablished, or in violation of a requirement must remain representable.

This is an implementation handoff for an AI working on Closer. Deliver code,
focused tests, a runnable example, and documentation. Complete the bounded slice
below before expanding the language or migrating unrelated commands.

## Repository and working rules

The implementation target is `/Users/chasewhite/Documents/gitStuff/anote-java-clojure`.
This work order is stored in `/Users/chasewhite/gitStuff/pille` for handoff. Pille
is a supporting dependency; this task does not require moving Closer into Pille.

Read the target checkout's instructions and inspect its working tree before
editing. Preserve other contributors' uncommitted work, particularly in
`closer-lang`. Inspect the current Rhombus implementation before deciding what is
missing: the migration is active, and older status reports and documentation can
lag the code. Extend existing facilities instead of introducing a parallel
compiler, proposition system, or graph format. Do not publish or remove
unrelated implementations as part of this order.

Keep the delivered path on Rhombus and the project's selected Pille parser route.
Do not introduce a new Mojo dependency or an offline depccg preparation step.
If a supporting Pille change is necessary, isolate the missing primitive with a
reproduction and keep the change small; domain policy belongs in Closer.

## Meaning of the boundary

Keep the following responsibilities distinct, even when they share a source file:

| Responsibility | What it establishes |
| --- | --- |
| Language declaration | A kind, predicate, state, or operation exists, with a signature and declared meaning. |
| Materials declaration | A particular instance exists in a context, with its kind and any explicitly supplied initial facts. |
| Requirement | A proposition is required to hold under specified conditions. |
| Elaboration | A source construction resolves to known declarations and instances and composes correctly. |
| Assertion or observation | A source occurrence asserts content or supplies evidence according to its explicit role. |
| Judgment | A proposition is evaluated or checked against specified facts, assumptions, and a moment or context. |

Call elaboration's successful result a **checked or well-formed proposition**.
Successful elaboration establishes neither truth, requirement satisfaction, nor
permission to execute an operation. Requirements are not automatically assumptions.
An ordinary page claim being checked is not evidence for itself. Initial facts,
observations, and explicit assumptions enter evaluation only through the roles
the language gives them, with provenance.

Imports and declarations determine the available vocabulary. This is a semantic
boundary, not a security sandbox or a guarantee that declarations are consistent.
Check declaration shape and references separately from consistency of the facts
and constraints used for a judgment.

## Required example

Use an existing declaration syntax where possible. The following is conceptual
notation, not a proposed public API:

```text
Language:
    Panel : Kind
    Pump : Kind
    Active : Panel -> Proposition

Materials:
    panel_a : Panel
    panel_b : Panel
    pump_a  : Pump

Page:
    panel_a is active.

Resolved content:
    Active(panel_a)

Source occurrence:
    this sentence asserts that content in this context at this moment

Judgment:
    evaluated separately against the explicitly selected facts and assumptions
```

`Panel` is a kind; `panel_a` is an instance. Applying `Active` to the kind itself
must fail unless a different signature explicitly accepts kinds. If the existing
state/formula model can express `Active`, reuse it rather than creating a second
predicate framework.

Also accept “the panel is active” when the supplied name-resolution context
uniquely selects a panel. With two eligible panels and no disambiguating context,
report ambiguity. Do not choose by declaration order, recency, or parser score
alone. Preserve existing documented contextual rules and show which rule resolved
a successful reference.

Run the same well-formed claim in three explicit fixture contexts: evidence that
it holds, evidence that it does not hold, and insufficient evidence. Make the
fixture's state relationships explicit. Missing evidence must not become a false
judgment merely because no supporting fact was found.

## Existing implementation to inspect

These are starting points, not a prescribed list of files to modify. Confirm the
current contracts and callers before changing them.

| Area | Starting point |
| --- | --- |
| Language identities and imports | [Kinds as bindings](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/docs/kinds-as-bindings.md), [noun space](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-lang/nouns.rhm), and [language declarations](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-lang/language.rhm) |
| Formulas and their meaning | [Formula contract](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/docs/formulas.md), [formula core](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-lang/formulas.rhm), and [rules](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-lang/rules.rhm) |
| Markdown and phrase expansion | [Phrase space](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-exports/closer_exports/phrase/space.rhm) and its existing fixtures |
| Compilation and judgments | [Rhombus compile](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-exports/closer_exports/compile.rhm) and [requirements](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-exports/closer_exports/requirements.rhm) |
| Instances and contexts | [Assembly model](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-exports/closer_exports/assembly/model.rhm) and [Materials](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-exports/closer_exports/assembly/materials.rhm) |
| Occurrences and downstream records | [Receiving records](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-exports/closer_exports/receiving.rhm) and [refinement occurrences](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-exports/closer_exports/refinement/occurrences.rhm) |
| Independent semantic references | [Receiving model](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/models/receiving_model.rkt) and [claim model](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/models/claim_model.rkt) |

## Implementation requirements

### Binding and elaboration

Reuse the existing vocabulary parser, phrase spaces, formula forms, and import
rules. Markdown words must be resolved through the declared vocabulary and the
selected context. Do not infer a declaration's meaning from its spelling or
manufacture a binding by turning a string into an identifier without the required
lexical context.

Preserve hygienic identity through expansion, including definition-site bindings
inside convenience macros. Map resolved bindings to explicit semantic identities
before crossing a serialized boundary. Display names remain distinct from those
identities. Imported aliases must denote the same declaration, while separately
declared concepts with identical spellings remain distinguishable.

A proposition binding space is appropriate if it supplies distinct syntax and
bindings. Validation and evaluation are processing stages; do not add a binding
space for each stage merely to match the terminology of this work order. Document
the chosen extension point and how another module adds a supported construction.

### Checked representation and ingestion

Extend existing records or constructors to preserve these logical distinctions;
the names below do not require new parallel record types:

- Declaration identity and signature, including the owning language/module.
- Instance identity, kind, and name-resolution context.
- Proposition content with resolved references and checked arguments.
- Source occurrence with source revision/span, proposition reference, authored
  role, and evaluation context or moment where applicable.
- Judgment with the proposition, selected context, assumptions/evidence,
  completion status, outcome, and supporting or opposing explanation.

Use controlled constructors or equivalent validation to prevent arbitrary strings
from masquerading as checked terms. Validate raw/imported records against the
receiving declaration and instance environment. Reject unknown identities, kind
mismatches, malformed nodes, and incompatible schema/model versions. A payload's
own `checked` flag is not validation. Recompute judgments after import unless
existing evidence validation establishes that a cached result applies to the
same model, context, and source revision.

Two authored sentences expressing the same content must retain two occurrences.
Content sharing is optional; provenance must not be overwritten. Define the
identity lifetime explicitly. Stable references within a build and across its
exports are required; persistent identity across arbitrary edits is outside this
slice unless an existing mechanism already provides it. Never reuse an old result
solely because a display name or source offset matches.

### Diagnostics and completeness

Unknown names, ambiguous readings, wrong argument kinds, and unsupported syntax
must produce structured diagnostics at the relevant source span. Show candidate
declarations or instances where helpful. Preserve the original construction so a
consumer can explain what was not understood.

No accepted meaning may silently omit a guard, negation, quantifier, or other
semantic clause. Include an `unless` regression: if the current implementation
supports it, preserve and evaluate the guarded meaning; otherwise retain it with
an unsupported/incomplete result. Do not turn it into an unguarded claim.

Keep semantic outcomes distinct from completeness and tool status. Insufficient
evidence is different from unsupported syntax, inconsistent assumptions, or a
solver timeout. An affected requirement cannot receive an unqualified success
from an incomplete interpretation. Reuse existing outcome conventions where they
express these distinctions; document any necessary schema extension.

### Evaluation and graph integration

Use Closer's current evaluator and independent semantic models for the supported
fragment. Establish judgments from the supplied context, rather than from the
fact that a sentence successfully elaborated. Keep a required proposition and a
claimed proposition out of the assumptions used to establish that same claim,
unless an explicit, separately recorded assumption supplies it.

Integrate with one existing graph view. It must expose the proposition, its
instance/declaration references, its occurrence, and its judgment or incomplete
status. Source navigation must reach the correct occurrence. A claim that fails a
requirement remains visible with its explanation. Reuse current node and edge
contracts and update their consumer checks where needed; a new general graph UI
is outside scope.

MLIR/SMT emission is not a new deliverable of this order. If the existing evaluator
uses those backends, exercise that existing path and preserve assumption/goal
separation. IRDL validity alone is not evidence that a proposition holds. Keep the
checked representation usable by later lowering without requiring new backend
work to finish this slice.

## Acceptance tests

Use public construction/elaboration entry points and the real compile/record
path. Tests should assert observable semantics and diagnostics, not duplicate the
implementation. Adapt existing fixtures where possible.

| Case | Required result |
| --- | --- |
| Explicit instance | “panel_a is active” resolves to the declared predicate and `panel_a`, with source/context retained. |
| Unique contextual reference | “the panel” resolves when one instance is selected by the supplied context. |
| Ambiguous reference | Two eligible panels produce a source-located ambiguity with candidates and no successful arbitrary resolution. |
| Unknown noun or predicate | An explicit unresolved result; no invented declaration. |
| Wrong argument | `Active(pump_a)` and `Active(Panel)` fail with a useful kind/category diagnostic. |
| Same spelling in two modules | Distinct declarations remain distinct; imports and explicit qualification settle references or report ambiguity. |
| Imported alias and macro hygiene | Renaming preserves declaration identity; a convenience macro retains its intended definition-site binding under caller shadowing. |
| Context separation | Reused local spellings in existing instance contexts do not mix instances or evidence. |
| Known true, known false, unknown | The same checked proposition gets the appropriate judgment from each explicit fixture context. |
| Claim is not evidence | Adding or repeating a page claim does not, by itself, establish it. |
| Requirement is not evidence | Requiring `Active(panel_a)` does not make it true; a violating situation remains representable and is reported. |
| Repeated content | Two occurrences retain separate source links even when their proposition content is shared. |
| Guard preservation | `unless` is interpreted with its guard or explicitly incomplete; the unguarded meaning is never substituted. |
| Raw/imported input | Unknown IDs, wrong kinds, missing required context, and unsupported versions fail at ingestion despite a claimed checked status. |
| Serialization | A valid round trip preserves semantic references, roles, occurrences, and context, with no silent promotion to evidence. |
| Stale or inconsistent context | Stale judgments are refused/recomputed; contradictory premises are reported explicitly rather than presented as ordinary confirmation. |
| Graph consumer | The graph links to the correct instance and source occurrence and distinguishes semantic outcome from incomplete analysis. |

Use existing declared context support for the context-separation case. If it
cannot represent nested assemblies yet, distinct explicit fixture contexts are
sufficient; implementing a new assembly hierarchy is outside scope.

For known migration divergences, use the intended semantics and independent
models to establish the expected result. Preserve recorded goldens as references
and explain intentional differences. Do not regenerate goldens merely to hide a
failure or copy a legacy omission into the new path.

## Delivery sequence

1. Map the existing declaration, instance, phrase, proposition, occurrence,
   judgment, and graph boundaries. Identify what already satisfies this order.
2. Define the smallest compatible checked-construction/ingestion contract and
   implement it with the fixture language and Materials instances.
3. Connect the actual Markdown reader to that contract, including resolution,
   hygienic references, diagnostics, and coverage/completeness.
4. Carry the result through evaluation and one existing graph view.
5. Complete the acceptance cases and relevant existing consumer/regression checks.
6. Document the public API, supported sentence fragment, identity lifetime,
   source/role/context model, and exact commands to reproduce the example.

Do not expand this order into general English understanding, a full occurrence
type system, proof of arbitrary requirement consistency, a new authorization
system, KiCad synchronization, the remaining Mojo migration, or general compiler
correctness. Occurrence typing and additional logical forms can build on this
boundary later. Existing supported constructs must continue to work.

## Definition of done

- A reproducible example compiles actual Markdown through the existing Rhombus
  route into checked content, distinct source occurrences, contextual judgments,
  and a consumable graph record/view.
- The positive and negative acceptance cases pass, with no silently dropped
  semantic clauses and no claim or requirement proving itself.
- Relevant existing checks pass; any unavailable external-tool checks are named
  explicitly and are not reported as passing.
- Documentation includes exact run/test commands and a short explanation of how
  another language module supplies vocabulary through the same boundary.
- The completion report lists changed files, test results, intentional semantic
  differences, and remaining limitations. No unrelated migration or deletion is
  needed to demonstrate completion.

## Language references

- [Rhombus identifiers, scopes, and binding spaces](https://docs.racket-lang.org/rhombus-model/id-model.html)
  defines the distinction between lexical binding and syntactic spaces.
- [Typed Racket occurrence typing](https://docs.racket-lang.org/ts-guide/occurrence-typing.html)
  describes refinement from predicate checks; it is a later capability, distinct
  from the name resolution and argument checking required here.
