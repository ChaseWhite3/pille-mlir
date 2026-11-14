# Work order for shared semantics annotations and graph views in Closer

Recipient: the Closer implementation AI, including the CCG-GNN consumer integration.

Organize Closer around shared semantic identities and checked representations.
Use Rhombus annotations as one interface to those representations. Generate
bounded graph neighborhoods and registered views from the same declarations and
records. Preserve the existing curved SVG wiring graph, ports, Describe workflow,
source navigation, and review history while replacing duplicated validation and
fragile renderer integration.

Deliver a working implementation, public synthetic fixtures, tests, and updated
architecture documentation. A schema proposal or producer-only export does not
complete this order: the existing viewer must consume the new boundary.

## 1 Scope and starting point

Primary checkout: `/Users/chasewhite/Documents/gitStuff/anote-java-clojure`.
Consumer checkout: `/Users/chasewhite/gitStuff/ccg-gnn`.
Supporting dependency: `/Users/chasewhite/gitStuff/pille`.

This document is stored in the Pille checkout for handoff. Implementation belongs
in Closer and its graph consumer; make a Pille change only for a demonstrated
missing reusable primitive. Inspect current repository instructions, working
trees, package contracts, and callers first. Preserve others' uncommitted work.
Keep frozen CCG-GNN packages, review answers, and recorded goldens unchanged;
produce new packages for changed sources or presentation assets.

The earlier [checked proposition work order](/Users/chasewhite/gitStuff/pille/CLOSER_PROPOSITION_WORK_ORDER.md)
defines the semantic foundation. This order incorporates that slice and extends
it with annotation cleanup, neighborhoods, and actual viewer integration. Reuse
completed work; do not implement the foundation twice.

Work within the active Rhombus migration. The new path must not introduce a Mojo
build/runtime dependency or require offline depccg preparation. Existing backend
dependencies used for a selected check may remain. Do not fold the rest of the
Mojo migration, reports, or unrelated commands into this task. Do not
publish, rewrite history, or delete unrelated features.

### Foundations already present

Verify these starting points against current code before editing:

| Area | Existing code and responsibility |
| --- | --- |
| Kind annotations | [language.rhm](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-lang/language.rhm:194) generates a namespace and annotation for each kind. The predicate currently checks a map's kind string and accepts state records by design; static information is empty. |
| Formula checking | [formulas.rhm](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-lang/formulas.rhm) and [rules.rhm](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-lang/rules.rhm) contain typed formulas, compatibility checks, expansion, and source origins. |
| Page elaboration | [phrase/space.rhm](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-exports/closer_exports/phrase/space.rhm), [compile.rhm](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-exports/closer_exports/compile.rhm), and [requirements.rhm](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-exports/closer_exports/requirements.rhm) already connect pages to records and judgments. |
| Assemblies and Materials | [assembly/model.rhm](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-exports/closer_exports/assembly/model.rhm), [assembly/declare.rhm](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-exports/closer_exports/assembly/declare.rhm), and [assembly/materials.rhm](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/closer-exports/closer_exports/assembly/materials.rhm) already describe models, instances, interfaces, constraints, controls, and composition. |
| SVG wiring renderer | [refinement.py](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/mojo/exports/refinement.py:2263) contains the canonical GRAPH_JS; [graph_js_lift.py](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/mojo/exports/graph_js_lift.py) generates its Mojo copy. |
| Editor host | [graph.cjs](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/tools/vscode-annotate/src/graph.cjs) hosts the generated graph and bridges source selection and focus. |
| Circuit renderer | [circuit.js](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/tools/vscode-annotate/media/circuit/circuit.js) already uses Cytoscape for circuit composition, states, and contract inspection. It is a separate presentation adapter. |
| CCG-GNN focus and Describe | [wiring_focus.py](/Users/chasewhite/gitStuff/ccg-gnn/src/ccg_gnn/evaluation/wiring_focus.py), [wiring_focus.js](/Users/chasewhite/gitStuff/ccg-gnn/src/ccg_gnn/evaluation/wiring_focus.js), and [wiring_describe_model.js](/Users/chasewhite/gitStuff/ccg-gnn/src/ccg_gnn/evaluation/wiring_describe_model.js) extend the captured renderer with neighborhoods, anchored cards, and routed connections. |
| Navigation and arrangements | [wiring_navigation.js](/Users/chasewhite/gitStuff/ccg-gnn/src/ccg_gnn/evaluation/wiring_navigation.js), [wiring_modes.js](/Users/chasewhite/gitStuff/ccg-gnn/src/ccg_gnn/evaluation/wiring_modes.js), and [wiring_arrangement.js](/Users/chasewhite/gitStuff/ccg-gnn/src/ccg_gnn/evaluation/wiring_arrangement.js) already manage selection history, mode state, and snapshot-specific positions. |

Read the current [type and instance inspector contract](/Users/chasewhite/gitStuff/ccg-gnn/docs/type-instance-inspector.md),
[graph integration requirements](/Users/chasewhite/gitStuff/ccg-gnn/docs/safetynet-graph-integration-work-order.md),
and [Rhombus MLIR contract](/Users/chasewhite/Documents/gitStuff/anote-java-clojure/docs/rhombus-mlir-contract.md).
Older documents may describe incomplete migrations; inspect callers rather than
assuming every named component still needs porting.

## 2 Required author experience

Provide this journey in one coherent graph experience:

1. Select a requirement about panels becoming active.
2. Inspect its interpreted proposition and the definition of Active.
3. Show the applicable Materials instances; choose one explicitly.
4. Inspect that instance's assembly, parts, interface, and behavior.
5. Inspect the requirement judgment at a selected moment and the evidence and
   assumptions supporting it.
6. Follow the exact source occurrence and return through navigation history.
7. Open Describe for a particular operation use, retain its draft, visit another
   view, and return to the same use and draft.

The selected instance, context, revision, and relevant moment must remain visible.
Changing the view must not silently change the subject or the evidence being
inspected. A definition with several uses opens a chooser or group. A view with
no representation of the selection explains that absence and retains the anchor.

## 3 Shared semantic model

Introduce the smallest shared descriptor and lookup boundary that existing
representations lack. Keep separate modules for declarations, instantiated
models, propositions, occurrences, and judgments; do not create a universal map
whose fields are interpreted differently by every consumer.

```text
Rhombus declarations, imports, and convenience macros
                  |
       resolved semantic descriptors
                  |
    +-------------+---------------------+
    |             |                     |
annotations   proposition checks   view and operation metadata
                  |
Materials + page elaboration + selected context
                  |
checked instances, propositions, occurrences, and judgments
                  |
         typed neighborhood queries
                  |
      existing graph presentation adapters
```

### Identity and compatibility

- Keep declaration, model-definition, instance, proposition, source-occurrence,
  and judgment identities distinct. A shared circuit definition instantiated
  twice creates two instance contexts.
- Preserve existing canonical identities through adapters. Imported aliases and
  display names are not new declarations. Same-spelled declarations from different
  modules must remain distinguishable.
- Resolve lexical bindings during expansion, then retain explicit identities in
  exported records. Do not reconstruct meaning from lowercase strings, printed
  syntax, source filenames, or a renderer's node labels.
- Centralize kind compatibility and declared-parent traversal. Retain small
  representation-specific adapters where necessary. Handle parent cycles and
  unresolved parents explicitly; sharing a family does not make siblings
  interchangeable.
- Define identity lifetime and revision compatibility. Reliable identity within
  a build and its exported snapshot is required. Arbitrary cross-edit identity
  recovery is not required. Changed revisions require an explicit correspondence
  or a stale/unavailable result, never a guessed match by offset or spelling.
- Keep source occurrences separate: several sentences may express one proposition,
  and generated semantic entities may have no authored occurrence. Preserve source
  revision, coordinate convention, and exact span when one exists.

### Meaning and judgments

Declarations define vocabulary and signatures. Materials introduce instances and
explicit initial facts. Requirements state obligations. Page claims assert content.
Judgments evaluate content using a specified context and evidence.

Successful construction means a term is well formed. It does not mean a requirement
is satisfied or an action is permitted. A claimed or required proposition must not
be inserted as an assumption merely to establish itself. Keep known true, known
false, and unknown distinct from incomplete interpretation, inconsistent premises,
unsupported analysis, and tool failure.

Keep semantic descriptions inspectable. Existing executable predicates may remain
implementation hooks, but an opaque function is insufficient as the sole source
for graph meaning, serialization, or solver translation. Retain explicit signature,
role, constraint, and provenance descriptors. Only supported semantic fragments
receive executable checks or lowering; other fragments remain explicitly unsupported.

## 4 Annotation cleanup

Use annotations to expose shared validation and useful static information. Do not
rebuild a type checker, page parser, or theorem prover inside annotation macros.

1. Preserve the existing public kind annotation's behavior, including its use for
   state records, unless a separately documented compatibility migration covers
   all callers. Introduce an explicitly named checked-instance annotation for
   validated instance references; choose idiomatic final syntax.
2. Prefer `annot.def` for reusable fixed annotations. Use `annot.macro` when syntax
   parameters or composition require it. Reuse annotation parsing through
   `annot_meta.Parsed`; it does not replace the existing phrase/proposition spaces.
3. Generate annotations from the same descriptor identity used by formula checks
   and views. An instance predicate checks the invariant of the validated value.
   It must not secretly read files, parse Markdown, or invoke SMT.
4. Put raw-input resolution in explicit checked constructors/converters. Validate
   schema version, identities, kinds, and membership in the supplied context.
   Preserve detailed diagnostics and provenance. Unknown references and forged
   kind tags must not become valid instances.
5. Use immutable checked values or another representation that preserves the
   validated invariant. A changed model snapshot requires revalidation. Avoid
   treating a previously checked mutable map as permanently trusted.
6. Supply static information only with a concrete consumer, such as a checked
   accessor or expansion-time signature lookup. Document the consumer and test it.
   Static information is not serialized evidence or a domain proof.
7. Treat deserialization as an entry boundary. A payload's `checked`, typing, or
   judgment fields do not certify themselves. Recheck imported references and
   bind reusable results to their exact model/context revision.

Start with instance references and predicate application. Then remove duplicate
checks only from callers now covered by the shared invariant. Keep a cleanup
ledger: former check, replacement rule/API, migrated callers, and validation that
makes deletion justified. Do not wrap every existing function in a new annotation
without removing any duplicated responsibility.

## 5 Typed relationships and olog structure

Represent relationships independently of drawing geometry. A relationship
descriptor needs an identity, endpoint categories, direction, multiplicity where
known, interpretation, and provenance. Separate declaration-level signatures from
instance-level edges and from claims about those edges.

At minimum, distinguish these families where current records supply them:

| Family | Examples and interpretation |
| --- | --- |
| Definition | Declares, has predicate, has parameter, declared parent kind |
| Instantiation | An instance uses a model definition; an occurrence invokes an operation |
| Composition | Contains, has boundary port, terminal membership in a net |
| Requirements | Applies to, refers to proposition, refines another requirement |
| Behavior | Declared precondition/effect, transition, actual modeled step occurrence |
| Evidence | A judgment uses an assumption/observation; an occurrence has source provenance |
| Compatibility | One operation can supply a state another accepts; this alone is not observed support or a dependency |

A visual edge may summarize several semantic relations. Give it a presentation ID
and the underlying relation IDs so it can expand and explain itself. Crossing
wires, spatial proximity, matching labels, and visual grouping create no semantic
relationship. A declared effect of a blocked step is not an observed effect.

Use the Definitions view to expose olog types, functional aspects, and declared
path equations where available. A reverse traversal of a functional aspect is a
query that may return many instances. Represent nonfunctional relationships using
explicit relation/membership records when exposing them as olog structure.

Do not label every UI edge an olog arrow or every view mapping a functor. Such a
claim requires specified categories, mappings, and preservation of composition
and equations. General categorical proof machinery or a formal topology is not
required. If the existing model exposes a path equation, show its declared versus
checked status; never invent an equation because two paths look similar.

## 6 Bounded neighborhood queries

Implement a shared query contract over the semantic records. Put relation meaning
and reference resolution in this boundary rather than independently reimplementing
them in each renderer. A browser may execute a projection of validated snapshot
data; it must use the same relationship definitions and conformance fixtures.

A request includes anchor identity or identities, model/capture revision, assembly
or procedure context, view, allowed relationship families, traversal direction,
depth, and node/edge budget. Run and moment are required only for queries whose
meaning depends on them.

A response includes nodes, typed relationships, reason/path for inclusion,
unresolved references, and explicit completeness information. Distinguish an empty
complete result from truncated, unsupported, or uncaptured data. Include omitted
counts only when known. Keep results deterministic for the same request and
snapshot; terminate on cycles and preserve direction and distinct occurrences.

Support widening by a relationship and expanding a summarized group. Bound the
query and rendering work to the requested neighborhood. Loading and indexing the
existing validated offline snapshot is allowed; this order does not require a
new streaming/storage architecture. Add lazy loading only if measurements justify
it. Layout filtering does not change evidence completeness or solver assumptions.
Hidden entities can still matter to a judgment, and its explanation must retain
those references.

## 7 Registered views and operations

Provide five views over shared identities. Reuse existing panels and renderers
instead of duplicating their data ownership.

| View | What it reveals |
| --- | --- |
| Definitions | Kinds, predicates, signatures, declared relationships, formulas, available olog facts, documentation, and examples |
| Composition | Materials instances, reusable models, contained parts, interfaces, ports, and nets |
| Requirements | Obligations, applicability, refinement links, interpreted content, and judgment summaries |
| Behavior | Operations, preconditions/effects, transitions, guards, and selected procedure occurrences/moments |
| Evidence | Assumptions, observations, derivations, solver results, source occurrences, and missing support |

A view registration declares its stable ID, applicable categories, relationship
families, context needs, selection-mapping function/contract, renderer adapter,
and available named operations. Extend the existing graph/schema metadata rather
than creating an unrelated registry keyed by display names.

Rhombus language modules provide declarative capabilities. Known browser/host
handlers implement rendering and commands; exported data must not contain arbitrary
JavaScript to execute. Modules can supply documentation, units, ranges, control
hints, and operation signatures. These hints configure controls; they do not prove
an operation is permitted or that a constraint holds.

Separate read-only navigation from model changes. A domain command identifies its
operation, operands, expected context/revision, and arguments. Dispatch through
existing validation/execution boundaries and return the changed revision plus
affected checks. Unsupported handlers are visibly unavailable. Navigating, moving
boxes, or changing a view must not edit Materials, grant approval, or run equipment.

Connect one existing safe model-edit operation, such as a parameter change, through
this dispatch boundary. Use a local synthetic model; no physical-device operation
is required. Mark affected judgments stale for the changed revision and distinguish
the pending check from its eventual result. Retain the earlier judgments and their
evidence under the earlier revision. Keep existing Describe proposals as proposals
until applied through their established workflow.

## 8 Navigation state and cross-view correspondence

Use one navigation contract shared by the graph host and its view adapters.
Conceptually, a destination contains:

```text
selected semantic identities and original anchor
view and bounded neighborhood request
assembly/procedure context and model/capture revision
run, moment, and source occurrence when relevant
inspector selection
```

Keep camera, pinned positions, collapsed groups, and display filters in associated
presentation state, scoped to the relevant view and snapshot. Preserve this state
through back/forward where applicable. Presentation changes must not change
semantic digests, evidence identity, or authored content.

Selection mapping must return one of three explicit results:

- **One correspondence:** navigate directly, preserving the original anchor and
  showing the relationship followed.
- **Several correspondences:** show a group or chooser with distinguishing scope,
  member, occurrence, or moment information. Never choose the first item silently.
- **No correspondence:** retain the anchor and explain whether the target view is
  inapplicable, uncaptured, unsupported, or empty in this context.

For example, Definitions may highlight Panel while the original anchor remains
panel_a. Going back to Composition returns to panel_a, not an arbitrary Panel.
Opening an operation definition with ten uses does not pick one invocation. Two
instances of a reusable assembly retain distinct local parts and evidence.

Separate these actions in the interface and event API:

1. Follow a named semantic relationship.
2. Enter or leave a containing assembly/context.
3. Switch the view of the current focus.
4. Change revision, run, or moment explicitly.
5. Change camera/layout or neighborhood display only.

Provide meaningful breadcrumbs and shareable destinations using existing hash or
host routing conventions. Validate restored IDs against the named snapshot. A
missing snapshot or stale entity produces an explicit unavailable destination;
do not silently apply a bookmark to the latest model.

Retain browser/editor back and forward behavior, keyboard navigation, and source
focus. Avoid duplicate history entries from nested selection events. Restore an
open inspector and the exact repeated member/operation occurrence.

Draft contents must remain outside navigation history. Preserve Describe drafts
under their established occurrence, operands, context, and evidence identities.
Changing views or using Back must neither lose a draft nor reassign it to another
member. Changed evidence does not inherit an old review answer. Keep navigation,
draft persistence, and semantic edits as separate responsibilities.

## 9 Preserve and modularize the actual renderers

Preserve the current SVG wiring presentation, including:

- Curved overview connections, typed port shapes, filled/open markers, labels,
  existing color meaning, and selection/hover inspection.
- Overview to focused use to Describe transitions.
- Orthogonal Describe routing, annotation cards, timing connections, and crossing
  bridges. A bridge means wires cross without connecting.
- Zoom, pan, pinned arrangements, source outlines, exact occurrence/member
  selection, and usable narrow layouts.

The circuit view may continue to use its existing Cytoscape adapter. Share semantic
identity and navigation through the contract instead of forcing both renderers
into one library or recreating circuit layout in SVG.

Extract the canonical wiring JavaScript from its embedded Python string into
ordinary source modules with an explicit mount/update/dispose interface and host
services for source reveal, navigation, and command dispatch. Choose one canonical
asset owner and a reproducible packaging/import path for the other checkout; do
not maintain two hand-edited copies of the renderer.

Keep thin compatibility wrappers for the generated graph page, offline bundle,
and VS Code webview. Existing embedded records and sidecar records remain readable
through explicit versioned adapters. Preserve content-security-policy handling
and source-message behavior. The new Rhombus producer can package these assets
without compiling Mojo.

Replace the current integration's exact JavaScript/HTML string matching and
global-function wrapping with supported entry points and events, incrementally.
In particular, migrate the responsibilities currently carried by wiring_focus.py,
wiring_modes.js, and wiring_navigation.js. Remove the obsolete live patching path
only after its supported callers use the new interface. Archived generated HTML
is historical evidence and stays unchanged.

Navigation contracts do not prescribe pixel geometry. Keep semantic IDs separate
from visual-node IDs so one entity can appear in multiple places. Every displayed
port/edge/card maps back to its descriptor or occurrence; no semantic state is
recovered by scraping SVG attributes or parsing its label.

## 10 Public demonstrations

### A Complete panel journey

Use a small public language with Panel, an unrelated kind, an Active predicate or
equivalent existing state formula, and explicit example state conditions. Declare
at least two panel instances and a reused model with locally named parts, using
the existing assembly facilities. Keep the fixture small and make all facts
declared or synthetic.

Include a requirement, page claims, operation uses, and known-true, known-false,
and unknown contexts. Reuse supported temporal forms if present; this fixture
does not require a new temporal logic. Demonstrate the journey in section 2
through all five views, exact source navigation, and Describe draft restoration.

The definition inspector must show the selected binding's meaning, signature,
structural relations, examples/counterexamples, source, and applicable instances.
Show unavailable metadata honestly. Reviewed interpretation and verification
outcome remain separate.

Include one repeated operation or repeated member whose source line is shared
but whose occurrence identities differ. Include a malformed/unsupported clause
and show that it remains visible with incomplete analysis. If `unless` is already
supported, verify its semantics instead of reclassifying it as unsupported.

### B Extension and existing circuit view

Use a second small module with different names, imported aliases, and a supported
operation, preferably adapting an existing pump fixture. It must use the same
annotation, neighborhood, view, and command interfaces without domain-name
branches in the shared renderer or navigation code. A custom domain-specific
renderer is allowed only as an explicitly registered adapter.

Connect an existing synthetic assembly/circuit fixture through the Composition
view and its current renderer. Demonstrate a selected instance surviving the
cross-view transition and one safe local parameter-edit command followed by
validation/rechecking. KiCad source reveal may be demonstrated when captured
source data exists; creating a new KiCad synchronization implementation is not
required.

## 11 Acceptance matrix

Extend existing tests at the owning boundary. The following are required observable
outcomes; equivalent cases may share a fixture. Keep independent semantic expected
answers alongside differential checks. Legacy omissions are not the desired result.

| Area | Case | Expected result |
| --- | --- | --- |
| Compatibility | Existing kind annotation on its documented inputs | Behavior preserved, including state records; no silent change to instance-only meaning. |
| Checked values | Valid instance, wrong kind, raw kind tag, unknown ID | Valid reference accepted; others rejected with the relevant diagnostic. |
| Identity | Same-spelled declarations, import alias, caller shadowing | Distinct declarations stay distinct; aliases preserve identity; macros retain intended lexical bindings. |
| Parent kinds | Child, sibling, missing parent, parent cycle | Shared compatibility follows declared ancestry and reports invalid/unknown ancestry explicitly. |
| Context | Two instances reuse the same local part name | Selection, facts, requirements, and drafts remain scoped to the chosen instance. |
| Ingestion | Supplied checked/typing/judgment metadata | Validated against the receiving environment; no self-certified acceptance. |
| Static information | New annotation's documented consumer | Consumer uses the provided information correctly; incorrect value construction still fails. |
| Proposition | True, false, unknown, unsupported, inconsistent context | Outcomes remain distinct from completeness/tool status; a claim or requirement never proves itself. |
| Provenance | Two sentences express one proposition | Two occurrences and exact source spans remain navigable. |
| Grammar | Guard, negation, or unsupported semantic clause | Meaning preserved or marked incomplete; no successful interpretation with silently removed clauses. |
| Relationships | Compatibility, containment, refinement, evidence | Correct edge families and explanations; no conflation of candidate connections with actual support. |
| Neighborhood | Cycle, large fan-out, inverse traversal | Deterministic bounded result, honest truncation, all returned endpoints scoped correctly. |
| Missing data | Empty result versus absent capability/capture | Distinct visible status; absence of capture does not become a negative fact. |
| View mapping | Zero, one, several correspondences | Explanation, direct mapping, or chooser respectively; original anchor retained. |
| Five views | One panel selected across all views | Identity/context/revision retained; different representations explained. |
| Repetition | Two uses share one source line/operation | Exact member and invocation survive navigation and inspection. |
| History | Back/forward through focus, source, Describe, and another view | Selection, inspector, and relevant presentation state restore without duplicate navigation events or draft loss. |
| Revision | Old bookmark, evidence, arrangement, or review | Exact snapshot used, explicit compatibility mapping applied, or stale/unavailable shown; no silent latest-version substitution. |
| Presentation | Move boxes, zoom, filter, cross wires | No change to semantics, evidence digest, approval, or connection topology. |
| Commands | Read-only selection and safe parameter edit | Selection has no domain effect; edit validates operands/revision and invalidates affected judgments before rechecking. |
| Extension | Second language module | Shared interfaces work without edits keyed to its domain names. |
| Packaging | Offline viewer and VS Code host | Both use the canonical assets and supported record adapters; source reveal and selection work. |
| Versions | Supported prior record and unknown version | Deliberate compatibility for supported inputs; explicit refusal for unsupported versions. |

Run focused Rhombus tests and affected existing compiler/record checks. Exercise
CCG-GNN's existing graph-navigation, focus, modes, Describe, per-member, and
arrangement checks where affected. Run the editor's relevant host/shape tests.
Confirm exact commands from current package scripts rather than guessing them.

Perform an actual browser/webview pass for arrow/port alignment, curve and crossing
appearance, labels, hover/click targets, zoom/pan, focus transitions, source reveal,
keyboard use, and a narrow viewport. DOM tests alone do not establish visual
preservation. Keep before/after screenshots and distinguish visual verification
from automated behavior tests.

Use existing snapshots to measure representative neighborhood/query/render work.
Record model size, budgets, and time to first usable focused view before and after.
Do not introduce a speculative benchmark program; investigate material regressions
in the workflows changed here.

## 12 Implementation sequence and cleanup gates

Complete these increments in order, adjusting within an increment for actual
dependencies. Report discoveries concisely and continue authorized work; do not
stop after writing an architecture proposal.

1. **Inventory and baseline.** Map existing identities, validators, annotation
   callers, schemas, view state, renderer assets, and consumer entry points.
   Capture the relevant checks and representative screenshots. Write a short
   ownership/dependency map identifying the canonical owner for each concern.
2. **Semantic and annotation slice.** Finish the checked-proposition foundation
   for the public fixture; implement shared identity/compatibility validation and
   the dedicated instance annotation. Migrate at least two real consumers and
   remove their now-redundant checks after regression cases pass.
3. **Neighborhood boundary.** Add typed relationship adapters and deterministic
   bounded queries over current records. Validate them with independent fixtures
   before using them to select rendered nodes.
4. **Renderer seam.** Extract canonical assets and expose a supported API while
   preserving the current appearance and interactions. Switch one current host,
   then the CCG-GNN integration; retain explicit compatibility for supported
   record formats while eliminating live exact-string patching.
5. **Views and navigation.** Register the five views, implement correspondence and
   shared navigation state, and connect the circuit adapter. Carry out the full
   author journey, including the safe command and Describe draft restoration.
6. **Extension, regression, and retirement.** Run the second-language fixture and
   acceptance matrix. Remove superseded validators, mode branches, wrappers, and
   generated duplicate sources only after all active callers are accounted for.
   Preserve independent semantic checks and frozen historical artifacts.
7. **Documentation and handoff.** Update architecture, extension instructions,
   record contracts, packaging instructions, and runnable examples. Report exact
   test commands and results, intentional differences, and remaining limits.

Maintain a concise cleanup ledger during implementation:

| Previous responsibility | Shared replacement | Migrated callers | Evidence permitting removal |
| --- | --- | --- | --- |
| Repeated kind/reference checks | Chosen descriptor/validation API | Actual files and functions | Positive and negative regression cases |
| Hardcoded mode/selection branching | Registered view mapping | Actual hosts and inspector paths | Zero/one/many correspondence and history tests |
| Embedded renderer plus HTML string patching | Canonical assets and supported host events | Generated page, editor host, CCG-GNN | Behavior tests and browser verification |

Fill this with actual changes. Line-count reduction is supporting information;
removing duplicated ownership and retaining correctness are the completion test.

## 13 Definition of done and limits

The task is complete when:

- One shared semantic boundary supplies annotations, checked proposition use,
  neighborhood relationships, and view metadata, with real callers migrated.
- The existing SVG viewer consumes that boundary through supported APIs and
  retains its curved arrows, ports, Describe workflow, source links, and history.
- All five views and explicit zero/one/many mappings work on the public example;
  the existing circuit adapter participates without changing selected identity.
- The second module works through the same generic interfaces.
- Annotation compatibility, semantic negative cases, context separation, raw
  ingestion, bounded queries, draft retention, and stale-state cases are covered.
- The cleanup ledger shows concrete duplicated checks and fragile integrations
  removed, rather than a new framework layered over unchanged live paths.
- Automated checks and browser verification are reported accurately. An unavailable
  required consumer/browser check is an outstanding gap, not a completed milestone.
- Current documentation identifies canonical source owners, APIs, version behavior,
  exact reproduction commands, and how a language author adds a supported concept,
  view, or operation without modifying generic dispatch by domain name.

This order does not require a new graph library, complete static type system,
general occurrence typing, arbitrary categorical equivalence proofs, automatic
extraction of semantics from opaque predicates, automatic resolution of ambiguous
English, new solver theory, full Mojo retirement, or general KiCad round-trip
editing. It must preserve existing supported capabilities while establishing the
shared boundaries described above.

Use [Rhombus annotation macros](https://docs.racket-lang.org/rhombus-meta/Annotation_Macros.html)
and [binding spaces](https://docs.racket-lang.org/rhombus-model/id-model.html) for
the language mechanisms. Use the [olog account of schemas, instances, and mappings](https://arxiv.org/html/1102.1889v2)
when describing categorical structure; keep those claims narrower than the whole
UI navigation graph.
