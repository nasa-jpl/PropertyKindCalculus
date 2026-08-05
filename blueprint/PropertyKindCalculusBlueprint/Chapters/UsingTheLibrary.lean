import Verso
import VersoManual
import VersoBlueprint
-- The directives that render the generated tables.
import PropertyKindCalculusBlueprint.IndexTables
-- The worked examples, so the rendering-family indexes below have real occurrences to list: the
-- annotations are *used* in `Examples`, not in the core spine, and an index of an unimported
-- namespace is an empty table.
import PropertyKindCalculus.Examples
import PropertyKindCalculus.DocGenMath
-- Chapters holding the blueprint nodes some rows link to.
import PropertyKindCalculusBlueprint.Chapters.Spine
import PropertyKindCalculusBlueprint.Chapters.DedicatedKind

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PropertyKindCalculusBlueprint
open PropertyKindCalculusBlueprint.IndexTables

#doc (Manual) "Using the library: annotations and generated indexes" =>

The preceding chapters develop the calculus. This one is about *working in it*: the annotations an
author writes, what each one changes, and the indexes the library generates from them.

Three things cannot be inferred from a definition and so must be stated by its author.
*Where the calculus is left* — the one place two kinds genuinely meet, the plumbing that must drop
to the carrier, the point at which a kinded value becomes a naked one. *How a definition should
read* — the notation, the constants, the intermediate bindings a rendered equation should keep.
*What an external document says* — which requirement a theorem discharges, which clause of Dybkær or
VIM a definition formalizes. Each is a family of annotations below.

The distinction that matters most is between the first family and the other two. `@[kindCrossing]`
is not documentation: `#kind_boundary_audit` fails the build on a boundary site that carries no
tier, so the annotation *discharges an obligation* about the code, in the way a proof discharges one
about a proposition. `@[pkc_math_symbol]` changes only how something reads. The *Enforcement*
column below draws that line for every annotation at once.

Everything in the *Generated indexes* section at the end is computed from the environment when this
chapter is built. No row is maintained by hand, so a renamed declaration is a build error rather than
a stale table.

# The annotations at a glance

:::pkc_annotations
:::

# Where the calculus is left — the boundary family

A kind crossing must be *authored*. The calculus will not infer that two kinds may meet, and the
audit will not accept that they did without being told. That is the whole design: the set of
authored crossings is a closed, enumerable statement of where the type discipline is deliberately
set aside, in the way `#print axioms` is a closed statement of what a proof rests on.

The audit detects a boundary structurally, not textually. A grep cannot see through `⟨…⟩`
constructor sugar, structure-eta projections, or the `match_N` and `_proof_N` auxiliaries Lean lifts
out of a definition — and it cannot tell a parity *theorem about* `.magnitude` (legitimate, a
statement in `Prop`) from a compute body that exits the calculus (a defect). `#kind_boundary_audit`
walks the environment instead, and reports every declaration that constructs or projects a
registered carrier.

## `@[kindCrossing]` — an authored crossing

The one carrier-level place two kinds genuinely meet. The kinds are stated in the signature; the
mint or erasure inside is the crossing's mechanism, reviewed once.

```
/-- A tagged crossing minting the probe output kind. -/
@[kindCrossing]
def probeCrossing (x : Float) : Quantity outputKind Float := ⟨x⟩
```

*In the InfoView.* Nothing changes on the declaration itself. The effect is on the audit:
`#kind_boundary_audit` prints one line per boundary-active declaration, and the tier tag is what
distinguishes a sanctioned site from a violation.

```
boundary audit:
[kindCrossing] …probeCrossing — mints: outputKind
[carrierVocab] …probeVocab — mints: gainKind
[kindEmission] …probeEmission — erases (emission-only)
⚠ UNTAGGED …violationSite — mints: outputKind
```

The last line is the point. An untagged mint is reported as a violation, and because the report is
pinned with `#guard_msgs` in an indexed probe, a *new* interior boundary fails the build — the same
discipline by which a pinned axiom profile catches a proof silently relocated behind a `sorry`.

*In the generated indexes.* Every tagged site appears in the kind-crossing table with the kinds it
mints, taken from the audit's own walk so the two cannot disagree.

## `@[carrierVocab]` — a carrier-vocabulary exception

Representation plumbing for an operation the kind algebra does not name: a branchless minimum, a
square root on the complex carrier, a `map` over a coefficient table. Kind-preserving by
construction, which is what distinguishes it from a crossing.

```
/-- A carrier-vocabulary exception on the probe kinds. -/
@[carrierVocab]
def probeVocab (a b : Quantity gainKind Float) : Quantity gainKind Float :=
  ⟨min a.magnitude b.magnitude⟩
```

## `@[kindEmission]` — a genuine emission boundary

Where a kinded value legitimately becomes a naked one for a consumer outside the calculus: a deploy
driver, a tape recorder, a serializer.

```
/-- An emission boundary out of the probe world. -/
@[kindEmission]
def probeEmission (x : Quantity outputKind Float) : Float := x.magnitude
```

## `@[kindCarrier]` — teaching the audit a new carrier

The audit recognizes a boundary as an application of a *carrier structure*'s constructor or
first-field projection. `Quantity` and `CertifiedQuantity` are built in; a downstream layer
registers its own — soil-moisture-model registers its `DedicatedQuantity`, which carries a
`DedicatedKind` rather than a `KindOfProperty`.

```
/-- A toy single-field carrier, standing in for the model's `DedicatedQuantity`. -/
@[kindCarrier]
structure Tagged (k : KindOfProperty) (R : Type) where
  magnitude : R
```

Registering a carrier is the single opt-in that also earns a layer the two *structural* indexes: the
kinded-record and kinded-operation tables recognize a structure or definition by whether a
registered carrier appears in its fields or its result type. A layer therefore cannot register for
the audit and be missed by the indexes, or the reverse.

:::pkc_index "carriers"
:::

*Why the crossing table is not here.* The core spine has no kind crossings, and that is a fact
about what the spine *is* rather than an omission: a crossing is where a model meets a measurement,
so crossings live downstream. The populated table — twenty-three sites, with the kinds each one
crosses — is in soil-moisture-model's technical reference. This chapter's boundary examples come
from the validation probe that pins the audit's behaviour.

# How a definition reads — the rendering family

`@[pkc_math]` renders a `Quantity` definition to LaTeX and writes it into that declaration's
*own docstring*. Nothing else in the toolchain has to know: doc-gen4 typesets the docstring with MathJax
and the InfoView renders the same markdown on hover, so one annotation reaches both surfaces.

Every rendering is *faithful* — it denotes exactly what the definition computes. Substitution is
delta-expansion and keeping a `let` is a naming choice; neither asserts algebra the definition does
not perform. The full policy, and the escape hatch for the cases it cannot serve, are in
`RENDERING.md`.

## `@[pkc_math]` — render this definition

```
/-- The vegetation attenuation `τ = exp(−2·b·ndvi)`, kind `attenuationK`. -/
@[pkc_math]
def attenuationQ (cfg : AvsConfig α) (b : Quantity paramB α)
    (ndvi : Quantity vegetationIndex α) : Quantity attenuationK α := …
```

*The effect*, appended to that declaration's docstring and typeset on its doc-gen4 page:

$$`\tau = e^{-2\,b\,\mathrm{NDVI}}`

Two clauses control the shape. `keeping` binds a definition's `let`s as named auxiliary equations
below the main one instead of inlining them — right when a model shares one subexpression across
several outputs, where inlining both explodes the LaTeX and hides the structure the author wrote.
`substituting` adds a *derivation*: one further equation per clause, each inlining the named
helpers, so a reader sees the equation as written and then the same equation expanded.

## `@[pkc_math_symbol]` — fix the notation

Overrides every naming heuristic for one token.

```
attribute [pkc_math_symbol "n_{d}"]  MironovNK.nd
attribute [pkc_math_symbol "m_{vt}"] MironovNK.mvt
```

This is not always cosmetic. The rendering heuristic maps a Greek-letter *spelling* to its letter, so
a refractive-index field named `nu` would typeset as $`\nu` — an angular frequency. Notation stated
once, on the field, wins over every heuristic, and the index below is therefore a table of the places
where a heuristic was deliberately overruled.

:::pkc_index "pkc-math-symbol" (scope := PropertyKindCalculus.Examples)
:::

## `@[pkc_math_config]` — a configuration type

A projection of an ordinary structure renders as a function applied to its receiver:
$`\mathrm{two}\left(\mathrm{cfg}\right)`, which is the field name stripped of the type it belongs to
plus a spurious application. Tagging the structure makes its projections render as the qualified
constant $`\mathrm{AvsConfig.two}` instead, with the configuration value elided.

```
@[pkc_math_config]
structure AvsConfig (α : Type) where
  two : Quantity pureNumber α
```

The type must opt in: a blanket "drop the receiver" rule would wreck `Prod.fst` and `Prod.snd`.
Note what this does *not* do — it does not render `cfg.two` as `2`, which would assert something
about a `def` parameter rather than report what the definition computes.

:::pkc_index "pkc-math-config" (scope := PropertyKindCalculus.Examples)
:::

## `@[pkc_math_transparent]` — a notational wrapper

Marks a wrapper the renderer should see through, so the wrapped term is rendered in place of a call
to it. The carrier's numeral injection is the motivating case: without this, every literal in a
rendered equation appears wrapped in a helper nobody wants to read.

:::pkc_index "pkc-math-transparent" (scope := PropertyKindCalculus.Examples)
:::

## The rendered definitions

Every `@[pkc_math]` application in the worked examples, with the clauses each requested.

:::pkc_index "pkc-math" (scope := PropertyKindCalculus.Examples)
:::

# External correspondence — the metadata family

`@[requirement]`, `@[dybkaer]` and `@[vim4]` record what an external document says about a
declaration. All three are advisory, and all three already have their own generated index: the
requirement-traceability matrix in the *Requirements* section maps every numbered requirement to the
declarations that specify, prove, implement or exemplify it, and the two correspondence tables in the
*External Cross-References* chapter map Dybkær sections and VIM clauses to this work's declarations.
They are listed in the reference table above for completeness and are not duplicated here.

# The generated indexes

## Kinds and their algebra

The column that earns this table is *Algebra*. A kind's authored edges are the complete statement
of what may be done with it — multiplied by what, divided into what, raised to what power — because
the calculus infers none of them. A kind whose Algebra cell is empty supports no arithmetic at all,
and being able to see that is the point.

:::pkc_index "kinds" (scope := PropertyKindCalculus.Examples)
:::

## The ontology

The Dybkær spine is inhabited by ordinary definitions, so nothing marks them as a family: the
criterion is simply "a constant whose type is that structure". The dedicated-kind table renders each
one as the `System — Component ; kind-of-property` triple it is, cross-linked to the system and
component tables rather than repeating their identity strings.

:::pkc_index "systems" (scope := PropertyKindCalculus.Examples)
:::

:::pkc_index "components" (scope := PropertyKindCalculus.Examples)
:::

:::pkc_index "dedicated-kinds" (scope := PropertyKindCalculus.Examples)
:::

Two dedicated kinds that share a kind-of-property are held apart only by their system and component,
and the *Theorems* column lists what proves it. A dedicated kind with no distinctness theorem is
one that nothing yet relies on separating.

The examination chain needs no annotation either: a method is based on the principle it cites and a
procedure on the method it cites, so `BasedOn` is structural, and the table below is the generating
edges of the `Refines` closure.

:::pkc_index "examinations" (scope := PropertyKindCalculus.Examples)
:::

## Kinded records and operations

Neither table needs an annotation to decide membership. A *kinded record* is a structure at least
one of whose fields is a registered carrier applied to a kind; a *kinded operation* is a definition
whose result type is one. `@[kindCarrier]` is the only opt-in, and it is already required for the
audit.

For a record the useful column is the notation, because the fields are where `@[pkc_math_symbol]`
attaches and a rendered equation's readability is decided.

:::pkc_index "records" (scope := PropertyKindCalculus.Examples)
:::

For an operation it is the kind signature together with the authored crossings its body routes
through — which makes the row a contract rather than a signature, since an operation that changes
kind must reach a sanctioned crossing to do it.

Field projections are excluded. `MironovNK.nd` satisfies the criterion literally, its result type
being `Quantity nIndexKind α`, but it is the record's accessor rather than an operation on kinds and
is already a row of the table above.

:::pkc_index "operations" (scope := PropertyKindCalculus.Examples)
:::
