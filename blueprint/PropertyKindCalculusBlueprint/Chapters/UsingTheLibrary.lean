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
chapter is built, scoped to this package's own worked examples. No row is maintained by hand, so a
renamed declaration is a build error rather than a stale table.

# The annotations at a glance

Each row links to the section that explains it.

:::pkc_annotations
:::

# The commands at a glance

What the annotations *declare*, the commands *ask*. The column that matters is the last one: a
command whose answer a probe file freezes with `#guard_msgs` stops being a report about the code and
becomes part of the discipline the build enforces — a changed answer is a failed build. The three
audits are pinned that way; the reading commands are not, because their job is to be run by hand.

:::pkc_index "commands"
:::

# Where the calculus is left — the boundary family
%%%
tag := "boundary-family"
%%%

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
%%%
tag := "annotation-kindCrossing"
%%%

The one carrier-level place two kinds genuinely meet. The kinds are stated in the signature — on
the argument side as much as the result: `add` rejects a `@[kindCrossing]` declaration none of
whose arguments carries a registered carrier, because a crossing goes FROM an already-kinded
value, and a declaration with no kinded argument has nothing to cross from. The mint or erasure
inside is the crossing's mechanism, reviewed once.

```
/-- A tagged crossing minting the probe output kind from an already-kinded gain value. -/
@[kindCrossing]
def probeCrossing (g : Quantity gainKind Float) : Quantity outputKind Float := ⟨g.magnitude⟩
```

A declaration with no kinded argument at all — `probeCrossing (x : Float) : Quantity outputKind
Float := ⟨x⟩` — is rejected at the `@[kindCrossing]` line itself, with a message pointing at the
two tiers below it is actually one of: `@[kindIngest]` if something is checked on the way in,
`@[kindConst]` if it is a fixed literal.

*In the InfoView.* Nothing else changes on the declaration itself. The effect is on the audit:
`#kind_boundary_audit` prints one line per boundary-active declaration, and the tier tag is what
distinguishes a sanctioned site from a violation.

```
boundary audit:
[kindCrossing] …probeCrossing — mints: outputKind
[carrierVocab] …probeVocab — mints: gainKind
[kindEmission] …probeEmission — erases (emission-only)
[kindIngest] …probeIngest — mints: outputKind
⚠ UNTAGGED …violationSite — mints: outputKind
```

The last line is the point. An untagged mint is reported as a violation, and because the report is
pinned with `#guard_msgs` in an indexed probe, a *new* interior boundary fails the build — the same
discipline by which a pinned axiom profile catches a proof silently relocated behind a `sorry`.

*In the generated indexes.* Every tagged site appears in the kind-crossing table with the kinds it
mints, taken from the audit's own walk so the two cannot disagree.

## `@[kindIngest]` — a checked ingest mint
%%%
tag := "annotation-kindIngest"
%%%

The dual of `@[kindCrossing]`: raw, external data — a host column, a JSON blob, an env-var's text
— enters the calculus for the first time, admitted through some check (a `KindAdmissible`/
`BatchAdmissible` instance, an inline range test, a fallible parse). No argument carries a kind,
because none has been established yet — that is the entire point of an ingest boundary, and the
reason `@[kindCrossing]`'s own check must not reject it: the check performed is this
declaration's evidence, stated once, rather than presupposed.

```
/-- A checked ingest mint: a raw carrier value enters the calculus as the probe output kind. -/
@[kindIngest]
def probeIngest (x : Float) : Quantity outputKind Float := ⟨x⟩
```

## `@[carrierVocab]` — a carrier-vocabulary exception
%%%
tag := "annotation-carrierVocab"
%%%

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
%%%
tag := "annotation-kindEmission"
%%%

Where a kinded value legitimately becomes a naked one for a consumer outside the calculus: a deploy
driver, a tape recorder, a serializer.

```
/-- An emission boundary out of the probe world. -/
@[kindEmission]
def probeEmission (x : Quantity outputKind Float) : Float := x.magnitude
```

## `@[kindCarrier]` — teaching the audit a new carrier
%%%
tag := "annotation-kindCarrier"
%%%

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

# What the kind algebra rests on — the edge audits
%%%
tag := "edge-audits"
%%%

The boundary audit asks where the calculus is *left*. These two ask what it *rests on*.

A kind-level law — `ProductKind k₁ k₂ k`, a `KindMul` table entry, a `PowerKind` — is authored, not
derived. The calculus signs any ratio-scale triple its author writes, exactly as a proof assistant
accepts any axiom its author declares, and for the same reason: a claim about which physical
quantities compose to which is not something a type checker can settle. What follows from that is
not that the claims go unchecked, but that they must be *enumerable*.

`#kind_edges k` is that enumeration, per kind. It finds all three authoring styles in one scan over
constant types — named witness theorems, the `_proof_N` auxiliaries Lean lifts out of call-site
witnesses, and operator-table instances — so a reader sees every edge a kind participates in
regardless of how it was written. This is what makes the *Algebra* column of the kind tables below
worth reading: a kind whose Algebra cell is empty supports no arithmetic at all.

`#kind_dimensional_coverage ns …` then cross-checks those edges against the dimension layer, and it
is the one place an authored edge can be *refuted* rather than merely listed. Each edge's kinds are
resolved to their declared {ref "dimensioned-kind"}[dimensioned kinds] and the family's rule is
evaluated in PhysLib's `Dimension` group — products add exponents, quotients subtract, powers scale
by the rational exponent, a transcendental demands dimension one on both sides. An edge reports as:

```
[coherent]      relPermKind · relPermKind → relPermSqKind
[parametric]    pureNumber · k → k
⚠ UNDIMENSIONED angFreqKind · relaxTimeKind → dimlessKind — no DimensionedKind for: relaxTimeKind
⚠ INCOHERENT    angFreqKind · relaxTimeKind → angFreqKind
⚠ CONFLICTING   … — disagreeing DimensionedKinds for: …
```

`[parametric]` is generic vocabulary — an edge quantified over a kind variable has no fixed
dimensional content, and its instantiations are audited as their own rows. The two `⚠` verdicts that
matter are different failures: *undimensioned* is a coverage gap, an edge nobody mirrored into the
dimension layer, while *incoherent* is a genuine error, `T⁻¹ · T = T⁻¹` asserted where the group
says otherwise.

The division of labour with the curated {ref "interaction-algebra"}[interaction algebras] is worth
stating, because the two look similar and are not. This command is *total* and mechanical: it can
only affirm that an edge's dimensions balance, and every dimension-one triple balances trivially — which
is most of a soil-moisture model. An `InteractionAlgebra` is *curated*: it says which products are
physically sanctioned, which is the thing dimensional analysis discards and no walk can recover.
Coverage is checked; curation stays authored.

# How a definition reads — the rendering family

`@[pkc_math]` renders a `Quantity` definition to LaTeX and writes it into that declaration's
*own docstring*. Nothing else in the toolchain has to know: doc-gen4 typesets the docstring with MathJax
and the InfoView renders the same markdown on hover, so one annotation reaches both surfaces.

Every rendering is *faithful* — it denotes exactly what the definition computes. Substitution is
delta-expansion and keeping a `let` is a naming choice; neither asserts algebra the definition does
not perform. The full policy, and the escape hatch for the cases it cannot serve, are in
`RENDERING.md`.

## `@[pkc_math]` — render this definition
%%%
tag := "annotation-pkc-math"
%%%

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
%%%
tag := "annotation-pkc-math-symbol"
%%%

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
%%%
tag := "annotation-pkc-math-config"
%%%

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
%%%
tag := "annotation-pkc-math-transparent"
%%%

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
%%%
tag := "annotations-metadata-family"
%%%

`@[requirement]`, `@[dybkaer]` and `@[vim4]` record what an external document says about a
declaration. All three are advisory, and all three already have their own generated index: the
requirement-traceability matrix in the *Requirements* section maps every numbered requirement to the
declarations that specify, prove, implement or exemplify it, and the two correspondence tables in the
*External Cross-References* chapter map Dybkær sections and VIM clauses to this work's declarations.
They are listed in the reference table above for completeness and are not duplicated here.

# The generated indexes

*What these tables index.* Every table in this section is scoped to `PropertyKindCalculus.Examples`
— the calculus's own worked examples, which are what this package has to index. They are *not* the
soil-moisture model: that model is a separate downstream repository, and its technical reference
renders the same eight tables over its own namespaces, populated with its real kinds and crossings.

The rows nonetheless read as soil-moisture material, and it is worth saying why rather than letting
it look like a leak. The calculus's worked examples deliberately run on the domain that motivated
it: a vegetation-attenuation forward model, Mironov coefficients, soil and soil-water as systems.
That is the point of a worked example — it has to be *of* something — and the alternative, examples
over invented quantities, would demonstrate the machinery while hiding whether it survives contact
with a real model. The generic examples are here too, in the same tables: length and width as
distinct kinds, a blood group as a nominal scale, Mohs hardness as an ordinal one, the
principle/method/procedure examination chain.

So the reading to avoid is that these tables document the model. They document *the examples this
package ships*, and they exist here for the same reason the boundary probe does: a derived table
nobody renders is a table nobody notices has broken.

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

# Reading an index without building a document
%%%
tag := "reading-an-index"
%%%

Every table above is also available from the InfoView, under the name the directive uses:

```
#pkc_index "crossings" PropertyKindCalculus.Examples
```

which is how a pinned probe fixes one. `tests/PropertyKindCalculus/Tests/Core/Index.lean` authors a
small closed world — three kinds with one edge between them, a record, an operation, one site of
each boundary tier — and pins the rendered index of each with `#guard_msgs`. That is what turns
*the table came back empty* into a build failure, which matters more here than for a hand-written
table: a derived index that stops matching does not look broken, it looks like an absence.

The second command asks after the *docstrings* the tables quote:

```
#pkc_summary_overflow PropertyKindCalculus.Examples
```

The `What it does` column is a declaration's first paragraph — the unit its author composed, read
in preference to its first line, which ends wherever a hard wrap fell. A paragraph much longer than
the column is cut, and the cut is made on the parsed inline runs rather than on characters, so a
code span is dropped whole rather than severed and an emphasized phrase keeps its delimiters. No
docstring length can produce a cell that fails to parse.

What a length can still produce is a cell that says nothing: an ellipsis three words in, where a
summary should be. `#pkc_summary_overflow` reports the quoted docstrings that will do that, widest
first, so the question is asked where the docstrings are rather than raised as a warning against the
directive that happened to render them. It is not an error, and the fix where one is wanted is a
paragraph break — a first paragraph saying what the declaration *is*, with the argument below it.
