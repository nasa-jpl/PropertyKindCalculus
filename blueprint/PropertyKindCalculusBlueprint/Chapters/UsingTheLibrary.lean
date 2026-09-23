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
%%%
tag := "using-the-library"
%%%

The preceding chapters develop the calculus. This one is about *working in it*: the annotations an
author writes, what each one changes, and the indexes the library generates from them.

Four things cannot be inferred from a definition and so must be stated by its author. Each is a
family of annotations, and each has its own section below.
- *Where the calculus is left* — each site at which a value already carrying one kind is re-typed
as another, the plumbing that must drop to the carrier, the point at which a kinded value becomes
a naked one. The
{ref "boundary-family"}[boundary family]: `@[kindCrossing]`, `@[kindIngest]`, `@[kindConst]`,
`@[carrierVocab]` and `@[kindEmission]` each name the tier that sanctions a boundary site;
`@[kindCarrier]` is what brings a downstream carrier under the audit at all, `@[kindAttest]`
registers a wrapper through which authored mints go on the record, and
`@[kindCounterexample]` exempts a deliberate falsification probe from the provenance sweeps.
- *What a vocabulary answers for* — whether every dimension-one kind is individuated, every
boundary carries a measurement model, every inversion says where it fails. The
{ref "coverage-censuses"}[census marks]: `@[kindPrincipleFree]`, `@[kindRelationFree]` and
`@[kindInversionTotal]` record an honest negative with its reason, and `@[kindDiagnostic]`
enrolls a conditioning output.
- *How a definition should read* — the notation, the constants, the intermediate bindings a rendered
equation should keep. The {ref "rendering-family"}[rendering family]: `@[pkc_math]`, steered by
`@[pkc_math_symbol]`, `@[pkc_math_config]` and `@[pkc_math_transparent]`.
- *What an external document says* — which requirement a theorem discharges, which clause of
Dybkær or VIM a definition formalizes. The {ref "annotations-metadata-family"}[metadata family]:
`@[requirement]`, `@[dybkaer]` and `@[vim4]`.

The distinction that matters most is between the first two families and the other two, and it is a
distinction about what happens when an annotation is *absent*. A boundary site that carries no tier
is reported as a violation by `#kind_boundary_audit`, and that report is pinned, so omitting
`@[kindCrossing]` fails the build, and a dimension-one kind with neither a principle nor a
`@[kindPrincipleFree]` mark fails `#kind_examination_clean` the same way: the annotation *discharges
an obligation* about the code, in the way a proof discharges one about a proposition. Omitting a rendering or metadata annotation fails
nothing — `@[pkc_math_symbol]` changes only how something reads. Read the *Enforcement* column below
with that asymmetry in mind: it says `checked` for `@[pkc_math]` and `@[pkc_math_config]` too, but
what those checks reject is a *misuse* of the annotation — an argument naming a binding the
definition does not have, an attribute attached to something that is not a structure — never its
absence.

Everything in the *Generated indexes* section at the end is computed from the environment when this
chapter is built, scoped to this package's own worked examples. No row is maintained by hand, so a
renamed declaration is a build error rather than a stale table.

# The annotations at a glance
%%%
tag := "annotations-at-a-glance"
%%%

Each row links to the section that explains it.

:::pkc_annotations
:::

# The commands at a glance
%%%
tag := "commands-at-a-glance"
%%%

What the annotations *declare*, the commands *ask*. There are three forms of asking, and a
command's *suffix* names which form it is — so the table below reads in pairs and triples, each
base command followed by its suffixed siblings.

* A bare command *reads*: the answer goes to the InfoView, for a person.
* A reading frozen with `#guard_msgs` becomes a *record*. The whole answer is now reviewable in
  the diff, and a changed answer is a failed build. This is the form most of the audits take.
* A `_clean` command is the *gate that a record cannot be*, and the distinction is the reason it
  exists as a separate command rather than as a stricter pin. A record can be *re-blessed*:
  re-pinning a message whose summary reads `⚠ UNTAGGED — invariant 6/7 violation` leaves the build
  green with the invariant dead, and nothing about the pin itself distinguishes that from a
  legitimate update. The mechanism that makes an inventory reviewable is exactly the mechanism that
  lets the invariant be signed away. So a `_clean` command carries no message and pins nothing: it
  throws. There is nothing there to re-bless.

`_decide` is the fourth suffix and a different axis: the same check run in the *kernel*, leaving a
theorem behind rather than a message. `#kind_contract_decide` does not print that a boundary agrees
— it adds `c.kindContractOk` and lets `#print axioms` answer for it.

Reading the table, then: the *Pinned* column says what freezing a command's answer buys, and reads
`—` for the commands whose job is to be run by hand.

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

Two kinds can meet in two ways, and only one of them is a crossing. Under a *law* — an authored
edge, `ProductKind k₁ k₂ k` or a `KindMul` entry — the calculus derives a third kind from two, and
the use site needs no annotation at all, because the edge already licenses it. Those are the
{ref "edge-audits"}[edge audits]' subject, not this family's.

A *crossing* is the case no law covers: a value already carrying one kind is re-typed as another on
the author's signature rather than on a derivation. An edge is a rule the calculus applies; a
crossing is a place the calculus is left. That asymmetry is why one is inferred at every use and the
other must be declared once and counted.

Both kinds are stated in the signature — on the argument side as much as the result: `add` rejects a
`@[kindCrossing]` declaration none of whose arguments carries a registered carrier, because a
crossing goes FROM an already-kinded value, and a declaration with no kinded argument has nothing
to cross from. The mint or erasure
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

*And the two gates beside it.* `#kind_boundary_clean ns…` states the same invariant without a
message: it throws when any boundary-active declaration in scope carries no tier. The audit says
what the boundary *is*; this says every one of its sites has been adjudicated, and re-blessing the
first cannot silence the second because there is nothing here to re-bless. `#kind_mint_ratchet ns…`
tightens the granularity. A tier tag sanctions a whole *declaration*, so a `@[kindCrossing]` body
can hold any number of interior `⟨…⟩` under one sanction; the ratchet requires that at the crossing
and carrier-vocabulary tiers every mint be a licensed derivation or a `Quantity.attest` whose reason
is harvested — the raw column stays empty, so a new anonymous mint fails the build instead of
joining a list nobody re-reads. `@[kindConst]` and `@[kindIngest]` keep raw mints legal at the
declaration granularity, because there the declaration's own evidence is the sanction.

*In the generated indexes.* Every tagged site appears in the kind-crossing table with the kinds it
mints, taken from the audit's own walk so the two cannot disagree. `#kind_crossings [ns…]` is the
same registry from the InfoView — every sanctioned site with the first line of its docstring,
grouped by tier. It reads the *registry* where the audit walks the *environment*, which is why the
audit can report a site the registry does not contain: that site is the violation.

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

## `@[kindConst]` — a constant mint
%%%
tag := "annotation-kindConst"
%%%

The third mint tier, and the one a nullary crossing candidate turns out to be. Where
`@[kindCrossing]` goes *from* an already-kinded value and `@[kindIngest]` admits external data
through a check, `@[kindConst]` mints from neither: the value is adjudicated *data* — a cited
coefficient table, a configuration bound or box, a seed, a threshold, or a structural constant of
the model such as a zero accumulator or the vacuum index `1`.

```
/-- The probe's adjudicated threshold, cited to the table it is read from. -/
@[kindConst]
def probeThreshold : Quantity outputKind Float := ⟨0.02⟩
```

The mint's value is data rather than dataflow, so its provenance is the declaration's docstring
rather than its signature — there is no argument to trace it to. That is why the tier exists as its
own tag instead of collapsing into `@[kindCrossing]`: a declaration with no kinded argument is
*definitionally* this tier, having nothing to cross from, and the crossing attribute's rejection
message names it for exactly that reason.

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

## `@[kindAttest]` — a registered attestor
%%%
tag := "annotation-kindAttest"
%%%

An _attested_ mint is an authored `⟨…⟩` written through a registered attestor that names
its reason at the call site; `Quantity.attest` is the built-in one. The audit cannot see
through a named wrapper — a helper's body is walked once, under the helper's own name, so a
declaration that mints through an unregistered wrapper shows nothing at its own site.
Registration turns that hiding into accountability: the audit recognizes a registered
attestor's applications, reports each site with the reason string harvested from the
argument, and skips the attestor's own body, whose one raw mint is the sanctioned mechanism,
reviewed at registration — the same reason a carrier's own constructor is not a site. The
attribute derives the attestor's footprint from its signature, and refuses a declaration
that does not carry both arguments it needs:

```
`@[kindAttest]` expects a declaration taking a `KindOfProperty` argument (the attested kind) and
a `String` argument (the reason) — '…' has neither or only one. Without both, attested sites
could not be harvested, and the wrapper would HIDE its mint from the walk instead of putting it
on the record.
```

The discipline the registry serves: raw mints are the *suspect* column — a declaration-level
tier covers however many its body holds, multiplicity unseen — and attested mints the
*reviewed* one, each surviving site carrying its own one-line justification into the pinned
report. An attestation is a claim with no machine-checkable evidence; where evidence exists,
the licensed route — a `KindAdmissible` check at ingest, a `ProductKind` or `QuotientKind`
witness edge — is what to write instead, and the reason should say why no check applies.

# What the kind algebra rests on — the edge audits
%%%
tag := "edge-audits"
%%%

The boundary audit asks where the calculus is *left*. These ask what it *rests on* — the laws
under which two kinds may meet without a crossing.

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

`#kind_dimensional_clean ns…` is the coverage report's gate, and stands to it exactly as
`#kind_boundary_clean` stands to the boundary audit: no message, nothing pinned, it throws while any
edge in scope is undimensioned, conflicting or incoherent. `[parametric]` does not fire it. It has
one false alarm, and the error message says so: both the edges and the `DimensionedKind`
declarations are harvested from the environment, so a module that reaches an edge but not the module
declaring its kinds' dimensions reports that edge undimensioned while the codebase is coherent. That
is the same import-closure sensitivity the generated indexes have, pointing the other way — an
under-imported *report* silently misses rows, an under-imported *gate* invents violations. The
asymmetry is the safe one, because a false alarm is loud and a silent omission is not.

# What one declaration wires — the graph and incidence commands
%%%
tag := "graph-incidence"
%%%

The audits so far sweep *namespaces*. These read a single declaration, or the kind vocabulary as a
whole, and they are what an author runs while writing rather than what a probe pins — though most of
them pin, because a wiring that changes silently is the thing worth catching.

*What a signature states, and what a body does.* `#kind_ports d` prints the ports the declaration's
kind-typed signature states — inputs, configuration reads, outputs, each with its kind — and then
the signature's *unkinded* positions, which is the half a reader forgets to ask for.
`#kind_occurrences d` prints the other side: every authored license the body discharges inline,
each consuming application's edge with the operands that met there, in body order and with
multiplicity. `#kind_graph d` puts the two together as the constructed step graph and evaluates its
well-formedness, and `#kind_graph_decide d` proves that verdict in the kernel, leaving
`d.kindGraphWf` behind. `#kind_assembly` and `#kind_assembly_decide` are the same pair over a *list*
of declarations, assembled into one multi-step graph — which is what a boundary spanning several
definitions needs.

*What the kind vocabulary looks like as a graph.* `#kind_scc [ns…]` reports the kinds in scope,
their licensed-derivation edges, and — the finding it exists for — every *inter-derivability
cluster*: a set of two or more kinds each manufacturable from the others by licensed steps. Inside
such a cluster the kind algebra alone cannot refuse a substitution, so a cluster is a real weakening
of the discipline and one worth knowing about. `#kind_scc_clean` is its gate, and it is declarative
rather than absolute: every cluster must be declared as a parenthesized group at its exact size, so
a new witness registration that merges two kind *roles* fails the build at the vocabulary level,
before any value walks the new cycle. `#kind_scc_d2` writes the same findings as D2 diagram sources
for rendering, and `#kind_footprint c ns…` asks the question a module owner asks: which of those
clusters this boundary's own kinds land in, and therefore where the module's guarantee actually
comes from.

# What a boundary claims — the provenance sweeps
%%%
tag := "provenance-sweeps"
%%%

The boundary audit asks where the calculus is left; the edge audits ask what it rests on. These ask
whether a declared boundary is *the one its members compute*.

A `Provenance.Contract` is that declaration: the ports a boundary consumes, the exits it produces,
and the member steps that realize it. It can disagree with itself — an input the members read and
the contract never declared, a clause naming a supplier that answers no port — and the disagreement
is not visible in any type, because a contract is data about a computation rather than a constraint
on it.

*Enrollment is by type, which is the design.* Every constant whose type is headed by
`Provenance.Contract` under the swept namespaces is a subject, so declaring a boundary enrolls it.
There is no per-declaration command to remember and no registration to forget: a boundary cannot be
declared and left out of the sweep, which is the property a per-name command
(`#kind_contract`, one contract) cannot offer however diligently it is used.

`#kind_contracts ns…` re-checks every subject exactly as `#kind_contract` checks one — the
decider, aggregation and supplier clauses, then the declared boundary against the one the members
compute — and renders one line per contract in declaration-name order, as a single `info` message
suitable for `#guard_msgs` pinning. Namespaces elided, this is the validation probe's own pinned
output:

```
kind contracts — 4 contract(s), 1 violated, 1 exempted
  ✗ …Bad.forgottenInput: 'sweep probe forward, x forgotten' — undeclared input fwd/x : aK
  …Good.fwdBoundary: 'sweep probe forward' — 2 ports, 0 exits, 1 member step(s)
  …Good.invBoundary: 'sweep probe retrieval' — 2 ports, 0 exits, 1 member step(s)
  ⊘ …Exempt.keptCounterexample: counterexample, exempted
```

Three things in that header rather than one. Because it counts the *subjects* as well as the
violations, a pin fails on a boundary that vanished as readily as on one that broke; because it
counts the exemptions, exemption creep is a failed pin too. And a scope with no contracts pins
`0 contract(s)` rather than passing invisibly — the distinction between *checked and clean* and
*nothing was checked*, which an empty report cannot make.

`#kind_contracts_decide ns…` is the same sweep as a hard gate. A violation is an error rather than a
`✗` row, so no reading of the output can state one, and each passing contract gains the kernel
theorem `c.kindContractOk`. Sweeping again re-proves nothing: a standing receipt reports as
`already stands`. The two tiers answer different questions — whether the boundaries in scope agree,
and whether the kernel has been made to say so.

*The same three forms, per name.* `#kind_contract c` and `#kind_contract_decide c` are the sweep's
singular siblings, and what they add over `#kind_assembly` is the comparison: the assembly says the
wiring holds together, the contract says the members are the ones the declared interface belongs to.

*And the edges between boundaries.* A `Provenance.Relation` states what one boundary claims of
another — an inversion, a bound. `#kind_relation r` checks one: a sorry-free witness, the conclusion
in the claimed shape, and the tolerance, hypothesis and license clauses each answered for by name.
Every failure throws, so that command is report and gate at once. `#kind_relations ns…` is its
by-type sweep, with the same `✗`/`⊘` rows and the same counted header.
`#kind_discharges c d` asks the tier question instead — what a deploying contract did with each
parameter the deployed one handed it — and `#kind_discharges_decide` proves the answer.

*What is not kinded, and what is not propagated.* Two commands report *absences*, which is the
thing a checker cannot notice on its own. `#kind_unkinded c` prints the naked positions and unkinded
flows in a contract's scope; pinned, it fails when a silence appears *and* when one is fixed,
which is what keeps the ledger honest about which direction it moved — and `#kind_unkinded_clean` is
the gate for a scope that has cleared them. `#kind_budget b c` checks an uncertainty budget's
attachment to a boundary and renders the influencing sources the budget *omits* as `unbudgeted
source(s)`, so what the model is not propagating appears in the report rather than being absent from
it. `#kind_contract_propagation` and `#kind_output_ledger` are the reading aids beside them: which
source ports reach which produced ports, and the per-output assumption ledger.

## `@[kindCounterexample]` — a deliberate misdeclaration, kept
%%%
tag := "annotation-kindCounterexample"
%%%

A sweep that enrolls by type has one cost: a *falsification probe* — a contract written wrong on
purpose, kept because its checker refuses it — enrolls too, and would fail the gate it exists to
demonstrate. Deleting it would leave the checker's refusal untested; leaving it untagged would make
the gate unpinnable.

```
/-- A deliberately misdeclared boundary, kept because the sweep must refuse it. -/
@[kindCounterexample]
def keptCounterexample : Provenance.Contract := …
```

A tagged subject renders as a `⊘` row and is *not* checked, so the probe stands beside the gate it
exercises. The exemption is not a way out of the discipline, because it is counted: the header's
exemption count is part of the pin, so a contract quietly exempted to make a build pass changes the
pinned output. The mark reaches the generated tables on the same terms — a tagged contract is not a
coverage subject, and a tagged relation is not a witness, since a deliberate misdeclaration must not
discharge a real boundary's edge obligation.

The attribute checks what it is attached to, and says why:

```
`@[kindCounterexample]` expects a 'Provenance.Contract' or a 'Provenance.Relation' — '…stray' is
neither. The mark exempts a declaration from the by-type provenance sweeps, and only those two
types are swept.
```

# What a vocabulary answers for — the coverage censuses
%%%
tag := "coverage-censuses"
%%%

The audits so far ask about one declaration, one namespace's boundary, or one boundary's
agreement with itself. The censuses ask the question the {ref "model-template"}[model
template]'s rubrics put to a whole vocabulary: over a *population* the environment can
enumerate — every dimension-one kind, every declared boundary, every produced port, every
inversion edge — does each member declare what the rubric obliges it to? Six censuses share
one shape, set by `#kind_examination_coverage`: a record command whose sorted `info` message
is pinned, a `_clean` gate that throws and pins nothing, a declared exception where the
population has honest negatives, and an audit receipt at each success point — which is what
lets a document's conformance table read a rubric as green only in a build where its census
ran over the document's scope.

- `#kind_examination_coverage ns …` (M6) walks every dimension-one `DimensionedKind` in
  scope and reports it `[individuated]` by its examination principle, `⊘ exempted` by a
  {ref "annotation-kindPrincipleFree"}[`@[kindPrincipleFree]`] mark, or `⚠ UNINDIVIDUATED`.
  Inside the dimension-one fiber the principle is the only defining aspect that separates
  two kinds, so a kind declared without one is named, not individuated. A `KindOfProperty`
  that no `DimensionedKind` wraps is reported `⚠ UNDIMENSIONED` rather than decided:
  "dimension one" is a fact about a dimension the vocabulary never declared, and a gate that
  passed over such kinds would pass over nothing.
- `#kind_relation_coverage ns …` (M12) walks every `Provenance.Contract` in scope and
  reports it `[witnessed]` by the theorem edges naming it, `⊘ exempted` by a
  {ref "annotation-kindRelationFree"}[`@[kindRelationFree]`] mark, or `⚠ UNWITNESSED`.
  Relations are walked unscoped, since a theorem edge may live beside a deployment rather
  than beside the boundary it is about, and a `@[kindCounterexample]` relation is not a
  witness. Whether a named edge is *valid* is `#kind_relations`' question; this census asks
  only whether one exists.
- `#kind_mereology_coverage ns …` (M15) walks every produced port — `output` or
  `conditional` — of every contract in scope and reports it `[classed]` by its aggregation
  class or `⚠ UNDECLARED`. There is no exception mark: the `AggregationClass` vocabulary is
  total over the honest negatives — a port that must never be summed declares `.intensive`,
  one its parts do not determine declares `.wholeProper` — so declaring nothing is exactly
  the finding.
- `#kind_inversion_coverage ns …` (M21, the domain half) walks every contract that an
  `inverts` edge names as its left side — the boundary that recovers what another consumed
  — and reports it `[guarded]` by a `conditional` port, with its decider where one is named,
  `⊘ exempted` by a {ref "annotation-kindInversionTotal"}[`@[kindInversionTotal]`] mark, or
  `⚠ UNGUARDED`.
- `#kind_wellposedness_coverage ns …` (M20, and M21's ambiguity half) walks every
  `inverts` edge in scope and reports it `[well-posed]` by a `wellPosed` witness on its
  declared `domain`, `[surfaced]` by an `ambiguity` witness, or `⚠ UNDECIDED`. No exception
  mark: an inversion either has exactly one answer on a declared domain or it does not, and
  either answer is a declaration.
- `#kind_diagnostic_coverage ns …` (M22) walks every
  {ref "annotation-kindDiagnostic"}[`@[kindDiagnostic]`]-marked kind in scope and reports it
  `[exported]` by a produced port carrying it or `⚠ SIDECHANNELED`. Enrollment is the mark,
  so a scope with no marks records that visibly rather than passing in silence.

Each has its `_clean` sibling — `#kind_examination_clean`, `#kind_relation_clean`,
`#kind_mereology_clean`, `#kind_inversion_clean`, `#kind_wellposedness_clean`,
`#kind_diagnostic_clean` — which throws while any member of its population is a `⚠` row,
and records the audit receipt exactly when it does not fire. A `@[kindCounterexample]`
contract is a subject of none of them and is listed as exempted, so a census says what it
skipped; a mark on a member that satisfies the predicate anyway is inert, so a stale
exemption cannot hide a declaration made later; and a contract declared at node or kind
types the census cannot read is reported `⚠ UNREADABLE` rather than walked past. Every
census is import-closure sensitive in the direction the other environment walks are: an
exemption declared in a module the probe does not reach is a loud false alarm, never a
silent pass.

The pinned form of the first, from the validation suite — the namespace prefix and two
further `[individuated]` rows elided:

```
examination coverage:
[individuated] …probeIndividuated (probe individuated) — principle: probe-principle
⊘ exempted …probeGeometry (probe geometry) — the wave calculus's own geometry, the product of no phenomenon
⚠ UNDIMENSIONED …probeBareKind (probe bare kind) — no DimensionedKind wraps it
⚠ UNINDIVIDUATED …probeBare (probe bare)
5 dimension-one kind(s): 3 individuated, 1 exempted, 1 UNINDIVIDUATED; 1 kind(s) UNDIMENSIONED — examination-coverage violation
```

## `@[kindPrincipleFree "…"]` — a dimension-one kind that is correctly principle-free
%%%
tag := "annotation-kindPrincipleFree"
%%%

The declared exception to M6. A geometry vocabulary — an illumination cosine, a normalized
wavenumber — is the product of no measurement phenomenon; a nominal designation has no
principle to carry; a bookkeeping fraction is examined by nothing. Each is dimension one and
each is correctly without an examination principle, and the mark is that decision as data
the census can read, with its reason:

```
/-- Dimension one, no principle, exempted with a reason. -/
@[kindPrincipleFree "the wave calculus's own geometry, the product of no phenomenon"]
def probeGeometry : DimensionedKind :=
  { kind := { id := "probe geometry", scale := .ratio }, dim := 1 }
```

It attaches to the `DimensionedKind`, not to the `KindOfProperty`, because the population
it exempts a kind from is "dimension one", a fact about the `DimensionedKind`. On a kind
that does carry a principle the mark is inert — the census reports the principle and
ignores the mark — so a stale exemption cannot hide an individuation supplied later. The
attribute checks its target, and requires a non-empty reason:

```
`@[kindPrincipleFree]` expects a 'DimensionedKind' — '…notAKind' is not one. The mark exempts a
dimension-one kind from the examination-coverage sweep, and dimension is a fact about the
DimensionedKind, so that is where the mark goes.
```

## `@[kindRelationFree "…"]` — a boundary with no measurement model
%%%
tag := "annotation-kindRelationFree"
%%%

The declared exception to M12, on a `Provenance.Contract`: a boundary whose behavior is not
a measurement model — pure data movement, or the reference the theorem edges are *about* —
said in the author's words where the census reads them.

```
/-- No edge, on purpose. Its port is classed. -/
@[kindRelationFree "a data-movement boundary: its behavior is the identity on kinds, and \
  there is no measurement model to carry"]
def dataMove : Provenance.Contract NodeId KindRef where …
```

Inert on a boundary some edge names. Rejected at elaboration unless the declaration is a
`Provenance.Contract` and the reason is non-empty: the mark exempts a declared boundary from
a census over declared boundaries, so that is where it goes.

## `@[kindInversionTotal "…"]` — an inversion with no outside
%%%
tag := "annotation-kindInversionTotal"
%%%

The declared exception to M21's domain half, on the `Provenance.Contract` an `inverts` edge
names as its left side: the inversion is total on its input type, so there is no failure
outside the domain to detect and no `conditional` port to guard it.

```
/-- Inverted, no conditional port, exempted as total. -/
@[kindInversionTotal "total on its input type: every integer is the forward's image of one, \
  so there is no outside to detect"]
def totalInverse : Provenance.Contract NodeId KindRef where …
```

Inert on a boundary that declares a conditional port, and checked exactly as
`@[kindRelationFree]` is.

## `@[kindDiagnostic "…"]` — a conditioning output, enrolled
%%%
tag := "annotation-kindDiagnostic"
%%%

Not an exception but an *enrollment*, on a `KindOfProperty`: the kind is a quality or
conditioning output a consumer must read, and the string says what it diagnoses.

```
/-- A quality kind the retrieval exports: marked diagnostic, and carried by a produced
port of `Good.invBoundary` below. -/
@[kindDiagnostic "whether the retrieval's answer was decided inside its domain"]
def qcK : KindOfProperty := { id := "contract coverage probe quality", scale := .ordinal }
```

`#kind_diagnostic_coverage` then asks the declared boundaries in scope for a produced port
carrying it; a marked kind no boundary exports is a side channel. An unmarked kind is not
walked, so removing the mark is the exemption, and a scope with no marks records that
visibly. Rejected at elaboration unless the declaration is a `KindOfProperty` and the
description is non-empty.

# How a definition reads — the rendering family
%%%
tag := "rendering-family"
%%%

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
one as the `System — Component ; kind-of-property` triple it is — the `System` slot naming the
*sort* — cross-linked to the sort and component tables rather than repeating their identity
strings. The systems table lists the particulars; nothing dedicates to a particular, so it carries
no dedicated-kinds column.

:::pkc_index "sorts" (scope := PropertyKindCalculus.Examples)
:::

:::pkc_index "systems" (scope := PropertyKindCalculus.Examples)
:::

:::pkc_index "components" (scope := PropertyKindCalculus.Examples)
:::

:::pkc_index "dedicated-kinds" (scope := PropertyKindCalculus.Examples)
:::

Two dedicated kinds that share a kind-of-property are held apart only by their sort and component,
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

The third writes rather than prints. `#pkc_index_page "…" […] ns…` renders the named indexes into
the *elaborating module's own module docstring*, so doc-gen4 publishes them as that module's page —
the same route `@[pkc_math]` takes to reach two surfaces through one docstring, applied to a table
instead of an equation.

What a length can still produce is a cell that says nothing: an ellipsis three words in, where a
summary should be. `#pkc_summary_overflow` reports the quoted docstrings that will do that, widest
first, so the question is asked where the docstrings are rather than raised as a warning against the
directive that happened to render them. It is not an error, and the fix where one is wanted is a
paragraph break — a first paragraph saying what the declaration *is*, with the argument below it.
