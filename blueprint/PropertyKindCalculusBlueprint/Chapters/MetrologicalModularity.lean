import Verso
import VersoManual
import VersoBlueprint
-- Importing the library being documented lets the `(lean := "PropertyKindCalculus.…")`
-- nodes below resolve to real declarations and report their *proved* status.
import PropertyKindCalculus
-- The tutorial's oscillator carries the requirement clause in both categories; the witness
-- node at the end of the chapter links its theorem.
import PropertyKindCalculus.Examples.Tutorial.HarmonicOscillatorRequirements

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Metrological modularity" =>
%%%
tag := "metrological-modularity"
%%%

The chapters so far give the calculus's vocabulary (kinds, quantities, units, dimensions)
and its evidence discipline (provenance, audit, uncertainty). This chapter states the
organizing principle they add up to: software organized as *metrology modules*. Nothing
in the principle is specific to science software — it applies wherever a computed value
is presented as a measurement result in the VIM sense, whatever the domain; science
software is simply where this development exercises it. A
{deftech}[metrology module]{index}[metrology module] is a software component — the
declarations one boundary names as its members, which need not be a file or a
namespace — whose

1. *interface* is a {deftech}[declared boundary]{index}[declared boundary] of kind-typed
   ports — input quantities, output quantities, parameters, configuration, and conditional
   outputs with their deciders;
2. *behavior* is a {deftech}[measurement model]{index}[measurement model] in the VIM sense — VIM 4 2CD §2.12 \[VIM3: 2.48\],
   the mathematical relation among the quantities involved, in the general implicit form
   $`h(Y, X_1, \ldots, X_n) = 0` — attached to the boundary as a checked theorem edge,
   not as prose;
3. *implementation* is a *measurement function* (VIM 4 2CD §2.13 \[VIM3: 2.49\], whose
   Note allows that "f" may symbolize an algorithm): a carrier-parametric kinded
   definition whose relation to the measurement model is `equals`, `inverts`, `refines`,
   or `boundedBy` a declared tolerance;
4. *licenses* are stated per rung of the {tech}[carrier ladder], as the relation's
   {tech}[license clause]: the measurement-model claim is proved at one carrier, and each
   further carrier the module runs at — binary32, `Float`, the tape — gets its own entry
   saying how the claim holds there. A law proved over the reals survives the move up to
   one rounding per operation; a side condition phrased in the carrier's own arithmetic,
   such as "the total is not zero", constrains the exact total at one rung and the
   rounded total at the next, and neither implies the other;
5. *mereology* is declared — each output port carries its aggregation class, and the
   license to distribute the module's computation over a carving is *derived* from that
   declaration, not assumed;
6. *requirements* are stated — what the module's quantities must satisfy, each a
   {tech}[requirement] beside the boundary it governs with the evidence by which it is
   met: a {tech}[provable requirement] by a theorem, an {tech}[empirical requirement] by
   a gate against a {tech}[referent] the model does not define.

The name pairs the discipline (metrology — the interface vocabulary is Dybkær/VIM kinds
and quantities, the spec vocabulary is the VIM measurement model) with the software
principle (modularity — boundaries, contracts, composition). Why the *relational* form
matters: VIM's general form is implicit, and its §2.12 Note 1 has the measurand's value
*inferred* from the relation. A retrieval module's honest specification is therefore
"the output satisfies the forward model's equation" — exactly, or within a declared
tolerance — not "the output is what this loop computes". The paradigm demotes the loop
to evidence *for* the relation, with the relation as the published behavior.
`MODULARITY.md` in the repository root is the working plan for carrying the paradigm
into the downstream model and deployment tiers.

# The interface — the declared boundary

:::group "metrological_modularity"
The interface clause and the judgments on it. A boundary is *declared*, so a membership
choice can be wrong about it — and the two decidable comparisons below are exactly the
two ways it can be wrong: not the boundary the members compute, or not a faithful
deployment of the tier below.
:::

:::definition "def_contract" (parent := "metrological_modularity") (lean := "PropertyKindCalculus.Provenance.Contract")
The *declared boundary*: a name, the member declarations the boundary is claimed for,
the kind-typed ports with the role each plays — `input`, `config`, `param`, `output`,
`conditional` — the exits where values leave the calculus, and, per conditional port,
the *decider*: the name of the declaration that decides its cases, so a validity domain
is read off the boundary rather than excavated from a constructor choice. Roles carry
*binding time*: a `param` is a source this tier leaves for the tier below to bind, and
`Contract.discharges` is the decidable tier relation — every inherited parameter bound
or restated, never forgotten, and no exit lost on the way up. `Contract.agrees` is the
decidable scope judgment: the declared boundary is the one the members actually
compute, in both directions. `#kind_contract_decide` and `#kind_discharges_decide`
reflect both into kernel-checked theorems. At scale the obligation moves off the
author's memory: `#kind_contracts` sweeps every contract declared under a namespace —
membership is by type, so declaring a boundary enrolls it — and `#kind_contracts_decide`
is the same sweep as a hard gate, adding each passing boundary's kernel receipt. A
deliberate falsification probe opts out explicitly with `@[kindCounterexample]`, and the
sweeps count the exemptions in their pinned headers.
:::

:::proof "def_contract"
A four-list structure over node and kind types, plus the decider association list; the
judgments are structural recursions decided by evaluation in a probe and by kernel
reduction (`decide`) in a theorem. Nothing about it is trusted from construction — the
doctrine is to decide the object.
:::

# The behavior — the measurement model as a theorem edge

:::definition "def_relation" (parent := "metrological_modularity") (lean := "PropertyKindCalculus.Provenance.Relation")
The *theorem edge* between two declared boundaries — the formal seat of the VIM 4 2CD
§2.12 measurement model. It names the two contracts, what is claimed
({uses "def_relation_kind"}[the relation kind]), the witness theorem, the claim in the
author's own words, and three optional clauses: a *tolerance* (a declaration whose type
is a `Quantity` at the kind of an output port of the governed boundary — a bound is a
kinded quantity, not a float in prose), the *named side conditions* the claim holds
under (each checked to be a declaration the witness statement mentions), and the
*license clause* ({uses "def_relation_license"}[one entry per carrier rung]). The edge
is load-bearing because the semantic claim is often unstatable structurally: a
closed-form retrieval contains none of its forward's members, a Newton retrieval
contains all of them, a lookup-table retrieval contains the forward only while building
its table — yet the scientific claim has one shape in all three cases, and only the
theorem edge states it uniformly. `#kind_relation` checks everything around the proof —
the witness a sorry-free theorem, the conclusion in the claimed shape, members of both
boundaries mentioned, every optional clause answered for by name — and
`#kind_relations` surveys a namespace's edges as one pinnable report — membership by
type, violations rendered in the report itself, `@[kindCounterexample]`-marked probes as
counted exemptions.
:::

:::proof "def_relation"
A record of names; nothing about it is decidable, because the witness already *is* a
kernel-checked proposition. What the elaborator adds is the checking of everything
around the proof, throwing on every violation, so the command is the report and the
gate at once.
:::

:::definition "def_relation_kind" (parent := "metrological_modularity") (lean := "PropertyKindCalculus.Provenance.RelationKind")
The four ways an implementing *measurement function* (VIM 4 2CD §2.13) may relate to
its measurement model, each with a checked conclusion shape: `equals` (an `Eq`),
`inverts` (an `Eq` one of whose sides composes members of both boundaries — the round
trip must be in the statement), `refines` (an `Eq` under at least one bound
hypothesis — the smaller domain, stated), and `boundedBy` (an order relation, its
tolerance nameable as a kinded quantity). The exact-versus-approximate axis of a
module's honesty is carried here: a fixed-iteration solver's true relation to its model
is `boundedBy`, and the vocabulary makes that statable rather than silently rounding it
to `equals`.
:::

:::proof "def_relation_kind"
A four-constructor enumeration; the shape checks live in the elaborator, pinned by
acceptance and refusal probes for all four kinds.
:::

# The license clause — side conditions do not transfer

A relation's {deftech}[license clause]{index}[license clause] is the part of its
declaration that extends its witness beyond the carrier rung the witness is proved at: one
entry per further rung of the {tech}[carrier ladder], each naming how the claim holds
there — a repair theorem, or an independent witness restated at that rung.

:::definition "def_relation_license" (parent := "metrological_modularity") (lean := "PropertyKindCalculus.Provenance.RelationLicense")
One rung of a relation's license clause: the carrier rung the claim is extended to, and
how it holds there. Laws transfer across the carrier ladder at the cost of one rounding
step per join; side conditions do not — a nonzero-total hypothesis checked over the
reals constrains the exact total, over binary32 the rounded fold, and neither implies
the other. So a relation claimed beyond the rung its witness is stated at owes, per
additional rung, either a named repair — {uses "thm_licenses_agree_exact"}[exact],
where rounding is the identity on the values in play, or
{uses "thm_licenses_agree_nonneg"}[nonneg], where nonnegative on-grid weights rule the
cancellation out — or `restated`: an independent witness proved at that rung. A rung
claimed with no repair and no restatement is refused, because a side condition does not
transfer by being assumed to.
:::

:::proof "def_relation_license"
A rung name and a three-constructor transfer status, each constructor carrying the name
of its evidence; the elaborator checks the named evidence is a sorry-free theorem, and
the refusal of an unanswered rung is a pinned probe.
:::

# The mereology clause, and the footprint audit

:::group "metrological_modularity_mereology"
The fifth clause is declared aggregation, and it is the port-level form of the
mereology chapter's vocabulary: a kind is {uses "def_extensiveKind"}[extensive],
{uses "def_intensiveKind"}[intensive], {uses "def_wholeProper"}[whole-proper], or
{uses "def_quasiExtensive"}[quasi-extensive], and a
{uses "def_weightedCarving"}[weighted carving] carries the aggregation license. The
clause puts that vocabulary on the boundary — each produced port declares its class —
so the license to shard, tile, or stitch a module's batch axis is derived from the
declarations rather than held as deployment convention. Requirement R27 states the
obligation; the distribution license below is the theorem that discharges it.
:::

:::definition "def_aggregation_class" (parent := "metrological_modularity_mereology") (lean := "PropertyKindCalculus.Provenance.AggregationClass")
The *aggregation class* of a produced port — the declared mereology of a boundary.
Dybkær's §13.5 vocabulary, extended by the classes the mereology layer proves laws
over: `extensive`, `quasiExtensive` (naming its per-join tolerance, a declaration
whose type is a `Quantity` at the governed port's kind — without the name,
"approximately" is not a claim), `conditionallyExtensive` (naming its condition),
`intensive`, `wholeProper`, `countKeyed` (naming the sortal the count is *of* — a
count is extensive over a fixed carving yet not a property of the whole, so it
travels with its carving rather than surviving a re-carving), `extensiveAbout`
(naming the transport law that prices a parameter change), and `interfaceLicensed`
(naming the cancellation law that purchases additivity over interior interfaces). A
contract carries one entry per classed port; the checks are hygiene — a class governs
a *produced* port, and each name the class carries exists, a tolerance as a kinded
quantity. The truth of a class is the author's curated claim, exactly as an
`Assembles` entry is.
:::

:::proof "def_aggregation_class"
An eight-constructor enumeration whose payloads are the names the classes must
answer for, plus the `aggregations` association list on the contract; the elaborator
checks are pinned by acceptance and refusal probes, and the class renders in every
`#kind_contract` report.
:::

:::theorem "thm_distribution_license" (parent := "metrological_modularity_mereology") (lean := "PropertyKindCalculus.Recarving.distribution_license") (tags := "capstone, proved") (effort := "small")
*The distribution license.* A module whose batched outputs are all extensive commutes
with a re-carving of its batch axis: one map, every output's total preserved, however
the axis is cut into tiles, blocks, or shards. The quantified boundary-level form of
{uses "thm_recarving_invariant"}[re-carving invariance], stated over the list of
output measurements because a boundary is a list. What it deliberately does not
cover: a count-keyed output — the re-carving that merges parts preserves every
extensive total while changing the count, which is why a count travels per pixel or
per shard; and the quasi-extensive case, where each total stands within its carving's
`joins · t` of the preserved whole, so a re-carving costs at most both carvings'
joins times the per-join tolerance.
:::

:::proof "thm_distribution_license"
Each output alone is {uses "thm_recarving_invariant"}[the re-carving invariance
capstone]; the license applies it under the quantifier. The quasi-extensive price is
proved in the uncertainty layer beside the `joins · t` accumulation law.
:::

What the vocabulary *does* already support module-by-module is the audit of how much
checking the kind algebra gives a boundary for free. `#kind_scc` reads the kind
vocabulary's inter-derivability clusters; `#kind_footprint` reads one declared boundary
against them and reports the component partition of its port and interior kinds (a
single-cluster collapse is flagged), the same-kind port groups (swappable however
separated the components), and the review-strength sites (crossings, attests, exits) —
closing with a pinnable verdict line answering one question per module: where does this
module's guarantee actually come from?

# The requirement clause — what the model must satisfy

:::group "metrological_modularity_requirement"
The sixth clause is a stated requirement per produced port: what the port's quantity
must satisfy, and the evidence by which it is met — a theorem edge to a specification
boundary or a theorem, with spot checks where the model runs; a gate against a marked
referent; or an attestation with its reason. The four definitions carry the data, the
commands beside them check, survey, census and gate it, and the witness at the end of the
chapter is the tutorial's oscillator carrying the clause in both categories.
:::

The five clauses above say what a module computes, how that relates to its measurement
model, at which carriers, and how it distributes. None says what the module's quantities
*must* satisfy — the input/output ratio that may not exceed a bound, the output that must
lie in a band, the idealization whose error must stay below a tolerance — nor by what
evidence each demand is met. A {deftech}[requirement]{index}[requirement] is that
statement, as data beside the {tech}[declared boundary] it governs, in the shape the
theorem edge set: declaration names the environment resolves, the author's words where
the calculus cannot read them, and nothing the commands do not check.

Two categories, told apart by the statement and not by the effort. A
{deftech}[provable requirement]{index}[provable requirement] closes over the model's own
declarations and kinded quantities — every constant its statement mentions is the model's
or the library's — so a theorem about the model discharges it: a theorem edge from the
governed boundary to a {deftech}[specification boundary]{index}[specification boundary],
a declared boundary whose one member computes the bound and whose role says so, or a
bare theorem; a negative one — "this is never summed over the pair" — by the absence of a
license the elaborator asks the environment for and must not find. Where the model also
runs, the requirement names its {deftech}[spot check]{index}[spot check]s: `Bool`
declarations the requirement command evaluates and requires `true`, the way an
inhabitation check spot-checks a proof — evidence that the proof reaches the carrier the
model runs on and the operational inputs, not a discharge. An
{deftech}[empirical requirement]{index}[empirical requirement] names a
{deftech}[referent]{index}[referent] the model does not define — a datasheet value, a
prior, a reference measurement, a population — so no theorem about the model alone can
discharge it, however much proof is spent: the referent is a free variable only
observation closes, which makes this the falsifiable category and testing its correct
instrument rather than a fallback. It is discharged by a *gate*, a decider whose
threshold is the referent, or deferred. The referent is a kinded quantity carrying
`@[kindReferent "where it comes from"]`, and the mark is what makes the demarcation
mechanical: a provable requirement's statement may name no referent, and an empirical
requirement's gate must name one. Either category may be attested, in the sense of
{tech}[attestation]: deferred with a reason in the author's words. That is not a third
category but a ratchet, counted by the census and meant to fall.

A requirement has a {deftech}[requirement scope]{index}[requirement scope]: the objects
it quantifies over — every object the boundary is evaluated for, every object of a named
sort, reached through the `Sorted` edge of the ontological square, named objects, or the
objects a named decider selects. "Every spring" is a sort, "the coupling spring" is an
object, and neither is statable over a boundary whose objects are nominal.

:::definition "def_requirement" (parent := "metrological_modularity_requirement") (lean := "PropertyKindCalculus.Provenance.Requirement")
A requirement on a declared boundary: its name as a document cites it, the statement in
the author's words, its category, the model boundary it governs and the governed port
(or the boundary as a whole), its scope, and the evidence — for a provable requirement
the witness (a theorem edge whose left side is the governed boundary and whose right
side is a specification boundary, or a sorry-free theorem), the spot checks, and the
absence claimed; for an empirical requirement the referents and the gate; for either, the
attestation that defers it. `#kind_requirement` checks everything around the statement
and throws on every failure — the governed boundary is a model's, the port is one it
declares, the scope names a sort, sorted objects, or a decider, a provable statement
names no referent, an empirical gate names one, every spot check evaluates to `true`, a
claimed absence is absent, and an attestation never stands beside a discharge.
`#kind_requirements` surveys a namespace's requirements as one pinnable report;
`#kind_requirement_coverage` is the census — every produced port of every model boundary
in scope governed by a requirement or marked `@[kindRequirementFree "reason"]`, with the
category tallies and the attested count — and `#kind_requirement_clean` its gate.
:::

:::proof "def_requirement"
A record of names and strings, nothing about it decidable; what the elaborator adds is
the checking of everything around the statement, the evaluation of the spot checks, and
the instance search behind a claimed absence, each refusal pinned by a probe.
:::

:::definition "def_requirement_kind" (parent := "metrological_modularity_requirement") (lean := "PropertyKindCalculus.Provenance.RequirementKind")
The two categories, `provable` and `empirical`, as the demarcation reads them: the
constants a provable requirement's witness statement mentions may include no
`@[kindReferent]`-marked declaration, and an empirical requirement's gate must mention
one. A requirement declared in the wrong category is refused on its constants.
:::

:::proof "def_requirement_kind"
A two-constructor enumeration; the demarcation is the elaborator's constant walk over the
witness statement and the gate's body, pinned by acceptance and refusal probes.
:::

:::definition "def_requirement_scope" (parent := "metrological_modularity_requirement") (lean := "PropertyKindCalculus.Provenance.RequirementScope")
The four scope forms: `all`, `sort` (a `SortOfSystem` declaration, which the objects
reach through their `Sorted` instance), `objects` (declarations whose type carries a
`Sorted` instance, so each is an object of some sort and not a bare value), and
`decided` (a named decider selecting a batch's subset). The square's left edge is what
makes the first three statable.
:::

:::proof "def_requirement_scope"
A four-constructor enumeration; the elaborator checks a named sort is one, synthesizes
the `Sorted` instance for each named object's type, and refuses an empty object list as
a vacuous scope.
:::

:::definition "def_boundary_role" (parent := "metrological_modularity_requirement") (lean := "PropertyKindCalculus.Provenance.BoundaryRole")
Which side of a requirement a declared boundary stands on: `model` (the default — what a
requirement governs and what the coverage census asks for) or `specification` (what a
requirement is checked against, and itself the subject of no requirement). The same
structure under the same checks, so a specification is kernel-accepted exactly as a
model is; only the role tells them apart, and `#kind_requirement` refuses a requirement
that governs a specification or is checked against a model.
:::

:::proof "def_boundary_role"
A two-constructor enumeration carried as a defaulted field of the contract, rendered in
the contract's own report when it is not the default.
:::

# What the requirement clause adds — every claim a model makes, with its evidence
%%%
tag := "requirements-as-evidence"
%%%

The five clauses before it answer the reviewer's question about a module's *computation*:
the {tech}[declared boundary] says what it reads and produces, the theorem edge says how
that relates to its {tech}[measurement model] and the {tech}[license clause] at which
carriers, and the mereology clause says how it distributes. Together they are evidence
that the module computes what it is specified to compute. They leave open the question a
model is asked when it is put to use — do the quantities it produces satisfy what that use
demands of them? — and that question has a different shape: its answer names a bound, a
band, a tolerance, and sometimes a number the model does not define. The sixth clause
answers it the way the other five answer theirs, as data beside the boundary, checked by
the elaborator, surveyed and censused by commands whose reports are pinned, and gated.
What follows is what that buys, point by point, against the mechanisms the definitions
above name.

*The demarcation is read off the statement, not granted to the author.* A
{tech}[requirement] is provable or empirical according to the constants its evidence
mentions, and the `@[kindReferent]` mark is what the check reads: a
{tech}[provable requirement]'s witness statement may name no {tech}[referent], and an
{tech}[empirical requirement]'s gate must name one. The consequence is a symmetry no prose
ledger enforces. A claim about the world cannot be presented as a theorem, since a witness
whose statement names a datasheet value is refused as provable; and a claim about the
model cannot shelter behind a test, since an empirical requirement that names a witness
is refused as empirical. The two categories are kinds of evidence, not degrees of
confidence: a reader who meets `provable` in the survey knows the discharge is a theorem
the command checked for `sorry`, and `empirical` names the referent only observation
closes. Metrology draws a neighboring distinction, between verification against a
specification and validation for an intended use; the clause cuts along a different line
— how a claim is discharged, not what it is about — because that is the line the
elaborator can decide. That an output never exceeds a physical bound is an intended-use
demand and provable; a rounding budget over the operational input distribution is a
design demand and empirical, its referent the distribution.

*Non-vacuity, carried from the capstones down to each requirement.* The
{ref "capstones"}[capstone chapter] owes every theorem three witnesses — an instance the
kernel decides, a mutant that fails, a pinned axiom profile — so that a proved statement
is shown to carry weight. A provable requirement owes the same, and the command collects
it. Its witness is a theorem edge, checked as the license clause checks one, or a bare
theorem whose axioms the report prints; on either route a witness that depends on
`sorryAx` is refused. Its {tech}[spot check]s are the instance: `Bool` declarations
evaluated where the model runs, on the operational inputs. And the construct's own test
pins a refusal for each clause of the check beside the acceptances, which is the mutant
discipline applied to the checker itself. The spot check is where the
{tech}[carrier ladder] bites. The theorem is proved at `ℝ`; the license clause above
records that a side condition does not transfer across carriers on its own; so the `Bool`
the command evaluates at `Float` is the evidence that the proof reaches the carrier the
model runs on and the inputs it meets there — evidence of reach, not a second discharge.
The asymmetry with the empirical category is exactly that there the test *is* the
discharge, and its oracle is the referent rather than the requirement's own statement.

*A negative claim becomes a discharge.* What a module must never do — sum an angular
frequency over the pair, distribute a whole-proper quantity over its parts — is as much a
requirement as what it must do. The kind algebra can refute such a sum as a theorem, and
the oscillator case study does; but the fact a reviewer needs is about the registry: that
the environment the model is built in holds no license for the sum. A provable requirement
may name that license as the one that must be absent, and the command discharges it by
asking the environment for an instance and finding none. The refusals the calculus is
built around are thereby citable as the evidence for a stated claim, rather than visible
only as a probe that fails to elaborate.

*The referent is the constant mint of the validation side.* An empirical requirement's
gate decides against a threshold, and a threshold that is a bare carrier value with a
docstring is the docstring problem in a new place: invisible to every census, its
provenance a comment. The referent is a kinded quantity carrying
`@[kindReferent "where it comes from"]`, so a datasheet band, a prior, a reference
measurement enters the model through a declared tier with its provenance on the record,
as a {tech}[constant mint] enters the computation; the mark is what the demarcation reads
and what the survey prints beside the requirement. A gate whose threshold is the model's
own is refused: a decision against nothing the world supplied is not an observation.

*Scope, through the ontological square.* "Every spring", "body A", "the objects a
decider selects" are quantifiers over particulars, and a {tech}[requirement scope] states
them through the `Sorted` edge of {ref "object-types"}[the object type]: a sort, named
objects, or a decider. Over a boundary whose objects are nominal none of the three is
statable. This is where the object layer pays for itself a second time: besides keeping
one object's quantity from standing in for another's, it makes a demand about particular
objects statable at all — a bound that holds of the coupling spring and not of the wall
springs, a band every spring of one sort must lie in — and it is why a requirement is
declared beside a boundary whose objects have sorts, not beside a bare function.

*What the capstones do not claim becomes what the model states and counts.* The capstone
chapter closes with what no theorem there asserts — the truth of an {tech}[attestation],
accuracy against nature — and leaves them to the uncertainty chapter and the reader. The
requirement clause is where those become data: each an empirical requirement with its
referent and gate, or deferred by an attestation whose reason the survey prints. The
coverage census then asks of every produced port of every model boundary whether some
requirement governs it or a `@[kindRequirementFree "reason"]` mark says why none does, in
the shape of the other {ref "coverage-censuses"}[coverage censuses], and counts the
attested ones. That count is a ratchet: it moves only by a conscious edit, and it is meant
to fall as the apparatus supplies its numbers. A model's remaining dependence on the world
is then a number in a pinned report, with a reason per entry, rather than a sentence in a
limitations section.

*What a reader gets.* For each output of each module, the survey and the census answer in
one pinned report: what must hold of it, in the author's words; over which objects;
whether the evidence is a theorem or an observation; where a theorem's proof reaches, by
its spot checks; which referent an observation is decided against and where that referent
comes from; and what is still attested, with the reason. That is the per-output form of
the question the mereology clause closes with — where does this module's guarantee
actually come from? — answered from data the elaborator checked rather than from a reading
of the source.

The tutorial's harmonic oscillator carries the clause in both categories over the
ForPhysLib case study, and its reports are pinned in
`PropertyKindCalculus.Examples.Tutorial.HarmonicOscillatorRequirements`:

:::table +header
*
  * Requirement
  * Category
  * Governs, over
  * Evidence
*
  * HP1 — the static displacement of body A per unit force never exceeds its wall spring's compliance
  * provable
  * the static-compliance boundary, over body A
  * a `boundedBy` edge to the specification boundary computing `1/k_A`, proved at `ℝ` on a named domain; a spot check at `Float`
*
  * HP2 — the velocity response per unit driving force never exceeds `1/c`
  * provable
  * the squared-impedance boundary, over every driven oscillator
  * a `boundedBy` edge to the specification boundary computing `c²`, unconditional; a spot check at the complex carrier
*
  * HP5 — the pair's mass is the sum of its bodies' masses
  * provable
  * the pair's mass boundary, over every coupled pair
  * a theorem, the licensed assembly; a spot check
*
  * HP6 — angular frequency is never summed over the pair
  * provable, negative
  * the pair's mass boundary, over every coupled pair
  * the absence of the license that would assemble it
*
  * HE1 — the linear model is used only within the spring's linear range
  * empirical
  * the static-compliance boundary, over every spring
  * attested: the range is the datasheet's to supply
*
  * HE2 — each spring's mass is at most one percent of the lighter body's
  * empirical
  * the pair's mass boundary, over every spring
  * attested: discharged when the springs are weighed
*
  * HE5 — every spring's stiffness lies within its datasheet band
  * empirical
  * the static-compliance boundary, over every spring
  * attested: the band is the datasheet's to supply
:::

The census over the module reads `3 governed, 2 exempted — clean` and
`4 provable, 3 empirical, 3 attested`: the two specification boundaries are listed as the
subject of no requirement, and the three attestations are the ratchet's opening count. The
node below is the clause's witness in this document, in the form the capstones set.

:::theorem "req_oscillator_witness" (parent := "metrological_modularity_requirement") (lean := "PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.compliance_bounded") (tags := "proved") (effort := "small")
*The clause's witness.* HP1 in full: a model boundary whose one member computes body A's
static compliance from the three stiffnesses; a {uses "def_boundary_role"}[specification
boundary] whose one member computes the wall spring's own compliance; both kernel-accepted
by `#kind_contract_decide`; a `boundedBy` edge between them whose witness is the linked
theorem, proved over `ℝ` under the named domain — positive wall stiffness, non-negative
others, a non-degenerate chain; and a spot check at `Float` on the tutorial's stiffnesses,
evaluated by `#kind_requirement` and pinned with the rest of the report. Beside it, HP6
discharges a negative claim by absence, and HE1, HE2 and HE5 are the attested empirical
rows the census counts.
:::

:::proof "req_oscillator_witness"
The bound `(k_B + k_C)/(k_A k_B + k_A k_C + k_B k_C) ≤ 1/k_A` by cross-multiplication
under the domain, closed by `nlinarith` from the non-negativity of `k_B k_C`. The
requirement command's report — edge, witness, spot check `true` — is pinned by
`#guard_msgs`, as are the survey, the census and the gate over the module.
:::
