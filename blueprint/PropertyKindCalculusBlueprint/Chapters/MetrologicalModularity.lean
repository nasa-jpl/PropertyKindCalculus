import Verso
import VersoManual
import VersoBlueprint
-- Importing the library being documented lets the `(lean := "PropertyKindCalculus.…")`
-- nodes below resolve to real declarations and report their *proved* status.
import PropertyKindCalculus

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Metrological modularity" =>

The chapters so far give the calculus's vocabulary (kinds, quantities, units, dimensions)
and its evidence discipline (provenance, audit, uncertainty). This chapter states the
organizing principle they add up to: science software organized as *metrology modules*.
A metrology module is a unit whose

1. *interface* is a declared boundary of kind-typed ports — input quantities, output
   quantities, parameters, configuration, and conditional outputs with their deciders;
2. *behavior* is a *measurement model* in the VIM sense — VIM 4 2CD §2.12 \[VIM3: 2.48\],
   the mathematical relation among the quantities involved, in the general implicit form
   $`h(Y, X_1, \ldots, X_n) = 0` — attached to the boundary as a checked theorem edge,
   not as prose;
3. *implementation* is a *measurement function* (VIM 4 2CD §2.13 \[VIM3: 2.49\], whose
   Note allows that "f" may symbolize an algorithm): a carrier-parametric kinded
   definition whose relation to the measurement model is `equals`, `inverts`, `refines`,
   or `boundedBy` a declared tolerance;
4. *licenses* are stated per carrier rung — because laws transfer across the carrier
   ladder and side conditions do not;
5. *mereology* is declared — each output port carries its aggregation class, and the
   license to distribute the module's computation over a carving is *derived* from that
   declaration, not assumed.

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
reflect both into kernel-checked theorems.
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
`#kind_relations` surveys a namespace's edges as one pinnable report, violations
rendered in the report itself.
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
