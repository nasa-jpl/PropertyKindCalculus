import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import PropertyKindCalculusBlueprint.Chapters.Spine
import PropertyKindCalculusBlueprint.Chapters.Units
import PropertyKindCalculusBlueprint.Chapters.Dimension
import PropertyKindCalculusBlueprint.Chapters.Interaction
import PropertyKindCalculusBlueprint.Chapters.Extensivity
import PropertyKindCalculusBlueprint.Chapters.Iso80000
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part3
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part4
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part5

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "PropertyKindCalculus Blueprint" =>
%%%
shortTitle := "PropertyKindCalculus"
tag := "kindcalculus-blueprint"
%%%

PropertyKindCalculus is a Lean 4 formalization of René Dybkær's *An Ontology on Property
for Physical, Chemical, and Biological Systems* (2009), extended with David
Flater's full tracking of kinds of quantities (NIST Technical Note 1943,
Appendix C). This blueprint is the design map: it records what is already proved
(linked to real declarations) and the *capstone theorems we plan to provide*,
with the dependency graph and a status summary at the end.

The whole blueprint is also available as a single paginated document:
[download the PDF](PropertyKindCalculus-Blueprint.pdf).

# Requirements

What follows is the fixed set of requirements PropertyKindCalculus is *specified*
to meet. The next section, *Why a calculus, not a taxonomy*, argues *why* a
calculus is needed where a taxonomy stops, and the chapters after it develop and
prove each requirement; this section states them up front, as the axes the design
is judged against, with a status table at the end mapping each axis to the
declaration that discharges it.

The requirements fall into four groups: how kinds are *structured*, how
*operations* on them are gated, how the kind layer is kept *consistent* with the
coarser dimension and unit layers, and how values *aggregate* over parts.

## Kind structure

*R1 — Kinds are first-class and discriminate within a dimension.* Two properties
of the same physical dimension can still be different kinds, and the type system
must keep them apart. Volumetric water content (`Quantity vwc`), gravimetric
water content (`Quantity gwc`), relative permittivity, reflectivity, and
emissivity are all dimension-one, yet `Quantity vwc` and `Quantity gwc` must be
*different types* — not interchangeable values. (QUDT's and SysML v2's `QuantityKind` is subsumed here as one such kind —
a scale-gated leaf — not as the root.)

*R2 — Specialization is a lattice, with comparability but not identity.* Width,
Height, and Diameter each specialize Length, and a kind may specialize several
parents at once — a lattice, not a tree. Specialization is a preorder (reflexive
and transitive) and induces a *one-way* coercion: a `Quantity Width` may be used
where a `Quantity Length` is wanted, never the reverse, and that up-cast is a
visible, deliberate loss of information. Width and Height remain *mutually
comparable* — they share the super-kind Length — while staying distinct kinds. This
requirement is now realized on the real standard: the ISO 80000-3 length family
(width, height, distance, radius, … of items 3-1.2 … 3-1.12, all of dimension `L`)
is specified as a specialization lattice over the general length kind, each species
individuated *not by fiat but by an explicit measurement principle* (see the
_ISO 80000-3_ chapter).

*R3 — General versus individual is type versus term.* A kind is the general
notion (a *type*); a particular measured value is an individual (a *term* of that
type). `Length` is a type; the length of this pencil is a term of type
`Quantity Length`. The two are never conflated — the punning OWL permits between a
class and its instances is structurally impossible here.

## Operation gating

*R4 — Operations are gated by kind (the additive law).* Arithmetic that keeps a
quantity within its kind is well-typed; arithmetic across incompatible kinds is a
*compile-time type error*, not a runtime check. `Width + Width = Width`
type-checks; `Width + Height` does not — and, decisively, neither does
`Torque + Energy`, even though torque and energy share a dimension. Matching
dimension is not licence to add.

*R5 — The interaction algebra is a partial, typed, ternary product.* Some kinds
combine *across* kinds to yield a third: torque times plane angle is energy,
force times length is work. The combination is partial and curated — most pairs
combine to *nothing* (fuel-consumption times rainfall is a category error, not a
number) — and it carries a division dual, with multiplication and division proved
inverse. This multiplicative combination is distinct from R4's additive,
same-kind gate.

*R6 — Operator availability is gated by the measurement scale, monotonically.*
Which operations even *exist* between two properties is fixed by their scale type,
$`\mathrm{nominal} \sqsubset \mathrm{ordinal} \sqsubset \mathrm{interval}
\sqsubset \mathrm{ratio}`: a nominal property admits only $`=`, a ratio property
admits $`\times` and $`\div`, and a richer scale licenses every operation a
poorer one does. This gate is *orthogonal* to kind — kind says *which* properties
may combine, scale says *which operators* are defined at all. This requirement is
now realized on the real standard: ISO 80000-5 lists thermodynamic temperature
(ratio-scale) and Celsius temperature (interval-scale) at the *same* dimension `Θ`,
so a ratio of Celsius temperatures is undefined where a ratio of thermodynamic
temperatures is not — the scale type, not the dimension, separates them (see the
_ISO 80000-5_ chapter).

## Soundness bridges

*R7 — Dimension certifies coherence; it does not decide legality.* Every kind has
a dimension, but dimension is a *consistency check*, not the authorization:
matching dimensions are necessary yet never sufficient — which is exactly what
lets R4 reject `Torque + Energy`. Formally the dimension map
$`\dim : \mathrm{Kind} \to \mathrm{Dimension}` is a *forgetful functor* and a
*homomorphism*:
$$`\mathrm{KMul}\ k_1\ k_2\ k_3 \;\Longrightarrow\; \dim k_3 = \dim k_1 \cdot \dim k_2.`

In plain engineering terms: $`\dim` is a deliberately *lossy, one-way*
translation from the rich kind layer down to the coarse SI-dimension layer. It
keeps only the base-quantity exponents (length, mass, time, …) and *forgets*
everything else, so many distinct kinds collapse onto the same dimension and
there is no way back — that is what "forgetful" names. Calling it a
*homomorphism* says the translation *respects multiplication*: the dimension of a
product equals the product of the dimensions (the exponents add), so the kind
layer and the dimension layer can never disagree about what multiplying means. It
is the discipline of ordinary dimensional analysis, stated and proved as a law
rather than performed by hand.

*R8 — Units are chosen values of a kind; conversion is a faithful round-trip.* A
unit is a distinguished value of a kind (a metre is a chosen length), and a
measured quantity is a number times a unit. Converting a quantity from one unit
to another of the *same* kind and back is the identity — conversion is
multiplication by a ratio, defined only within a kind. There is no conversion
between units of *different* kinds; that too is a type error, not a runtime check.

## Aggregation

*R9 — Extensive quantities aggregate additively over parts; intensive ones do
not.* For an *extensive* kind the value over a whole is the sum of the values
over its disjoint parts — the mass of an assembly is the sum of its parts'
masses. Where this fails it must *not* be assumed: volume on mixing is
sub-additive (ethanol and water), and that negation is stated to keep the
extensive predicate honest. Tracking which kinds are extensive is the
precondition for soundly summing measurements.

## Representation parametricity

*R10 — A quantity value is parametric in its numeric representation type.* The
magnitude of a scalar quantity is carried at a *representation type* $`R`, a type
parameter bounded by whatever algebraic structure a given task demands, so the
*same* kind-indexed value can be instantiated at whichever $`R` the task needs —
without changing the kind, scale, dimension, interaction, or extensivity layers
above it. This is the axis dependent types make not just possible but *necessary*:
the carrier the kind sits over is exactly where proof and execution diverge, and a
single quantity must serve both. Three representations matter, and they are not
interchangeable:

- *Lean's $`\mathbb{R}` — for proofs.* A complete ordered field: the continuous
  specification against which laws (monotonicity, conversion round-trips,
  extensivity) are stated and proved.
- *A finite floating-point rounding model — for numerical-accuracy reasoning.*
  TorchLean's `FP32` (`NeuralFloat` at binary32 precision: round-to-nearest,
  ties-to-even over $`\mathbb{R}`, finite-only, with `toReal : FP32 → ℝ`). It is
  *non-computable* — it exists to bound rounding error against the $`\mathbb{R}`
  spec, not to run.
- *An executable IEEE-754 type — for exact-execution reasoning and code
  generation.* TorchLean's `IEEE32Exec` (a bit-level `UInt32` binary32 kernel) that
  models NaN, infinities, signed zeros, and subnormals, with `toFloat`/`ofFloat`
  and `isNaN`. This is the representation that actually runs and the one in which
  exceptional values (NaN) can be reasoned about — what one might call the
  "exec" float, distinct from the `FP32` rounding *spec*.

Soundness *across* representations is itself a theorem, not an assumption: an
exec/spec *refinement* (the executable float result is the rounding of the real
result) lets a law proved over $`\mathbb{R}` transfer to the executable run. In
plain engineering terms: choose the number type to fit the job — reals to prove,
the rounding model to bound error, the IEEE kernel to run and to catch NaN — while
the kind, dimension, and unit machinery above is written once and is identical for
all three. This refines R1/R3/R4's kind-indexed value into a doubly-indexed
`Quantity (k : KindOfProperty) (R : Type)` whose arithmetic is bounded by a
`Carrier` typeclass on $`R`. The value layer and its additivity laws are *realized*
(sorry-free): `Quantity k R` with same-kind addition, the additivity laws proved
once over any lawful carrier, and three carriers — `Int` and `ℝ` (lawful, for
proof) and `Float` (executable, deliberately not lawful). The exec/spec
*refinement* across representations is now *also realized* (sorry-free): the
abstract bridge `CarrierRefinement` and its kind-indexed capstone
`Quantity.add_refines` — a law over the lawful spec carrier descends to the exec
carrier as one rounding step — instantiated in the separately-built `Torch`
library at TorchLean's binary32: `FP32` (the rounding *spec*, an *unconditional*
refinement of $`\mathbb{R}`) and `IEEE32Exec` (the *executable* kernel, refining
$`\mathbb{R}` on the finite/no-overflow path, with overflow surfaced as an explicit
side condition rather than silently dropped).

## Value representation: vectors and scalar units

*R11 — Units are scalar; a vector quantity is a numerical array times one scalar
unit.* Following ISO 80000-2 §18 (scalars, vectors and tensors), a vector (or
tensor) quantity is written as a *numerical* vector multiplied by a single unit,
and "all units are scalars" — *not* as a collection of per-coordinate quantity
values each carrying its own number × unit; the quantity itself is independent of
the coordinate system while its numerical components are not. This is exactly the
R10 carrier taken at a numerical-array type: a vector quantity is
`Quantity (k : KindOfProperty) (Fin n → R)` — one kind $`k`, the numbers an
$`n`-vector in the carrier $`R`, and one *scalar* `MetrologicalUnit` of the kind
for the whole vector — and the additivity laws transfer to the vector carrier by
the *same* parametric proof used for scalars (the pointwise `Carrier (Fin n → R)`).
It is the ISO 80000-2 §18 *numerical-array* reading of value representation, and it
aligns with the VIM's "a quantity is scalar; a vector/tensor is a composite of
scalar quantities" — the priority SysML v2 inverts (see *Why a calculus, not a
taxonomy*). The fuller *structural* apparatus is a separate axis, still owed below.

## Verified classification: kind-laws that instantiate at the quantity level

*R12 — A classification is a certificate, not an assertion; kind-laws instantiate at
the quantity level.* By default a kind is a *tag*: `Quantity k R` records the kind but
the magnitude is arbitrary, so a value can be labelled with a kind it has not earned.
R12 upgrades a classification to a *certificate* — a proof that a quantity satisfies
its kind's *defining relation* (the formalized ISO 80000 *Remark*) to quantities of the
kinds it is built from. A length built as speed × time is certified by construction; a
bare `⟨999⟩` cannot be certified against those factors. The kind becomes a *refinement*
(a tag plus its earned proof).

The reason this strengthens the calculus is *instantiation*. Every kind-law is stated
as a carrier-parametric universal over quantities with the kind-relation as a premise,
so it instantiates to a quantity-level fact by ordinary application — the inter-kind
generalization of R10's carrier-parametric laws — and any property of a kind's defining
relation transports to *every* quantity certified under it (every certified surface
area is `≥ 0`, because the area element is). The pattern comes in three algebraic
shapes — *product* (area = length · length, energy = force · length), *quotient*
(speed = length / duration, plane angle = arc / radius), and *reciprocal* (frequency =
1 / period, curvature = 1 / radius) — each a kind-law family in the core; analysis-shaped
relations such as area as a surface integral `∬ √g du dv` follow the same discipline in
the layer where their mathematics lives. These are exercised directly on ISO 80000-3's
own *Remarks* (see the _ISO 80000-3_ chapter), where, for instance, the plane angle is
*computed* to be dimension one because it is a ratio of two lengths. R12 unifies the two
halves of the standards work: the formalized remark *is* the defining relation, and
classification is the witnessed instantiation of it.

## Out of scope (for now)

*Value representation in the structural sense* — coordinate frames, tensor
variance (the covariant/contravariant split), bound-versus-free vectors, and frame
transformations — is *not yet specified* here, beyond the ISO 80000-2 §18
numerical-array reading now specified as R11. This *structural* axis is distinct
from R10's *numeric carrier* $`R` and R11's *numerical array*. It is a genuine
systems-engineering requirement, but a *separate, orthogonal* axis: its principled
home is an index *over* the kind, never a layer the kind hangs beneath (the
inversion the *Why a calculus, not a taxonomy* section charges against SysML v2).
Stating it as owed keeps the boundary honest.

## The requirements at a glance

:::table +header (align := center)
*
  * Requirement
  * Concrete test
  * Specified as
  * Status
*
  * R1 — kind discrimination within a dimension
  * `vwc ≠ gwc`, both dimension one
  * kind-indexed `Quantity k R`; dimension-1 disambiguation
  * proved
*
  * R2 — specialization lattice + comparability
  * Width, Height, Diameter specialize Length (ISO 80000-3); weight, static vs kinetic friction force specialize Force (ISO 80000-4); Helmholtz vs Gibbs energy specialize Energy (ISO 80000-5) — comparable yet distinct, by examination principle
  * `Specializes` preorder; `MutuallyComparable`; examination defining-aspect (`Refines`, `distinct_of_examPrinciple`)
  * proved
*
  * R3 — general vs individual (type vs term)
  * `Length` a type; this pencil's length a term
  * `KindOfProperty` vs `Quantity k R`
  * proved
*
  * R4 — kind-gated addition
  * `Width+Width` ok; `Width+Height`, `Torque+Energy` rejected
  * `Quantity.add` over `Quantity k R` (same-kind gate)
  * proved
*
  * R5 — interaction algebra (partial, typed)
  * `torque × angle = energy`; `fuel × rainfall` an error
  * `KMul` / `KDiv`; multiplication–division inverse
  * proved
*
  * R6 — scale-type operator availability (monotone)
  * nominal: only `=`; ratio: `×`, `÷`; thermodynamic temperature (ratio) vs Celsius (interval), same dimension `Θ` (ISO 80000-5)
  * `ScaleType` order; operator monotonicity; `AllowsRatio` on the standard's temperatures
  * proved
*
  * R7 — dimension certifies, not decides
  * `dim` many-to-one; necessary ≠ sufficient
  * `dim` homomorphism
  * proved
*
  * R8 — units and conversion round-trip
  * round-trip metre/foot conversion is the identity; cross-kind is a type error
  * `Unit k`; conversion round-trip
  * planned
*
  * R9 — extensive aggregation
  * mass sums over parts; volume-on-mixing does not
  * `Extensive`; additive law + counterexample
  * proved
*
  * R10 — numeric representation parametricity
  * same value at `ℝ`/`Int` (proof), `Float` (executable); `FP32`/`IEEE32Exec` refine `ℝ`
  * `Carrier`-bounded `Quantity k R`; parametric additivity laws; `CarrierRefinement` + `Quantity.add_refines`
  * proved (layer + laws + exec/spec refinement)
*
  * R11 — scalar units; vector = numerical array × one scalar unit (ISO 80000-2 §18)
  * a displacement as `Quantity k (Fin 3 → ℝ)` with one metre; laws transfer
  * pointwise `Carrier (Fin n → R)`; scalar `MetrologicalUnit`
  * proved
*
  * R12 — verified classification; kind-laws instantiate at the quantity level
  * a length built as speed × time is certified by construction; `⟨999⟩` cannot be certified; every certified surface area is `≥ 0`
  * `ProductKind` kind-laws; `Quantity.IsProduct` certificate + smart constructor; defining relations from the ISO 80000 remarks (area = `∬√g`)
  * proved (product family + area instance)
*
  * *(out of scope)* structural value representation
  * coordinate frames, tensor variance, transforms
  * an orthogonal index over the kind
  * not specified
:::

# Why a calculus, not a taxonomy

PropertyKindCalculus continues a line of machine-checkable metrology modeling, and
inherits its problem statement from exactly where that line stops.

## From QUDV to an OML metrology vocabulary

OMG SysML 1.2 introduced
[QUDV](https://www.omgwiki.org/OMGSysML/doku.php?id=sysml-qudv:quantities_units_dimensions_values_qudv)
(Quantities, Units, Dimensions, Values) as a library for declaring quantity
kinds, units, and their dimensional factoring; QUDV's foundations were then
revised substantially across SysML 1.3 and 1.4.

In parallel, a formalization in OML — leveraging the semantics of OWL2-DL for
classification-based reasoning — reworked those foundations, the quantity-kind
and unit _stereotypes_ carried by SysML, to align them with Dybkær's _An
Ontology on Property_. That effort became the
[opencaesar metrology vocabulary](https://github.com/opencaesar/metrology-vocabularies),
whose current version combines the updates and motivations of the VIM4 2nd
Committee Draft (2CD, 2023-07-31) with Dybkær's ontological grounding. OWL2 (SROIQ) carries the metrology
_taxonomy_ well: specialization, the general-vs-individual quantity distinction
(encoded as concept vs. instance), dimensional factoring, and OWL2-DL/SPARQL
consistency checks over units.

Where a description logic stops is visible in that vocabulary's own _dimensional
analysis_: computing a derived quantity's dimension from its factors is an
arithmetic induction that has to be pushed out of OWL2 into SPARQL 1.1 Update,
and even there it is brittle — updates report success while inserting no triples,
because "update succeeded" is not a statement about _what was established_.
Dimension arithmetic sits right at that boundary; the kind interaction algebra
and the algebraic _laws_ are past it.

## What a description logic cannot express

A description logic captures the _taxonomy_ but is structurally unable to capture
the _calculus_. The recurring gap is arithmetic, operations,
definedness-conditions, laws, and proofs:

- *Dimension arithmetic* ($`\dim(a\cdot b) = \dim a + \dim b`): OWL2 has no
  datatype arithmetic; in Lean it is an ordinary function with a homomorphism
  theorem.
- *The interaction algebra* (torque $`\times` angle $`=` energy): role chains
  are binary, regular, and carry no arithmetic side-conditions; in Lean it is a
  ternary relation with a dimensional-coherence proof obligation.
- *Scale-type operator gating* (which of $`=,<,+,\times` are *defined*): DL has
  no operations; in Lean the scale indexes which typeclasses apply, and
  monotonicity of availability is a proved meta-theorem.
- *Extensivity* ($`\mathrm{value}(\text{whole}) = \sum \mathrm{value}(\text{parts})`):
  no quantified arithmetic in DL; in Lean it is a $`\forall`-theorem.
- *Units* (a unit is a chosen value of a kind; conversion is a ratio): no
  arithmetic in DL; in Lean it is a definition with a round-trip theorem.
- *Meta-theorems* (specialization is a preorder; $`\dim` is a homomorphism): a
  DL reasoner checks *consistency*, not *laws* — proving the laws is the point.

## SysML v2: a quantity model organized by value representation

OMG's current generation ships a standard-library treatment of quantities and
units, examined here at tag
[SysML v2, 2026-04](https://github.com/Systems-Modeling/SysML-v2-Release/tree/2026-04/sysml.library/Domain%20Libraries/Quantities%20and%20Units)
(its `Quantities`, `MeasurementReferences`, and ISQ packages). Read against
Dybkær, it is built around a different organizing axis than the one taken here as
primary, and the contrast is the cleanest way to say what a *kind-primary* model
buys.

### The evidence: representation is the root, kind is a leaf

The quantity-value hierarchy is rooted in *value representation*, not in quantity kind.
The most general value is `TensorQuantityValue`, a tensor of any order, and the
specialization chain runs *toward* the scalar, each more specific type being a
lower-order tensor — `VectorQuantityValue :> TensorQuantityValue`, then
`ScalarQuantityValue :> VectorQuantityValue`
([SysML v2, 2026-04 — Quantities.sysml, lines 17–46](https://github.com/Systems-Modeling/SysML-v2-Release/blob/2026-04/sysml.library/Domain%20Libraries/Quantities%20and%20Units/Quantities.sysml#L17-L46)):
$$`\text{Scalar} \sqsubseteq \text{Vector} \sqsubseteq \text{Tensor}.`
So a scalar *is a* tensor of order 0 and a vector *is a* tensor of order 1. What
a value's type primarily records is the apparatus of that representation:
- its tensor order,
- the split of that order into *contravariant* and *covariant* indices — the attributes `contravariantOrder` and `covariantOrder` on
`TensorQuantityValue`, constrained to sum to the order
([SysML v2, 2026-04 — Quantities.sysml, lines 33–36](https://github.com/Systems-Modeling/SysML-v2-Release/blob/2026-04/sysml.library/Domain%20Libraries/Quantities%20and%20Units/Quantities.sysml#L33-L36))
- whether a vector is bound or free, and
- a matching measurement reference (tensor / vector / scalar) carrying the coordinate frame and its transformations.

Each of these is a statement about *how a quantity is measured, coordinatized, and
valued*, not about *what kind of property* it is.
The contravariant/covariant split is the sharpest case of this representation-centric view — the one
record-field that is *unambiguously* representational, on three escalating counts.

1. *Pure coordinate bookkeeping.* It records only how a value's components
   transform under a change of frame — nothing about what the quantity *is*. The
   other three fields each record a facet of the quantity itself:
   - tensor order tracks its mathematical character,
   - bound-versus-free is a genuine physical distinction (and one the library actually uses), and
   - the measurement reference
   names a dimension and a frame.

  The variance split alone carries no information about the quantity kind.

2. *Not quantity-invariant.* Using the metric to raise a covariant (lower) index
   or lower a contravariant (upper) one moves a unit between the two counts — say
   from `contravariantOrder` 2, `covariantOrder` 0 to a mixed 1 and 1 — while the
   order, and the physical quantity, stay fixed. That the quantity is unchanged is a
   fact of *tensor algebra* — the metric's raising/lowering isomorphism — not a SysML
   v2 statement: the library defines no raise- or lower-index operation, so it would
   record the two splits as distinct `TensorQuantityValue`s with nothing to mark them
   as one quantity. A feature that a pure change of representation can move while the
   quantity is held fixed is thus a property of the representation, not of the
   quantity's kind. Hold the quantity fixed and the other three fields are pinned with
   it — order, bound-status, and reference do not change — so the variance split is the
   one field free to vary while the modeled quantity stays put (worked through just below).

3. *Empirically inert.* The split is declared on the abstract root and named by
   its constraint, yet assigned by *no* quantity anywhere in the library: even the
   genuine order-2 kinds — `Cartesian3dStressTensor`, with strain and moment of
   inertia alongside it — inherit the two slots and leave them unset, fixing only
   `isBound`, `num`, and `mRef`
   ([SysML v2, 2026-04 — ISQMechanics.sysml, lines 730–746](https://github.com/Systems-Modeling/SysML-v2-Release/blob/2026-04/sysml.library/Domain%20Libraries/Quantities%20and%20Units/ISQMechanics.sysml#L730-L746)).
   The apparatus is carried at the root whether or not any kind exercises it. By
   contrast `isBound` *is* used (88 free against 7 bound), so the point is precise
   rather than blanket: bound-versus-free is live machinery, while the variance
   split is declared-but-unexercised overhead inherited from the tensor root.

To see why the second count bites — and what the model *loses* by it — follow the
library's own machinery. `Cartesian3dStressTensor` stores its value as
`num: Real[9]`, nine bare reals, with the variance split left blank (same
listing). In an orthonormal Cartesian frame that omission is harmless: under the
Euclidean metric the contravariant components $`\sigma^{ij}`, the mixed
$`\sigma^i{}_j`, and the covariant $`\sigma_{ij}` are numerically equal, so it
does not matter which the nine numbers are. But `TensorCalculations::transform` is
defined to carry a tensor value from a source frame to a target frame through a
`CoordinateTransformation`
([SysML v2, 2026-04 — TensorCalculations.sysml, lines 45–49](https://github.com/Systems-Modeling/SysML-v2-Release/blob/2026-04/sysml.library/Domain%20Libraries/Quantities%20and%20Units/TensorCalculations.sysml#L45-L49),
[MeasurementReferences.sysml, lines 126–135](https://github.com/Systems-Modeling/SysML-v2-Release/blob/2026-04/sysml.library/Domain%20Libraries/Quantities%20and%20Units/MeasurementReferences.sysml#L126-L135)),
and the transformation rule is keyed on the split: a contravariant index
transforms by the Jacobian of the coordinate change, a covariant index by its
inverse — mutually inverse rules, so the two generally yield different numbers.
Move to a frame where they differ — any non-orthonormal frame, which is to say the
everyday cylindrical, spherical, or material coordinates of continuum mechanics —
and the nine numbers transform by *different* rules depending on a datum the model
declared but never filled in.

What is missing, then, is the ability to transform an order-2 (or higher-order)
quantity between frames *at all*: the `transform` contract cannot be met without
the split, so for exactly the quantities where it would matter the operation is
underdetermined. And the gap is *silent*. The concrete types are pinned to a
Cartesian frame, where the omission never shows; the model type-checks and looks
complete, and fails only where one would actually rely on it — in the curvilinear
frames it was never exercised in. That is precisely a representational hole that
validation cannot see: correct on every case anyone tested, wrong on the first
case anyone needed.

The lone constraint the library attaches to the split sharpens the reading.
`orderSum` requires `contravariantOrder + covariantOrder == order`
([SysML v2, 2026-04 — Quantities.sysml, line 36](https://github.com/Systems-Modeling/SysML-v2-Release/blob/2026-04/sysml.library/Domain%20Libraries/Quantities%20and%20Units/Quantities.sysml#L36)).
Metrologically it is a well-formedness invariant, not a statement about the
quantity: it says only that the chosen split must be a valid partition of the
quantity's actual order. Its content is that *order is the frame-invariant datum
and the split is a convention that must respect it* — raising or lowering an index
slides one unit between `covariantOrder` and `contravariantOrder` but holds their
sum, the order, fixed. So `orderSum` is exactly what makes *the same quantity, a
different split* formally coherent: the order — which carries the quantity's
mathematical character — is conserved while the representation changes underneath
it. It constrains nothing metrological: not dimension, unit, scale, or kind, only
that the coordinate bookkeeping adds up. The one rule SysML v2 writes about
variance is thus itself a pure-representation consistency check — the section's
thesis in miniature.

The kind-of-quantity sits one level *down*, as a leaf, and the source is decisive
on this point: there is no first-class "kind" entity. Length, mass, temperature,
and the other base quantities are each declared as a *subtype of the scalar value
type* — `attribute def LengthValue :> ScalarQuantityValue` — with the dimension
carried only by the corresponding unit's `quantityDimension`, e.g. `LengthUnit`
([SysML v2, 2026-04 — ISQBase.sysml, lines 16–38](https://github.com/Systems-Modeling/SysML-v2-Release/blob/2026-04/sysml.library/Domain%20Libraries/Quantities%20and%20Units/ISQBase.sysml#L16-L38)),
and that `quantityDimension` attribute itself lives on `ScalarMeasurementReference`
([SysML v2, 2026-04 — MeasurementReferences.sysml, lines 82–99](https://github.com/Systems-Modeling/SysML-v2-Release/blob/2026-04/sysml.library/Domain%20Libraries/Quantities%20and%20Units/MeasurementReferences.sysml#L82-L99)).
In other words, "length-the-kind" exists only as (i) a nominal subtype hanging
beneath `ScalarQuantityValue` and (ii) a power-product of base quantities on its
unit — never as a property whose nature is named in its own right. To reach a
kind one must already have committed to a representation branch: the kind is
*nested under* the representation. The proportions confirm the weight — across the
ISQ library 319 kinds are declared on the scalar branch, against 2 vector, 4
tensor, and 51 fixed-three-vector kinds.

That places the concern precisely. A valued quantity has two independent
classification axes:

- *(A) kind-of-property* — its nature, fixed by Dybkær's examination principle,
  common to all mutually comparable quantities;
- *(B) value representation* — scalar / vector / tensor order, coordinate frame,
  bound-versus-free — what SysML v2 packages as the measurement reference.

Dybkær's ontology lives entirely on axis (A) and is deliberately *agnostic* to
(B): whether a position is recorded as one number, three Cartesian components, or
a tensor in a chosen frame does not change *what kind of property* it is. SysML
v2 makes axis (B) the root and nests (A) beneath it. The model even flags the
departure from its own source: it quotes the VIM3 "quantity" Note 5 — "A quantity
as defined here is a scalar. However, a vector or a tensor, the components of which
are quantities, is also considered to be a quantity" — then notes that "the rest
of \[VIM\] does not explicitly define how tensor and vector quantities can be or
should be supported"
([SysML v2, 2026-04 — MeasurementReferences.sysml, lines 29–31](https://github.com/Systems-Modeling/SysML-v2-Release/blob/2026-04/sysml.library/Domain%20Libraries/Quantities%20and%20Units/MeasurementReferences.sysml#L29-L31)).
The tensor-rooted hierarchy is thus SysML's own interpretation, and it *inverts*
the VIM's priority — both the quoted VIM3 and the VIM4 2CD (quantity, 1.1 Note 4:
"As defined here, quantities are scalar … vectors, and tensors are considered
quantities in a broader sense if their components are (scalar) quantities") make
the quantity fundamentally scalar, with vectors and tensors as composites *of*
scalar quantities; SysML v2 makes the tensor primary and the scalar the degenerate
order-0 case.

### How PropertyKindCalculus takes the kind as root instead

PropertyKindCalculus inverts the nesting: axis (A) is the root. A kind-of-property is a
first-class value (`KindOfProperty`), and a quantity is indexed *by its kind* —
`Quantity (k : KindOfProperty)` — so the kind is fixed before, and independently
of, any choice of how the value is recorded. Dimension is not the organizing
principle but a forgetful functor $`\dim : \mathrm{Kind} \to \mathrm{Dimension}`
that *certifies* coherence without *deciding* what is allowed (developed in the
next section). Two consequences fall out directly: two kinds that share a
dimension remain distinct types — so the dimension-1 disambiguation is
expressible — and an operation across kinds is a type error rather than a silent
success. Value representation — the axis SysML v2 puts at the root — is, candidly,
*not yet specified* here; its principled home is an *orthogonal* index over the
kind, never a layer the kind hangs beneath.

### The two designs side by side

:::table +header (align := center)
*
  * Aspect
  * SysML v2 (2026-04)
  * PropertyKindCalculus
*
  * Root organizing axis
  * value representation (tensor order, frame)
  * kind-of-property (Dybkær)
*
  * A *kind of quantity* is…
  * a leaf subtype of `ScalarQuantityValue`
  * a first-class type index, `Quantity (k : KindOfProperty)`
*
  * Role of dimension
  * the discriminator for commensurability, on the reference
  * a forgetful functor `dim`; certifies, never decides
*
  * Two kinds, one dimension (vwc vs gwc)
  * indistinguishable
  * distinct by construction
*
  * Adding a length to a mass
  * well-typed (`Scalar × Scalar → Scalar`)
  * a type error
*
  * Scalar / vector / tensor, frames, transforms
  * first-class and rich
  * not yet specified (owed — an orthogonal index)
*
  * Algebraic laws
  * a modelling library; none machine-checked
  * proved theorems (preorder, homomorphism, monotonicity)
:::

The table is honest in both directions: SysML v2's representation-first design
buys real, first-class machinery for coordinate frames, transformations, and
stress and strain tensors that systems engineering genuinely needs — machinery
PropertyKindCalculus does not yet have. The claim is not that one model is right; it is
that the axes are *orthogonal and should not be nested*.

### Limitations of the SysML v2 approach

Rooting the hierarchy in representation has three consequences that bear directly
on PropertyKindCalculus's problem statement:

1. *A kind cannot be named without first choosing a representation, so one kind
   fragments.* Position is a single kind-of-property, yet appears as
   `CartesianPosition3dVector`, `CylindricalPosition3dVector`,
   `SphericalPosition3dVector`, and `PlanetaryPosition3dVector` — individuated by
   *coordinate frame*, not by the nature of the property. The cylindrical and
   spherical forms even carry mixed-dimension components (a length and two
   angles), so the single documented "quantity dimension $`\mathrm{L^1}`" does not
   survive its own representations
   ([SysML v2, 2026-04 — ISQSpaceTime.sysml, lines 304–353](https://github.com/Systems-Modeling/SysML-v2-Release/blob/2026-04/sysml.library/Domain%20Libraries/Quantities%20and%20Units/ISQSpaceTime.sysml#L304-L353)).
2. *The within-dimension conflation is left untouched.* On the scalar branch the
   dimension is the only discriminator, so volumetric and gravimetric water
   content, relative permittivity, reflectivity, and emissivity remain
   indistinguishable — exactly the confusion that motivates PropertyKindCalculus. Putting
   representation at the root does nothing about it; the two are orthogonal.
3. *The calculus is kind- and dimension-blind.* Scalar addition is declared
   `ScalarQuantityValue × ScalarQuantityValue → ScalarQuantityValue`, so adding a
   length to a mass is well-typed; nothing gates an operation on agreeing kind or
   dimension
   ([SysML v2, 2026-04 — QuantityCalculations.sysml, line 29](https://github.com/Systems-Modeling/SysML-v2-Release/blob/2026-04/sysml.library/Domain%20Libraries/Quantities%20and%20Units/QuantityCalculations.sysml#L29)).

## How the calculus maps into Lean

Two things in particular resist a DL encoding: the _interaction algebra_ (which
kind $`\times` which kind $`=` which kind, a _partial_ relation with arithmetic
side-conditions, not a role chain), and the difference between _instantiation_
and _subtyping_ (that a radius _is a_ length, versus that this pencil's length
_is an instance of_ the length kind — conflated by punning in OWL). In Lean both
map cleanly, and the mapping _is_ the design:

1. *Kinds and units are type-level parameters.* `Quantity (k : QuantityKind) (u :
   Unit) : Type` — a kind and a unit index a _type_, not a value of one universal
   `Quantity` class. This is the move OWL cannot make.

2. *Specialization (⊑) induces coercions between types.* It lives on those
   parameters: `Quantity Radius metre → Quantity Length metre` is sound — a
   radius _is a_ length — and the reverse is not. Up-casting to a parent kind is
   an explicit, visible loss of information.

3. *Instantiation is term-of-type, not subtyping.* The length of a pencil is a
   _term_ `pencil : Quantity Length metre := ⟨5.2⟩` — a value of that type,
   related to its kind by typing/instantiation, never by subtyping. The
   general/individual distinction _is_ the type/term distinction.

4. *The kind algebra is a partial typed algebra, not a group.* PhysLib's
   `Dimension` is a _total_ `CommGroup` — multiply, divide, invert anything.
   Kinds are not: `Torque × Angle = Work` is meaningful; `Torque + Energy` must
   be _blocked_ even though the dimensions match; `FuelConsumption × Rainfall` is
   an error (Flater's own example). The meaningful products are encoded as a
   relation surfaced through typeclass resolution — Flater's "map kinds onto
   classes + operator overloading," lifted into Lean's elaborator.

5. *Dimension is a soundness functor, not the primary type.* In QUDV and most
   quantity libraries dimension is the _primary_ classifier: two quantities
   interoperate exactly when their dimensions agree — which is precisely the move
   that collapses every dimension-one quantity into one indistinguishable type.
   PropertyKindCalculus inverts the dependency: the _kind_ is the primary type-level
   index, and dimension is recovered as a forgetful functor $`\dim : \mathrm{Kind}
   \to \mathrm{Dimension}`. Its job is _certification_, not decision — the
   coherence theorem `KMul k₁ k₂ k₃ → dim k₃ = dim k₁ · dim k₂` proves every
   product the kind algebra admits is dimensionally consistent — but `dim` never
   decides whether an operation is _allowed_; the kind relation does. Agreeing
   dimensions are necessary, not sufficient.

6. *Specialization (⊑) is a preorder — a lattice, not a tree.* Flater stresses
   this (citing Formal Concept Analysis): a kind can specialize several parents.
   Unit-1 subtyping (Flater §6) is then just the _dimension-1 slice_ of that kind
   lattice — and nothing forces it to be uniform: units of plane angle, for one,
   could carry their own subtyping reflecting the different measurement
   principles by which they are realized.

7. *The numeric carrier is a type parameter, bounded by a typeclass (R10).* A
   scalar quantity is `Quantity (k : KindOfProperty) (R : Type)` with the arithmetic
   on $`R` supplied by a `Carrier` typeclass — the kind fixes *what is measured*,
   $`R` fixes *in what numbers*. Everything above $`R` (kind discrimination, scale
   gating, the dimension functor, the interaction algebra, extensivity) is written
   once, against the typeclass, and is reused verbatim at every $`R` (the additivity
   laws, for one, are proved a single time over any lawful carrier and hold at `ℝ`
   and `Int` with no per-carrier proof). This is the architecture TorchLean already runs:
   models are written against a `Context α` typeclass (arithmetic + transcendentals
   + comparison) and instantiated at `α := ℝ` for the *spec*, `α := FP32` for the
   finite *rounding* model, and `α := IEEE32Exec` for the *executable* IEEE-754
   kernel — the *same* source elaborated at three carriers. The kind layer here is
   the missing index *above* that carrier: TorchLean makes a tensor polymorphic in
   its scalar type; PropertyKindCalculus makes the scalar polymorphic in its *kind*,
   and the two indices compose. Crucially the carriers are bridged by *refinement
   theorems* (`toReal (op_exec x) = round (op_real (toReal x))`), so a law proved at
   $`\mathbb{R}` is not stranded in the proof world — it descends to the float that
   runs. A description logic has no type parameters and no typeclasses, so this
   whole axis is unavailable to it; here it is the ordinary discipline of
   parametric polymorphism.

The trigger was concrete. PhysLib's `Dimension` makes all dimension-one
quantities equal, so it cannot distinguish volumetric ($`\mathrm{L^3/L^3}`) from
gravimetric ($`\mathrm{M/M}`) soil moisture, nor either from permittivity,
reflectivity, or emissivity. Every dangerous soil-moisture confusion is
dimension one. Indexing quantities and units by *kind* is what restores the
distinction — this is the dimension-1 disambiguation capstone in the Units
chapter.

# How to read the status

Nodes that link a real declaration with `(lean := "PropertyKindCalculus.…")` report
their *proved* status straight from the checked, sorry-free core. Nodes tagged
`planned` carry an informal statement and a proof sketch only; they show as
in-progress goals until formalized. The headline deliverables are tagged
`capstone`.

{include 0 PropertyKindCalculusBlueprint.Chapters.Spine}

{include 0 PropertyKindCalculusBlueprint.Chapters.Units}

{include 0 PropertyKindCalculusBlueprint.Chapters.Dimension}

{include 0 PropertyKindCalculusBlueprint.Chapters.Interaction}

{include 0 PropertyKindCalculusBlueprint.Chapters.Extensivity}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part3}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part4}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part5}

{blueprint_graph}

{blueprint_summary}
