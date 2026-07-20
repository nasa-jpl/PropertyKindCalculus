import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import PropertyKindCalculusBlueprint.Chapters.Spine
import PropertyKindCalculusBlueprint.Chapters.DedicatedKind
import PropertyKindCalculusBlueprint.Chapters.Units
import PropertyKindCalculusBlueprint.Chapters.Dimension
import PropertyKindCalculusBlueprint.Chapters.Interaction
import PropertyKindCalculusBlueprint.Chapters.FunctionCalculus
import PropertyKindCalculusBlueprint.Chapters.Extensivity
import PropertyKindCalculusBlueprint.Chapters.WriteOnce
import PropertyKindCalculusBlueprint.Chapters.Uncertainty
import PropertyKindCalculusBlueprint.Chapters.Iso80000
import PropertyKindCalculusBlueprint.Chapters.ScaleSpanning
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part3
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part4
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part5
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part6
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part7
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part8
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part9
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part10
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part11
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part12
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part13
import PropertyKindCalculusBlueprint.Chapters.CrossReferences
import PropertyKindCalculusBlueprint.ItemIndex
import PropertyKindCalculusBlueprint.TraceabilityTable
import PropertyKindCalculusBlueprint.References
import PropertyKindCalculusBlueprint.Version

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PropertyKindCalculusBlueprint.ItemIndex
open PropertyKindCalculusBlueprint.Traceability
open PropertyKindCalculusBlueprint.Version

/-- The per-part tally of catalogued quantity kinds, computed live from each
part's `catalogue` so the front-page counts cannot drift from the formalized
standards. -/
def isoTally : DocTable := tallyTable [
  (PropertyKindCalculus.Iso80000.Part3.source, PropertyKindCalculus.Iso80000.Part3.catalogue),
  (PropertyKindCalculus.Iso80000.Part4.source, PropertyKindCalculus.Iso80000.Part4.catalogue),
  (PropertyKindCalculus.Iso80000.Part5.source, PropertyKindCalculus.Iso80000.Part5.catalogue),
  (PropertyKindCalculus.Iso80000.Part6.source, PropertyKindCalculus.Iso80000.Part6.catalogue),
  (PropertyKindCalculus.Iso80000.Part7.source, PropertyKindCalculus.Iso80000.Part7.catalogue),
  (PropertyKindCalculus.Iso80000.Part8.source, PropertyKindCalculus.Iso80000.Part8.catalogue),
  (PropertyKindCalculus.Iso80000.Part9.source, PropertyKindCalculus.Iso80000.Part9.catalogue),
  (PropertyKindCalculus.Iso80000.Part10.source, PropertyKindCalculus.Iso80000.Part10.catalogue),
  (PropertyKindCalculus.Iso80000.Part11.source, PropertyKindCalculus.Iso80000.Part11.catalogue),
  (PropertyKindCalculus.Iso80000.Part12.source, PropertyKindCalculus.Iso80000.Part12.catalogue),
  (PropertyKindCalculus.Iso80000.Part13.source, PropertyKindCalculus.Iso80000.Part13.catalogue)
]

def sysmlComparisonTable : DocTable := mdTable true
  ["Aspect", "SysML v2 (2026-04)", "PropertyKindCalculus"]
  [
  ["Root organizing axis",
   "value representation (tensor order, frame)",
   "kind-of-property (Dybkær)"],
  ["A *kind of quantity* is…",
   "a leaf subtype of `ScalarQuantityValue`",
   "a first-class type index, `Quantity (k : KindOfProperty)`"],
  ["Role of dimension",
   "the discriminator for commensurability, on the reference",
   "a forgetful functor `dim`; certifies, never decides"],
  ["Two kinds, one dimension (vwc vs gwc)",
   "indistinguishable",
   "distinct by construction"],
  ["Adding a length to a mass",
   "well-typed (`Scalar × Scalar → Scalar`)",
   "a type error"],
  ["Scalar / vector / tensor, frames, transforms",
   "first-class and rich",
   "not yet specified (owed — an orthogonal index)"],
  ["Algebraic laws",
   "a modelling library; none machine-checked",
   "proved theorems (preorder, homomorphism, monotonicity)"]
  ]

#doc (Manual) "A Property Kind Calculus for Metrology: proving quantity and unit laws in Lean, from ISO/IEC 80000 to measurement uncertainty" =>
%%%
shortTitle := "A Property Kind Calculus for Metrology"
tag := "kindcalculus-blueprint"
%%%

Models of physical systems are saturated with quantities, yet the languages used to
manage them — SysML/QUDV, OWL-based vocabularies such as QUDT and OML, and
dimension-checking type systems — verify _dimensions_, not _kinds_. Two quantities of
the same dimension are therefore silently interchangeable: volumetric and gravimetric
water content, relative permittivity and reflectivity, torque and energy. These
descriptive languages record the metrology _taxonomy_ — which kinds exist, their
dimensions and defining relations — but stop there: they cannot express the _calculus_
that operates on those kinds — dimension arithmetic, the kind-interaction algebra,
scale-gated operations, extensivity; cannot carry one model across the numeric carriers a
quantity must inhabit; and cannot state, let alone check, a single law as a theorem. A property kind calculus _subsumes_ them: it
retains the taxonomy and adds the _calculus_, _parametricity_ over the carrier, and
machine-checked _proof_. The strongest prior formalization is no exception: the ISQ and
SI have been mechanized in a proof assistant
{Manual.citep foster_automated_reasoning_for_physical_quantities}[], yet that work checks
_dimensions_, not kinds — the dimensional calculus is one part of metrology, and cannot
separate the confusions above.
We present PropertyKindCalculus (PKC) {version}[], a machine-checked formalization, in the
Lean 4 proof assistant, of Dybkær's seminal contribution to metrology
{Manual.citep dybkaer_ontology_on_property}[] and several recent developments in this field
(Flater {Manual.citep flater_architecture_for_software_assisted_quantity_calculus}[],
Willink {Manual.citep willink_evaluation_of_measurement_uncertainty_based_on_moments}[], and
Degenhardt {Manual.citep degenhardt_efficient_alternative_to_monte_carlo}[]). PKC makes a
kind a first-class type, kind-incompatible arithmetic a compile-time error, and
classification a proof obligation. Of nineteen metrology requirements, sixteen are
discharged as kernel-checked theorems and three — the capabilities a type system affords
by construction — are demonstrated by elaboration. The standard is the test: all eleven
quantity-and-unit parts of ISO/IEC 80000, item by item, 700+ kinds with checked
dimensions and proved defining relations. Because a PKC model is carrier-polymorphic and
its measurement uncertainty is an additive descriptor, a single model definition serves
proof, calculation, sensitivity analysis, and uncertainty quantification with no
rewrite — the design principle we abbreviate _write once, correctly; go fast,
automatically_. Measurement uncertainty, its propagation, and the coverage of the
resulting interval are thereby machine-checked, while _accuracy_ against nature — which
needs a true value the kernel never has — remains an empirical matter; the boundary is
exact, not rhetorical. The result is a modeling discipline whose specification
documents — rendered from the checked sources — are verifiable rather than merely
descriptive.

This blueprint is the design map for that formalization: it records what is already
proved (linked to real declarations) and the *capstone theorems we plan to provide*,
with the dependency graph and a status summary at the end.

The whole blueprint is also available as a single paginated document:
[download the PDF](PropertyKindCalculus-Blueprint.pdf).

# What PropertyKindCalculus provides

This project addresses *nineteen requirements* about formalizing _metrology_ — the
science of measurement — and discharges most of them as machine-checked theorems
rather than prose. A substantial part of the library is grounded directly on the
published *ISO and IEC 80000* metrology standards — _eleven_ of the thirteen parts (every
part but the two general ones, 1 _General_ and 2 _Mathematics_), catalogued item by item.
The table below is generated directly from the formalized catalogues, so its per-part
counts and total stay in step with the Lean source:

:::iso_doc_table isoTally
:::

In plain terms, _rigorous metrology_ here means:

- *Telling apart quantities that look identical.* Two measurements in the same
  units can still be different in nature — volumetric and gravimetric soil
  moisture are both "just a ratio", yet confusing them corrupts a result. The
  calculus keeps such quantities distinct _types_, so the mix-up is impossible
  rather than merely discouraged; agreeing units (or dimensions) are treated as
  necessary but never sufficient.
- *Rejecting nonsense arithmetic before it runs.* Adding a length to a mass — or
  even a torque to an energy, which share the same dimension — is a compile-time
  error, not something caught (or missed) at run time. Quantities that genuinely
  combine, such as a torque times an angle giving an energy, are sanctioned
  explicitly; everything else is refused.
- *Knowing which operations even make sense.* What you may do to a measurement
  depends on its scale: you can rank mineral hardness but not average it; you can
  subtract Celsius temperatures but only take ratios of thermodynamic ones. These
  rules are enforced automatically.
- *A faithful hierarchy of kinds.* Width and height are special cases of length —
  usable where a length is wanted, never the reverse — while a general kind
  (length) is never confused with one individual measurement (the length of this
  pencil). A kind can even be tied to the system and component it is _dedicated_ to,
  so "water content of soil" is named in its own right.
- *Units that convert safely and never silently.* A unit is a chosen reference of
  one specific kind; a conversion round-trips exactly, and there is simply no
  conversion between units of different kinds.
- *Summing only what may be summed.* The masses of the parts add up to the mass of
  the whole; the volumes of mixed liquids do not. The calculus tracks which
  quantities aggregate and refuses to assume it of the rest.
- *Classifications you can trust because they are earned.* Labelling a value "an
  area" requires a proof that it really is a width times a height; an arbitrary
  number cannot wear the label.
- *The same model from proof to running code.* One quantity can carry exact real
  numbers for proving properties and IEEE floating-point for execution — with a
  theorem guaranteeing the running code matches the proven specification, rounding
  and all — and a vector quantity is a list of numbers under a _single_ shared
  unit, not a bag of separately-united components.
- *Honest unit classification.* Not even the SI base units are all alike — some
  (the mole, the candela) are derived in disguise — so the calculus names that
  third category instead of pretending the base/derived split is clean.

Each of these is stated precisely as one of the nineteen requirements below, and
the status table at the end of that section maps every requirement to the checked
declaration that discharges it.

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

## Kind structure (R1, R2, R3)

*R1 — Kinds are first-class and discriminate within a dimension.* Two properties
of the same physical dimension can still be different kinds, and the type system
must keep them apart. Volumetric water content (`Quantity vwc`), gravimetric
water content (`Quantity gwc`), relative permittivity, reflectivity, and
emissivity are all dimension-one, yet `Quantity vwc` and `Quantity gwc` must be
*different types* — not interchangeable values. (QUDT's and SysML v2's `QuantityKind` is subsumed here as one such kind —
a scale-gated leaf — not as the root.) This reaches its limit on ISO 80000-11
_Characteristic numbers_, where *all 115* kinds — every one a dimensionless ratio — share
dimension one, so the dimension functor collapses the entire part to a single point and
only the kind layer holds its members apart (see the _ISO 80000-11_ chapter). The
*principled* form of this within-dimension discrimination — naming a kind by the
system and component it is _dedicated to_, so volumetric and gravimetric water
content differ by their kind-of-property rather than by an identity string — is
Dybkær's dedicated kind-of-property (see the _Dedicated kinds-of-property_ chapter).

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
_ISO 80000-3_ chapter), and the same pattern recurs on Part 4's force family, Part 5's
thermodynamic potentials, and IEC 80000-6's AC power family — active, reactive, and
apparent power as species of one power kind, carrying three different unit strings
(`W`, `var`, `VA`) over one dimension (see the _IEC 80000-6_ chapter) — and on ISO 80000-7's
radiation trios, where radiant, luminous, and photon flux are one measurand in three
modes, the radiant and luminous members even sharing a dimension (see the
_ISO 80000-7_ chapter). ISO 80000-11 pushes this furthest: the same name recurs as a
_different kind_ across its transport-phenomena clauses — the two Froude numbers, the five
Stokes numbers, the four Bejan numbers — each sub-suffixed sibling sharing *both* name and
dimension (one) with the others, so the measurement principle alone tells them apart (see
the _ISO 80000-11_ chapter).

*R3 — General versus individual is type versus term.* A kind is the general
notion (a *type*); a particular measured value is an individual (a *term* of that
type). `Length` is a type; the length of this pencil is a term of type
`Quantity Length`. The two are never conflated — the punning OWL permits between a
class and its instances is structurally impossible here.

## Operation gating (R4, R5, R6)

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
_ISO 80000-5_ chapter). IEC 80000-6 repeats the pattern on electromagnetism: electric
potential is gauge-dependent (fixed only up to an additive reference), hence
interval-scale, while electric potential difference, of the same dimension `V`, is
ratio-scale (see the _IEC 80000-6_ chapter).

## Soundness bridges (R7, R8)

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

## Aggregation (R9)

*R9 — Extensive quantities aggregate additively over parts; intensive ones do
not.* For an *extensive* kind the value over a whole is the sum of the values
over its disjoint parts — the mass of an assembly is the sum of its parts'
masses. Where this fails it must *not* be assumed: volume on mixing is
sub-additive (ethanol and water), and that negation is stated to keep the
extensive predicate honest. Tracking which kinds are extensive is the
precondition for soundly summing measurements.

## Representation parametricity (R10)

*R10 — A quantity value is parametric in its numeric representation type.* The
magnitude of a scalar quantity is carried at a *representation type* $`R`, a type
parameter bounded by whatever algebraic structure a given task demands, so the
*same* kind-indexed value can be instantiated at whichever $`R` the task needs —
without changing the kind, scale, dimension, interaction, or extensivity layers
above it. This is the axis dependent types make not just possible but *necessary*:
the carrier the kind sits over is exactly where proof and execution diverge, and a
single quantity must serve both. Three *real* representations matter, and they are not
interchangeable — and a fourth *complexifies* any of them:

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
- *The complexification $`\mathrm{Complex}\ R` of any of the above — for
  complex-valued quantities.* Many physical quantities take a complex value (the
  relative permittivity of a lossy dielectric $`\varepsilon = \varepsilon' +
  j\varepsilon''`, an impedance, an AC phasor); complex-ness is a property of the
  *carrier*, not the kind, so $`\mathrm{Quantity}\ k\ (\mathrm{Complex}\ R)` is the
  *same* kind layer over a complexified carrier. As a functor $`R \mapsto
  \mathrm{Complex}\ R` it lifts each of the three above — $`\mathrm{Complex}\
  \mathbb{R}` to prove, complex binary32 to certify rounding, $`\mathrm{Complex}\
  \mathrm{Float}` to run. It is a `Carrier` — and a `LawfulCarrier` whenever $`R`
  is, since complex addition is componentwise so the additivity laws lift for free —
  carrying the full field $`+\,-\,\times\,\div`; but it is *unordered* (there is no
  $`\le` on $`\mathbb{C}`), so unlike the real carriers it sits outside the
  ordinal/interval/ratio carrier tower: complex magnitudes are compared by modulus,
  not ranked.

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

## Value representation: vectors and scalar units (R11)

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

## Verified classification: kind-laws that instantiate at the quantity level (R12)

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

## Unit classification (R13)

*R13 — Unit classification needs a third category beyond base and derived:
scale-spanning units.* The SI sorts units into *base* (kilogram, metre, second, ampere,
kelvin, candela, mole) and *derived* (everything built from them). Finkelstein and
Whitehead (_Eur. J. Phys._ 46 (2025) 035701) argue this dichotomy is insufficient: of
the seven base units only four — the kilogram, metre, second, and ampere — are genuinely
*dimensionally independent*, while the kelvin (the dimension of energy, via the Boltzmann
constant), the candela (the dimension of power, via the luminous efficacy), and the mole
(a dimensionless number, via the Avogadro constant) are not — yet each is kept a distinct
coherent unit because it carries a *human-selected coefficient* sized to span vast scales.
They are *scale-spanning units*, a third category. R13 specifies that category, and its
point is the unit-layer twin of R1: *whether a unit is scale-spanning is not a function of
its dimension alone*. The dimension layer can detect that the candela and the mole are
*mechanically reducible* (to power and to one), but it cannot detect the kelvin — this
work keeps thermodynamic temperature an independent dimension (ISO 80000-5 needs it), so
the kelvin's scale-spanning character is visible only through its coefficient, never
through dimensional analysis. The ampere, by contrast, *is* dimensionally independent (it
carries the electromagnetic generator), a genuine base unit — so the third category is
non-empty and distinct from the first. In plain engineering terms: just as a *kind* carries
more than its dimension, a *unit's category* carries more than its dimension; the candela
and mole (ISO 80000-7) and the kelvin (ISO 80000-5) are where this lands on the standard,
the ampere (IEC 80000-6) the base-unit foil.

## Uncertainty and numerical adequacy (R14, R15)

*R14 — Output uncertainty is computed by a provably nested ladder of methods.* A measured input
quantity carries not just a magnitude but a *dispersion*; given the uncertainty of the inputs of a
model $`Y = f(X_1,\dots,X_k)`, the calculus computes the uncertainty of $`Y`. The dispersion is an
*additive* descriptor placed alongside a quantity — moments and cumulants, an inverse-CDF sampler,
and a support range — never a change to the carrier tower, the same discipline R11 used for
vectors. Three methods estimate the output uncertainty at increasing fidelity and cost: GUM
linearization (combine variances), Willink's cumulants method (combine the second *and* fourth
cumulants, recovering the tail shape), and the derivative-free SSPRC sampling method (propagate
each input separately and combine by convolution, capturing full non-linearity). The organizing
claim is that these form a *provably nested ladder* $`\mathrm{GUM} \subset \mathrm{Willink} \subset
\mathrm{SSPRC}`: each coarser method is a projection of the finer one, all resting on the
additivity of cumulants under independent summation. The linearized methods' sensitivity
coefficients $`c_i = \partial f/\partial X_i` are *not* hand-supplied — they come from instantiating
the write-once model at an autograd carrier, R10's representation parametricity put to a new use.
This requirement is realized through Stages 1–2: the reference Monte Carlo propagator, the GUM and
Willink combines (reproducing both source papers' headline numbers as checked facts), the autograd
coefficients, the derivative-free SSPRC pipeline (recovering the fictive model's full non-linear
output uncertainty at ~67× fewer model evaluations than Monte Carlo), and all five ladder theorems —
cumulant additivity (T1), $`\mathrm{gum} = \mathrm{willink}|_{\kappa_4 = 0}` (T2), convolution adds
cumulants (T5), Willink as the $`(\kappa_2,\kappa_4)`-projection of the linearized SSPRC (T3), and
the affine reference equalling the mean (T4) — are proved over `ℝ`. The development is the
*Uncertainty quantification and numerical adequacy* chapter, and the full design is recorded in the
project's `UNCERTAINTY.md`.

*R15 — A floating-point representation is numerically adequate iff it loses no information at the
scale of the input uncertainties.* R10 gives a model exact reals to prove with and IEEE floats to
run with; R15 asks the sharper question the pairing makes possible — does the floating-point
representation silently drop an input uncertainty that *matters*? "Matters" is made precise by
R14's descriptor: the scale is the input dispersion itself, which is exactly why the two areas
*share* one descriptor rather than being two features. The textbook failure becomes checkable — an
input whose contribution $`c_i\,u_i` falls below half a unit in the last place of the accumulated
sum is *numerically invisible*, a silent corruption of the uncertainty result; its dual is
exact-by-Sterbenz cancellation that nonetheless amplifies *relative* uncertainty. Because the model
is written once over `[NumCarrier α]`, the check is obtained *for free* by instantiating it at an
analysis carrier that tracks each value's magnitude and carried uncertainty and flags swamping and
harmful cancellation — sound because the swamping threshold is exactly half a ulp, proved on the
rounding grid over `ℝ` and grounded in TorchLean's binary32 `FP32` unit-in-the-last-place lemmas and
its proven interval arithmetic. This requirement is realized through Stage 3: the executable
`Adequacy` carrier (a `NumCarrier` running the swamping and cancellation checks over `Float`, with a
worked flagged/clean example pair), and the three theorems over `ℝ` — A1 absorption (a sub-½-ulp
perturbation is invisible, its converse fixing the threshold), A2 Sterbenz (near-equal subtraction is
exact, its dual amplifying relative uncertainty), and A3 verdict soundness (the flag holds *iff* the
contribution is lost — sound and complete). Stage 3.1 then lifts A3 to the whole evaluation: A3′
(`DagBound`) abstracts a write-once model as a binary32 `+`/`−` DAG and proves that the `FP32`
measurand's variation over an input box reproduces the exact `ℝ` variation up to a DAG-additive
rounding budget (composed from the per-operation `FP32` half-ulp bounds), collapsing to *equality*
when no site rounds anywhere — so rounding is the sole source of the gap. Stage 3.2 then discharges
the FLT-level Sterbenz: a TorchLean PR (`neural_generic_format_FLT_sterbenz`) lifts A2 from the
self-contained `FLX` model to the gradual-underflow format binary32 actually uses (`fexp32`), so
$`\mathrm{round}_{32}(u - v) = u - v` for near-equal representable operands is a theorem about the real
rounding operator (`round32_sterbenz_exact`), and a near-equal binary32 subtraction is lossless.
Stage 3.3 then closes the executable↔spec gap: since Lean's host `Float` is an opaque FFI type no
theorem can constrain, a second TorchLean PR gives TorchLean's *computable* `IEEE32Exec` model an
executable ULP (`ulpExp`, proved equal to `ulp₃₂` on the finite fragment) and an absorption test
(`absorbs`, the float32 sum unchanged) that is *sound* against the specification — when it fires, the
exact real sum rounds back under `round₃₂` (`exec_verdict_sound`). So the computed adequacy verdict is
provably the specified one, the residual `Float32 ↔ IEEE32Exec` step being an upstream assumption
typeclass rather than an axiom. What remains is extending the DAG to `×`/`÷` and wiring the Axis-U
`cᵢ·uᵢ` yardstick, scoped as sub-stage 3.4 in the project's `UNCERTAINTY.md`.

## Out of scope (for now)

*User-specified base units* — making the dimension system parametric in the chosen base
set (so a quantity's dimensional decomposition is relative to a choice of generators,
expressing e.g. Gaussian-CGS electromagnetism, natural units, or the four-base Finkelstein
system) — was out of scope in an earlier draft and is now *delivered*. We made PhysLib's
`Dimension` itself parametric in its basis and contributed the change upstream
(`github.com/leanprover-community/physlib/issues/1441`, pull request 1447, under review);
the former fixed five-generator type is recovered as the default instance, so no existing
result changes. PKC then *realizes* the angle-augmented basis — PhysLib's five generators
together with *angle* — as one instantiation among several (Gaussian-CGS, natural units,
the four-base Finkelstein system): in it plane angle, solid angle, and a pure number are
dimensionally distinct (solid angle the square of plane angle, `sr = rad²`) and torque is
energy *per angle* (so `torque ≠ energy`), the very separations the five-generator group
cannot draw. The ISO 80000 catalogue stays faithful to the standard (SI convention, plane
angle dimension one) in the five-generator basis and lifts into any of these along the
injective embedding of those generators, with every kind invariant under the lift — a proved
change-of-basis theorem. Committing the catalogue to one reformed basis would merely
privilege a single contested proposal, which is exactly what the parametricity avoids. So the controversy over which
units are base is answered on both layers: a kind is invariant under the choice of base, and
only its dimensional shadow changes. R13 captures the specific base/scale-spanning/derived
controversy over the five-generator basis.

*Value representation in the structural sense* — coordinate frames, tensor
variance (the covariant/contravariant split), bound-versus-free vectors, and frame
transformations — is *not yet specified* here, beyond the ISO 80000-2 §18
numerical-array reading now specified as R11. This *structural* axis is distinct
from R10's *numeric carrier* $`R` and R11's *numerical array*. It is a genuine
systems-engineering requirement, but a *separate, orthogonal* axis: its principled
home is an index *over* the kind, never a layer the kind hangs beneath (the
inversion the *Why a calculus, not a taxonomy* section charges against SysML v2).
Stating it as owed keeps the boundary honest.

## The requirements at a glance — the traceability matrix

The requirements fall into two kinds of obligation. A *verifiable* requirement is
a truth-apt claim about the calculus, discharged by a *checked theorem* — PropertyKindCalculus
*proves* it. An *expressiveness* requirement is a capability the type system must
afford — general-versus-individual (R3), units as chosen values of a kind (R8) —
discharged not by a theorem but by a *construction that typechecks*: that the
witnessing declaration elaborates under CI *is* the demonstration. Conflating the
two would make a capability look like an unfinished proof; separating them lets each
be reported in its own honest vocabulary.

:::traceability_summary
:::

The matrix below is *generated* from the typed `@[requirement …]` annotations
carried by the Lean declarations (harvested by `PropertyKindCalculus.Requirements`),
not maintained by hand. It is organized by the requirement groups introduced
above; within each group, every requirement lists the declarations that
_specify_, _prove_, _implement_, or _exemplify_ it, linked to that declaration's
blueprint node. The *Status* column is likewise derived, not asserted, in the
vocabulary of each requirement's kind: a *verifiable* requirement reads _proved_
and shows links to the very theorems that discharge it; an *expressiveness*
requirement reads _demonstrated_ and links to the constructions that exhibit it;
an undischarged one reads _specified_ (addressed) or _unaddressed_.

Because every annotation attaches to a *real* declaration and every status is a
function of those annotations and the requirement's kind, the matrix cannot drift
from the source — a renamed declaration or a missing proof is a build-time fact, not
a stale cell. (This replaces the hand-maintained requirements-at-a-glance table.)

:::traceability
:::

## What _proved_ is checked to mean

A _proved_ status is stronger than "a theorem of that name compiles", and two
guarantees that `lake build` does not enforce on its own are carried by a dedicated
validation suite (`PropertyKindCalculus.Tests`, one probe per requirement group),
built by CI alongside the dimension and uncertainty layers so that _all sixteen_
verifiable requirements — not only the nine whose theorems live in the Mathlib-free
core — are under regression on every change.

First, each verifiable requirement's theorem has its _axiom profile_ pinned with
`#guard_msgs` over `#print axioms`, so _proved_ means *sorry-free as certified by the
axiom set*, not merely that no `sorry` keyword appears: a proof relocated behind a
`sorry` raises no warning at its call sites, and only the axiom profile exposes it.
(The exportable core stays axiom-free; the Mathlib-backed layers use only the three
standard classical axioms — and the suite pins exactly that.) Second, each theorem is
applied to a _concrete witness_ whose premises are discharged — and, at the degenerate
boundary where a premise _fails_, shown genuinely excluded — so that no requirement is
satisfied *vacuously*: an empty quantifier or an unsatisfiable hypothesis would leave a
theorem true but empty, and the witness is what rules that out.

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

:::iso_doc_table sysmlComparisonTable
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

{include 0 PropertyKindCalculusBlueprint.Chapters.DedicatedKind}

{include 0 PropertyKindCalculusBlueprint.Chapters.Units}

{include 0 PropertyKindCalculusBlueprint.Chapters.Dimension}

{include 0 PropertyKindCalculusBlueprint.Chapters.ScaleSpanning}

{include 0 PropertyKindCalculusBlueprint.Chapters.Interaction}

{include 0 PropertyKindCalculusBlueprint.Chapters.FunctionCalculus}

{include 0 PropertyKindCalculusBlueprint.Chapters.Extensivity}

{include 0 PropertyKindCalculusBlueprint.Chapters.WriteOnce}

{include 0 PropertyKindCalculusBlueprint.Chapters.Uncertainty}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part3}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part4}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part5}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part6}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part7}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part8}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part9}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part10}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part11}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part12}

{include 0 PropertyKindCalculusBlueprint.Chapters.Iso80000Part13}

{include 0 PropertyKindCalculusBlueprint.Chapters.CrossReferences}

{blueprint_graph}

{blueprint_summary}

# License

PropertyKindCalculus and this blueprint are released under the Apache License,
Version 2.0 (SPDX `Apache-2.0`; [license text](https://www.apache.org/licenses/LICENSE-2.0)).

Copyright (c) 2026 California Institute of Technology (Caltech). U.S. Government
sponsorship acknowledged.
