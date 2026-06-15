# PropertyKindCalculus

A Lean 4 formalization of **Dybkær's *[An Ontology on Property for Physical,
Chemical, and Biological Systems](References/ontology-on-property.pdf)*** (2009),
extended with **Flater's full tracking of kinds of quantities**
([NIST Technical Note 1943](References/NIST.TN.1943.pdf), Appendix C).

It continues a line of machine-checkable metrology modeling 
from the Object Management Group (OMG) Systems Modeling Language (SysML)
 Conceptual model of Quantities, Units, Dimensions and Values (QUDV),
then an OML/OWL2 metrology vocabulary grounded in Dybkær — and is the first in
which the *quantity calculus itself*, not just the taxonomy around it, is a
checked artifact. OWL2 captures the taxonomy (specialization, instantiation,
dimensional factoring) but is structurally unable to express the calculus: the
partial kind-interaction algebra, scale-type operator gating, extensivity, unit
conversion, or any algebraic *law* as a provable theorem. Lean has all of it
natively.

The full rationale — the QUDV → OML lineage and how each construct maps into
Lean's type system — is in the [design blueprint](blueprint/) ("Why a calculus,
not a taxonomy").

## On the name

The calculus is over **kinds of *property*** — Dybkær's root notion (§6.19),
which spans nominal, ordinal, and quantitative kinds alike. A **kind of
quantity** is the special case whose scale carries magnitude (§13.3.1, in Lean
`IsQuantity k := k.scale.HasMagnitude`); the `QuantityKind` of QUDT and SysML v2
is therefore *subsumed here* — as a scale-gated leaf of the property-kind spine,
not as its root. The name keeps "Property" in front to make that genus visible
(and to avoid reading the bare word "kind" in its type-theoretic sense). So the
project is broader than a quantity calculus by construction, with quantity kinds
as its motivating special case.

## Representational conventions

* **Meta-concepts** ("what it is to be a kind-of-quantity") → Lean
  `structure`/`class`.
* **Specific kinds** (length, mass, vwc) → **values** of those structures, so
  applications extend the ontology by writing `def`s (open-world), mirroring how
  OML *declares* concepts. A fixed `inductive` would not be extensible.
* **Individual quantities** ("the width of this pencil") → **terms** of the
  quantity type. An individual *instantiates* its kind; it is **not** a subtype.
* **OML relations** map directly: `GeneralUnitaryQuantity`→`KindOfProperty`,
  `Specializes`→`Specializes`, `IndividualUnitaryQuantity`→`IndividualProperty`,
  `HasUnit`/`Instantiates`→ the `u`/`kind` indices.
* **Traceability**: every definition cites Dybkær by section (`§x.y`) or Flater
  by section, so the formalization can be audited against the source.

## Libraries and how to consume them

The package ships six libraries so the core is exportable on its own:

| Library | Source tree | Contents | `lake build` |
|---|---|---|---|
| `PropertyKindCalculus` (default target) | `PropertyKindCalculus/` | the exportable, Mathlib-free ontological spine | `lake build` |
| `Examples` | `examples/` | worked examples for the spine (`PropertyKindCalculus.Examples.*`), Mathlib-free | `lake build Examples` |
| `Dimension` | `dimension/` | the PhysLib-backed coherence layer (library modules only, no examples) — `dim` as the forgetful functor into PhysLib's `Dimension` (`PropertyKindCalculus.Dimension`), Flater's interaction algebra `KMul`/`KDiv` (`PropertyKindCalculus.Interaction`), and the `ℝ` quantity carrier (`PropertyKindCalculus.QuantityReal`); pulls in PhysLib + Mathlib | `lake build Dimension` |
| `DimensionExamples` | `examples/` | worked examples for the Mathlib-backed `Dimension` layer (dimension functor, interaction algebra, `ℝ` quantity carrier, the ISO 80000 catalogue, and the ISO 80000-2 §18 vector quantity) — kept under `examples/` so no library module carries example code; PhysLib + Mathlib-backed (transitively) | `lake build DimensionExamples` |
| `Iso80000` | `iso80000/` | the standards-grounded layer: a references catalogue citing the ISO/IEC 80000 parts by name + version only (no normative content), plus the full ISO 80000-3 *Space and time* (42 items), ISO 80000-4 *Mechanics* (54 items), ISO 80000-5 *Thermodynamics* (54 items), and IEC 80000-6 *Electromagnetism* (85 items) catalogues — quantity-kinds, units, the length/force/energy/power specialization lattices, the dimension-collision and scale-type capstones, and the formalized *Remarks* (several crossing between parts); PhysLib-backed | `lake build Iso80000` |
| `Torch` | `torch/` | the TorchLean-backed instance of the R10 exec/spec refinement bridge — the binary32 `FP32` (rounding spec) and `IEEE32Exec` (executable) carriers realizing `CarrierRefinement`; depends on TorchLean | `lake build Torch` |

The core spine and its `import PropertyKindCalculus` stay Mathlib-free. Note that
`require`-ing the package now also *resolves* the TorchLean dependency (it backs only
the `Torch` library), so a consumer's lock file lists it even when only the core is
imported and `Torch` is never built.

A downstream project depends on the package and imports selectively:

```lean
require PropertyKindCalculus from git "…/PropertyKindCalculus" @ "main"   -- in the consumer lakefile

import PropertyKindCalculus                       -- core spine only, no examples
-- import PropertyKindCalculus.Examples           -- opt in to the examples too
```

The **core spine is Mathlib-free** and builds with only the Lean toolchain. The
PhysLib-backed coherence layer has landed as the separate `Dimension` library —
`dim` as a forgetful functor (`PropertyKindCalculus.Dimension`), Flater's
interaction algebra (`PropertyKindCalculus.Interaction`), and the `ℝ` quantity
carrier (`PropertyKindCalculus.QuantityReal`), with its worked examples in the
`DimensionExamples` library — the layer where PhysLib + Mathlib enter, so a plain
`import PropertyKindCalculus` stays Mathlib-free. PhysLib tracks the same toolchain
this package pins (`leanprover/lean4:v4.30.0`). The soil-moisture *model* will land
as a further library on the same pattern.

## Design blueprint

A [Verso](https://github.com/leanprover/verso) /
[verso-blueprint](https://github.com/leanprover/verso-blueprint) design document
lives in [`blueprint/`](blueprint/). It records the **proved spine** (each node
linked to a real, sorry-free declaration here, so its status is read from the
checked library) and the **capstone theorems we plan to provide** — the
dimension-1 disambiguation, dimensional coherence (`dim` is a homomorphism), the
Flater interaction algebra, unit-conversion round-trip, and extensivity — with a
generated dependency graph and status summary. It is a **separate Lake package**
(it pulls in Verso) so a plain `import PropertyKindCalculus` stays lightweight:

```bash
cd blueprint
lake update && lake build   # type-check the doc + its Lean links
./scripts/ci-pages.sh       # render both outputs + print absolute paths to open
```

Open either `_out/blueprint/html-single/index.html` (one self-contained page) or
`_out/blueprint/html-multi/index.html` (the full per-chapter site) directly as a
file — `ci-pages.sh` post-processes `html-multi` so chapter navigation works over
`file://`. Search and the dependency graph need an HTTP server (`python3 -m
http.server 8000 -d "$PWD/_out/blueprint/html-multi"`). See
[`blueprint/README.md`](blueprint/README.md) for details.

## References

The primary sources are vendored under [`References/`](References/) so the
docstrings' `§x.y` citations resolve to a local copy:

* [`References/ontology-on-property.pdf`](References/ontology-on-property.pdf) —
  René Dybkær, *An Ontology on Property for Physical, Chemical, and Biological
  Systems* (2009).
* [`References/NIST.TN.1943.pdf`](References/NIST.TN.1943.pdf) — David Flater,
  *Architecture for Software-Assisted Quantity Calculus*, NIST Technical Note
  1943 (2016).
* [`References/VIM4-2CD-2023-07-31.pdf`](References/VIM4-2CD-2023-07-31.pdf) —
  JCGM/WG2, *International Vocabulary of Metrology* (VIM), 4th edition, 2nd
  Committee Draft (2CD), 2023-07-31. The `VIM4 2CD x.y` clause citations in the
  docstrings resolve to this copy.

## Roadmap (faithful to Dybkær's chapter structure)

Status: ✅ built & proved · 🚧 next · ⬜ planned

| Module | Source | Status |
|---|---|---|
| `Foundations` — system, object | Dybkær Ch. 3 | ✅ |
| `Scale` — operator-based scale types + monotonicity meta-thm | Ch. 12 (Fig. 12.21) | ✅ |
| `Kind` — kind-of-property / -quantity + scale divisions | Ch. 6, §13.2–3 | ✅ |
| `Specialization` — `Specializes` closure (preorder) + comparability | OML / §6 | ✅ |
| `PropertyKindCalculus.Examples.MiniLengthWidth` (in the `Examples` lib) — length/width/height as checked facts | — | ✅ |
| `Examination` — principle / method / procedure (as defining aspects) + refinement preorder & principle-coherence | Ch. 7, 14 | ✅ |
| `PropertyKindCalculus.Examples.MiniExamination` (in the `Examples` lib) — refinement chain + examination-individuates-kinds as checked facts | — | ✅ |
| `PropertyValue` + `ValueScale` — number × reference; value-comparability equivalence + scale-gated operators | Ch. 9, 16, 10, 17 | ✅ |
| `PropertyKindCalculus.Examples.MiniValueScale` (in the `Examples` lib) — same-kind comparison + quantity-vs-nominal value + value scale as checked facts | — | ✅ |
| `Unit` — metrological unit = *chosen reference quantity of a kind*; commensurability equivalence + number-and-reference round-trip, gated to unitary kinds | Ch. 18, §13.3.3 | ✅ |
| `PropertyKindCalculus.Examples.MiniUnit` (in the `Examples` lib) — metre/centimetre commensurable, metre/kilogram not; ordinal & nominal kinds bear no unit; "5 cm" round-trips as checked facts | — | ✅ |
| `Dimension` — `dim` as the forgetful functor into PhysLib's `Dimension`; the dimension-1 disambiguation capstone (distinct kinds, one dimension) + product-multiplicativity coherence | Ch. 19 | ✅ |
| `PropertyKindCalculus.Examples.Dimension` (in the `DimensionExamples` lib) — vwc/gwc/permittivity/reflectivity all dimension-one yet pairwise-distinct kinds; dimensional algebra (area = L², speed = L·T⁻¹); forgetful-functor coherence as checked facts | — | ✅ |
| `Interaction` — `KMul`/`KDiv` as a curated partial product, the multiplication–division round-trip, and the `dim`-homomorphism coherence capstone | Flater App. C | ✅ |
| `PropertyKindCalculus.Examples.Interaction` (in the `DimensionExamples` lib) — the SI-mechanics algebra: torque × angle = energy holds while torque × angle = torque is rejected; energy ≠ torque yet one dimension; coherence and round-trip as checked facts | — | ✅ |
| `Extensivity` — extensive kinds (additivity over a decomposition) + the n-ary aggregation capstone + a non-extensive counterexample | §13.5 | ✅ |
| `PropertyKindCalculus.Examples.MiniExtensivity` (in the `Examples` lib) — mass aggregates over a three-part assembly (3+5+7=15); volume on mixing is sub-additive (96 < 50+50) as checked facts | — | ✅ |
| `Quantity` — representation-parametric value `Quantity k R` over a `Carrier`-typed numeric carrier; same-kind addition (R4) + additivity laws proved **once** over any lawful carrier; carriers `Int` + `ℝ` (lawful), `Float` (executable) (R10) | — | ✅ |
| `PropertyKindCalculus.Examples.MiniQuantity` (in the `Examples` lib) — the same value layer at `Int` (laws transfer) and `Float` (runs, `#eval`); kind-gated add as checked facts | — | ✅ |
| `PropertyKindCalculus.QuantityReal` (in the `Dimension` lib) — the `ℝ` proof carrier: the `Carrier ℝ`/`LawfulCarrier ℝ` instances for `Quantity k R` | — | ✅ |
| `PropertyKindCalculus.Examples.QuantityReal` (in the `DimensionExamples` lib) — the core additivity laws transfer to `Quantity k ℝ` with no `ℝ`-specific proof as checked facts | — | ✅ |
| `QuantityRefinement` — the exec/spec refinement bridge: `CarrierRefinement E S` + the kind-indexed capstone `Quantity.add_refines` (a law over the lawful spec carrier descends to the exec carrier as one rounding step) (R10 capstone) | — | ✅ |
| `PropertyKindCalculus.Examples.MiniRefinement` (in the `Examples` lib) — a toy rounding carrier instantiating the bridge as checked facts | — | ✅ |
| `Torch` (in the `Torch` lib) — TorchLean instance: unconditional `CarrierRefinement FP32 ℝ` (genuine binary32 rounding) + the conditional `IEEE32Exec` executable refinement (overflow an explicit side condition); `Quantity.add_refines` realized at binary32 | — | ✅ |
| `QuantityVector` — vector/tensor quantities as a numerical array × one scalar unit (ISO 80000-2 §18, R11): pointwise `Carrier (Fin n → R)`, additivity laws transfer | — | ✅ |
| `Iso80000.References` (in the `Iso80000` lib) — references catalogue citing all 12 ISO/IEC 80000 parts by name + version | — | ✅ |
| `Iso80000.Part3` (in the `Iso80000` lib) — ISO 80000-3 *Space and time* **full catalogue** (all 42 items, 3-1.1 … 3-26.3): the length family as a specialization lattice (R2) individuated **by measurement principle** (width ≠ distance proved, not by fiat), the dimension-collision capstones (plane vs solid angle, Hz vs rad/s, velocity vs speed — same dimension, distinct kind), and all dimensional facts as checked computations | ISO 80000-3 | ✅ |
| `UnitPrefix` — SI prefixes (VIM4 §1.19) + prefixed units: the centimetre as *centi* · metre, with the §1.22 conversion factor and §1.20/§1.21 multiple/submultiple read off the projection | VIM4 | ✅ |
| `Iso80000.Part3.AreaElement` (in the `Iso80000` lib) — item 3-3's *Remarks* mathematics formalized analytically: the metric tensor (Gram), the surface element `dA = √g`, the area integral, with `(dA)² = g`, regularity, and the flat-patch correctness anchor proved | ISO 80000-3 | ✅ |
| `Iso80000.Part3.VolumeElement` (in the `Iso80000` lib) — item 3-4's *Remarks* mathematics: the 3×3 metric tensor, the volume element `dV = √g`, the volume integral, and the flat-region correctness anchor (`= |det A|`) proved | ISO 80000-3 | ✅ |
| `QuantityClassification` — verified classification (R12): the kind-law families `ProductKind` / `QuotientKind` / `ReciprocalKind` + their certificates + smart constructors; kind-laws stated to instantiate at the quantity level (axiom-free, Mathlib-free) | — | ✅ |
| `Iso80000.Part3.AreaClassification` (in the `Iso80000` lib) — R12 area instance: a rectangle's area certified as `width × height` by construction, and every certified surface area proved `≥ 0` (property transport from the defining relation) | ISO 80000-3 | ✅ |
| `Iso80000.Part3.DefiningRelations` (in the `Iso80000` lib) — the algebraic *Remarks* (curvature = 1/ρ, repetency = 1/λ, frequency = 1/T, speed = s/t, plane angle = s/r) as R12 kind-laws: the dimension *follows from* the relation (plane angle computed dimension-one because it is a ratio of two lengths) | ISO 80000-3 | ✅ |
| `Iso80000.Part4` (in the `Iso80000` lib) — ISO 80000-4 *Mechanics* **full catalogue** (all 54 items, 4-1 … 4-32): the force family as a specialization lattice (R2) individuated **by measurement principle** (static vs kinetic friction force proved distinct, not by fiat), the textbook torque-vs-energy dimension collision (N·m ≠ J, same dimension `M·L²·T⁻²`), and dimensional facts as checked computations | ISO 80000-4 | ✅ |
| `Iso80000.Part4.DefiningRelations` (in the `Iso80000` lib) — the algebraic *Remarks* as R12 kind-laws, several **cross-part**: momentum = mass × velocity and pressure = force / area build Part-4 kinds out of Part-3 kinds; efficiency computed dimension-one because it is a ratio of two powers | ISO 80000-4 | ✅ |
| `Iso80000.Part5` (in the `Iso80000` lib) — ISO 80000-5 *Thermodynamics* **full catalogue** (all 54 items, 5-1 … 5-36, every sub-suffixed item): the **scale-type** distinction between thermodynamic temperature (ratio) and Celsius temperature (interval) at the same dimension `Θ` (R6 on the standard), the entropy-vs-heat-capacity dimension collision (both `J/K`, not commensurable despite the same unit symbol), the thermodynamic-potential specialization lattice (internal energy, enthalpy, Helmholtz, Gibbs — R2), and dimensional facts as checked computations over the temperature generator | ISO 80000-5 | ✅ |
| `Iso80000.Part5.DefiningRelations` (in the `Iso80000` lib) — the algebraic *Remarks* as R12 kind-laws, several **cross-part**: specific heat capacity = heat capacity / mass and density of heat flow rate = heat flow rate / area build Part-5 kinds out of Part-4 and Part-3 kinds; the ratio of specific heats computed dimension-one because it is a ratio of two specific heat capacities | ISO 80000-5 | ✅ |
| `Iso80000.Part6` (in the `Iso80000` lib) — IEC 80000-6 *Electromagnetism* **full catalogue** (all 85 items, 6-1 … 6-62, every sub-suffixed item), the one IEC-published part: the new **electric-current** base axis (the ampere as `C·T⁻¹` over PhysLib's charge generator), the **scale-type** distinction between gauge-dependent electric potential (interval) and potential difference (ratio) at the same dimension `V` (R6), the AC power family as a specialization lattice (active/reactive/apparent power — R2) carrying three unit strings (`W`/`var`/`VA`) over one dimension, and the power/resistance dimension collisions | IEC 80000-6 | ✅ |
| `Iso80000.Part6.DefiningRelations` (in the `Iso80000` lib) — the algebraic *Remarks* as R12 kind-laws: Ohm's law (resistance = voltage / current), the power product (power = voltage × current), the conductance/admittance/permeance/resistivity reciprocals, and the power factor; the electric-current law (current = charge / time) **crosses into Part 3**; the power factor computed dimension-one because it is a ratio of two powers | IEC 80000-6 | ✅ |
| `Iso80000` — the remaining parts (1, 2, 7–12) quantity-kinds + units | ISO/IEC 80000 | ⬜ |
| `DedicatedKind` — kind × system × component | Ch. 20 | ⬜ |
| `Model.SI` — SI base kinds, verified well-formed | — | ⬜ |
| `Model.SoilMoisture` — vwc/gwc/permittivity/reflectivity/… | — | ⬜ |

## What builds today

`lake build` compiles the spine and the worked examples with **no `sorry`**,
proving: `ScaleType` is a linear order; operator availability is monotone in
scale; `Specializes` is a preorder; mutual comparability is reflexive/symmetric;
examination refinement (procedure ⊑ method ⊑ principle) is a preorder that
preserves the underlying principle, and the examination principle is a defining
aspect that individuates kinds; that a *property value* is comparable only with
values of the same kind — comparability is an equivalence relation and comparable
values share the same operator set — and that a *value scale* holds only mutually
comparable values, with operator availability inherited monotonically from the
scale layer; that a *metrological unit* is a chosen reference of a *unitary* kind
only — nominal and ordinal kinds bear none (Dybkær §9.13.4) — with commensurability
("of the same kind") an equivalence relation and the number-and-reference form
(`number × unit`) a faithful round-trip; and (in the examples) that `width`/`height` are distinct sub-kinds of
`length` — distinct *because they are examined differently*, yet mutually
comparable — with "the width of a pencil" specified as an instance, and "5 cm"
specified as a quantity value distinct in kind from a mass or a blood-group value,
measured in a centimetre that is commensurable with the metre but not the kilogram;
and that an *extensive* kind aggregates additively over a decomposition of a system
into disjoint parts — the value of the whole is the sum over the parts, proved by
induction on the decomposition (the aggregation capstone) — while *volume on mixing*
is a checked counterexample (50 mL water + 50 mL ethanol ≈ 96 mL < 100 mL), so it is
**not** extensive and assuming additivity would be unsound; and that a *quantity
value* is **parametric in its numeric representation** (R10) — `Quantity k R` is
indexed by both a kind `k` and a carrier type `R`, with same-kind addition
`Quantity k R → Quantity k R → Quantity k R` (so adding a length to a mass is a
type error), and the additivity laws (commutativity, associativity, the zero unit)
proved **once** over any lawful carrier and reused verbatim at `Int` and (in the
examples) holding for free, while the same layer runs at `Float` — a `Carrier` but
deliberately not a *lawful* one, since floating-point addition is not associative,
which is exactly the gap the exec/spec refinement bridge closes: a
`CarrierRefinement E S` packages a forgetful `toSpec` and a spec-side `round` with
the law `toSpec (x +ᴱ y) = round (toSpec x +ˢ toSpec y)`, and its kind-indexed
capstone `Quantity.add_refines` (axiom-free) lifts that to quantities, so a law
proved over the lawful carrier descends to an executable one as a single rounding
step. The same carrier-parametricity gives *vector* quantities for free
(ISO 80000-2 §18, R11): a numerical vector `Fin n → R` is a lawful carrier
pointwise, so a vector quantity is one kind with one **scalar** unit over a
numerical array — not a per-coordinate bag of number×unit values — and the
additivity laws transfer to it unchanged.

`lake build Dimension` additionally checks the PhysLib-backed coherence layer
(this is the one library that pulls in PhysLib + Mathlib). The dimension module
proves that `dim` — the forgetful functor that sends a kind to its PhysLib
`Dimension` — is **not injective**, the motivating capstone. Volumetric and
gravimetric water content (and relative permittivity and reflectivity) are
pairwise-distinct kinds that all forget to the dimensionless `1`, so PhysLib's
`Dimension`, and any dimension-only type system, cannot tell them apart while the
kind layer keeps them distinct. The functor still preserves products (the
dimension of a product is the product of the dimensions, exponents adding), and
the dimensional algebra computes in PhysLib's group (area = L², speed = L·T⁻¹).

The interaction module then adds Flater's **kind product** as a *curated, partial*
ternary relation (`InteractionAlgebra`): an application lists the products it
sanctions, and each must be dimensionally coherent — bundling that obligation with
the relation makes the **homomorphism** `KMul k₁ k₂ k₃ → dim k₃ = dim k₁ · dim k₂`
hold by construction (this is the coherence capstone). Its division dual `KDiv` is
the product read backwards, so multiplication and division are inverse by
definition. The worked SI-mechanics algebra carries the point: `torque × angle =
energy` is sanctioned while `torque × angle = torque` is **rejected** — even
though the dimensions would balance — because dimensional coherence is necessary,
not sufficient; `energy ≠ torque` as kinds yet they share one dimension. All
sorry-free.

`lake build Dimension` also provides the **`ℝ` proof carrier** for the
representation-parametric `Quantity k R` (`PropertyKindCalculus.QuantityReal`): the
`Carrier ℝ`/`LawfulCarrier ℝ` instances, so the additivity laws proved once in the
core specialize to `Quantity k ℝ` with no `ℝ`-specific proof — the R10 payoff in one
line. The `Int` and `Float` carriers ship with the Mathlib-free core; `ℝ` lands here
because it needs Mathlib.

`lake build DimensionExamples` then checks the Mathlib-backed worked examples — the
dimension functor, the interaction algebra, the `ℝ` quantity-law transfer, the
ISO 80000 catalogue, and the ISO 80000-2 §18 vector quantity — kept under
`examples/` so that no library module carries `example`/`#eval`/`#guard` code
(the Mathlib-free spine examples stay in the `Examples` library).

`lake build Iso80000` checks the standards-grounded layer: a references catalogue
that cites each of the twelve ISO/IEC 80000 parts by name and version only — e.g.
`IEC 80000-6, Edition 2.0, 2022-11`, with no normative content reproduced — and the
**full catalogue of ISO 80000-3 *Space and time*** (all 42 items, 3-1.1 … 3-26.3),
each carrying its exact item locator as data and its dimensional facts checked in
PhysLib's group. Part 3 is where the calculus meets the real standard: its length
family (width, height, distance, radius, …) is specified as a specialization lattice
over the general length kind, each species individuated **not by fiat but by a
measurement principle** (so `width ≠ distance` is *proved*, requirement R2); its
dimension collisions (plane vs solid angle, hertz vs radian-per-second, velocity vs
speed — same dimension, distinct kind) are the dimension-1 disambiguation on standard
quantities; and selected *Remarks* are formalized as mathematics — the surface and
volume elements (`√g`), and the algebraic relations (curvature, frequency, speed,
plane angle) as R12 kind-laws where the dimension *follows from* the relation.

The same build also checks the **full catalogue of ISO 80000-4 *Mechanics*** (all 54
items, 4-1 … 4-32). Part 4 carries the calculus's two theses on textbook quantities:
the force family (weight, the friction forces, drag, …) is a specialization lattice
over the general force kind, individuated by measurement principle (so static and
kinetic friction forces are *proved* distinct kinds though dimensionally identical,
R2); the torque-versus-energy collision is the headline dimension clash — both are
`M·L²·T⁻²`, yet the newton metre is not commensurable with the joule, because the
kinds differ; and the algebraic *Remarks* are R12 kind-laws, several **crossing into
Part 3** — momentum is mass × velocity, pressure is force / area, so mechanical kinds
are built out of space-and-time kinds — with efficiency computed dimension-one because
it is a ratio of two powers.

The same build checks the **full catalogue of ISO 80000-5 *Thermodynamics*** (all 54
items, 5-1 … 5-36, every sub-suffixed item included). Part 5 brings the one axis Parts
3 and 4 could not show — the **scale type**: thermodynamic temperature and Celsius
temperature share the dimension `Θ`, yet the first is ratio-scale (the kelvin admits
`×`,`÷`) and the second only interval-scale (a ratio of Celsius temperatures is
undefined), so the two are *proved* distinct kinds by scale alone (requirement R6 on
the standard). It sharpens the dimension-collision thesis with entropy versus heat
capacity — both `J/K`, not commensurable even though their units carry the *same
symbol* — and lays out the thermodynamic potentials (internal energy, enthalpy, the
Helmholtz and Gibbs energies) as a specialization lattice over energy (R2); the
algebraic *Remarks* are R12 kind-laws, several **crossing into Parts 3 and 4** —
specific heat capacity is heat capacity / mass, the density of heat flow rate is heat
flow rate / area — with the ratio of specific heats computed dimension-one because it
is a ratio of two specific heat capacities.

The same build checks the **full catalogue of IEC 80000-6 *Electromagnetism*** (all 85
items, 6-1 … 6-62, every sub-suffixed item included) — the one IEC-published part. Part
6 brings the last SI base quantity the earlier parts did not exercise, **electric
current**: PhysLib takes electric charge `C` as its generator, so the ampere appears as
`C·T⁻¹` and every electromagnetic dimension — capacitance `C²·M⁻¹·L⁻²·T²`, resistance
`M·L²·T⁻¹·C⁻²`, magnetic flux `M·L²·T⁻¹·C⁻¹` — is a checked computation over it. It
repeats the **scale-type** thesis on electromagnetism: electric potential is
gauge-dependent (fixed only up to an additive reference), hence interval-scale, while
electric potential difference, of the same dimension `V`, is ratio-scale — *proved*
distinct kinds by scale alone (R6). And it gives the sharpest **dimension does not
classify** case yet: active, reactive, and apparent power are all `M·L²·T⁻³`, yet the
standard spends *three* unit strings on the one dimension — the watt, the var, the
volt-ampere — and arranges them as a specialization lattice over power (R2); the
algebraic *Remarks* are R12 kind-laws — Ohm's law, the power product, the reciprocal
pairs — with the electric-current law (current = charge / time) **crossing into Part 3**
and the power factor computed dimension-one because it is a ratio of two powers.

`lake build Torch` checks the TorchLean-backed instance of the refinement bridge —
the only library that depends on TorchLean. `FP32` (TorchLean's binary32 rounding
spec) is an *unconditional* `CarrierRefinement` of `ℝ`, so `Quantity.add_refines`
holds at genuine binary32; the *executable* `IEEE32Exec` refines `ℝ` only on the
finite, no-overflow path, with overflow carried as an explicit hypothesis rather
than silently dropped — the class of failure this rigor work exists to surface.
