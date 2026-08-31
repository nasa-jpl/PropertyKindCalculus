# Requirements

Thirty-one requirements in nine tiers.

**On the numbering.** `MR` for *metrology requirement*, one flat family in tier order. It is
deliberately not `R`, which PKC's own `requirements/` catalogue already uses for the
blueprint's R1–R20, nor `M`, which [MOTIVATION.md](MOTIVATION.md) uses for its reasons.

MR1–MR19 were written first, against the harmonic oscillator, and the
[case-study Lean files](CaseStudies/HarmonicOscillator/README.md) cite them by number.
MR20–MR31 were added after surveying the twelve `API-map.yaml` files under
`PhysLib/SpaceAndTime` and `PhysLib/ClassicalMechanics`. MR32 was appended after the
first scoring pass, when tracing this list against PKC's own catalogue showed R2's subject
matter (`H = T + V`) on the page with no MR asking anything of it. **That history is not a
distinction** — a requirement's tier says what it is; where it was first noticed says
nothing. The meaningful division is the one below: Tiers 1–6 are defects against PhysLib's
own stated intent, Tiers 7–8 are what applying PhysLib needs and PhysLib never claimed to
provide, Tier 9 is process.

**What counts as satisfied.** Evidence that compiles: a `#check_failure` probe, a theorem
exhibiting the wrong answer, or an `example` showing that something which should be rejected
type-checks. *Satisfied by convention*, *satisfied if the author is careful*, and *satisfied
by a naming discipline* all count as **failed** — the whole question is what the checker
enforces when the author is not careful.

**Over-rejection is also failure.** A scheme that rejects `m_A + m_B` has not satisfied
[MR8](#mr8-aggregation-is-licensed-per-kind-in-both-directions); it has traded one error for
another.

**PhysLib is not scored against requirements it never adopted.** Tiers 7 and 8 are
requirements for *applying* PhysLib, not defects in it. The evidence cited under Tiers 1–6
and 9 is measured against PhysLib's own stated intent — its docstrings, its module docs, its
API maps — and nothing else.

---

## Tier 1 — Dimensional analysis

What `Dimension` already does well. PhysLib satisfies this tier wherever the layer is
actually used; the finding is that it almost never is.

### MR1. Dimensional homogeneity

A sum of quantities with different dimensions is rejected.

*Fails today:* `IsInertial.velocity : EuclideanSpace ℝ (Fin d)` has the same type as the
displacement `frame.origin t₂ -ᵥ frame.origin t₁` it is defined from, so `L + L·T⁻¹`
compiles. In `RigidBody/Motion.lean`, `comTrajectory`, `centerOfMassVelocity` and
`linearMomentum` are all `Time → Space d`, so position `+` momentum compiles.

### MR2. Derived dimensions are computed, not annotated

The dimension of a derived quantity is *inferred* from the expression, not written down
beside it.

*Fails today:* `Temperature.β`'s docstring reads "This has dimensions equivalent to
`Energy`". Since `β = 1/(kB·T)` and `kB` is energy per temperature, `β` is **inverse**
energy. The arithmetic is right; the annotation is wrong and nothing can disagree with it.

### MR3. Unit-change covariance

Changing the unit system acts on every quantity through the same law, and the law is
checked rather than asserted.

*Fails today:* four unit types exist — `TimeUnit`, `LengthUnit`, `MassUnit`,
`TemperatureUnit` — and **none is connected to the quantity type it measures**. See
[M4](MOTIVATION.md#m4-four-unit-types-none-connected-to-its-quantity).

---

## Tier 2 — What dimension cannot see

Every requirement in this tier concerns two quantities with the *same* dimension that must
not be interchanged. No refinement of the dimension group reaches any of them.

### MR4. Same-dimension kinds stay apart

Frequency `ν` in Hz and angular frequency `ω` in rad/s are both `T⁻¹` and are not the same
quantity. Interchanging them is a factor of 2π.

*Fails today, and PhysLib says so:* `SpaceAndTime/Time/Basic.lean` — *"since the choice of
units and origin is left implicit, Lean will not catch inconsistencies in the choice of units
or origin when working with `Time`"* — and then names the harmonic oscillator, with `t` and
`ω` as the pair the reader must keep consistent.

### MR5. Scale type gates the operators

Ratios are illegal on interval-scale quantities. An absolute energy, a Celsius temperature,
an electric potential and a differential entropy have no absolute zero; their *differences*
do.

*Fails today:* `Time` is documented as having "a given but arbitrary choice of origin" —
interval scale — and is given `Module ℝ`, `Norm` and `InnerProductSpace`. So `t.val • v` and
`(t₂ - t₁).val • v` are equally well-typed and only the second is meaningful. In
`StatisticalMechanics/CanonicalEnsemble`, `differentialEntropy` (documented: "not absolute
… can be negative") and `thermodynamicEntropy` (absolute) are separated by their names.

### MR6. Degrees of freedom are distinguishable

For an anisotropic oscillator the per-axis frequencies are not interchangeable, and isotropy
is a *theorem* about a particular system rather than a property of the type.

### MR32. Specialization keeps kinds comparable

*(Numbered out of tier order: appended after the first scoring pass, under the same append
discipline as PKC's own R16 onward. Tier 2 by content — see the numbering note at the top.)*

Kinetic energy, potential energy and total energy are three kinds, not one — each
individuated by its own examination — and a function expecting the potential rejects the
kinetic. Yet `H = T + V` stays writable, licensed by the fact that both terms *specialize*
the common kind energy, with the sum landing at that join. Two-sided, like
[MR8](#mr8-aggregation-is-licensed-per-kind-in-both-directions): a scheme that distinguishes
the family but rejects its sum has traded one failure for the other — Attempt 3's
`tagging_dilemma`, transposed from objects to specializations — and a scheme that licenses
the sum by collapsing the family into one kind cannot state which term is which.

*Fails today:* PhysLib's `HarmonicOscillator` types `kineticEnergy`, `potentialEnergy` and
`energy` all as `Time → ℝ` or `ℝ`. At first scoring it was also a requirement **PKC itself
did not sweep**: the lattice half was theorems (`Specializes`, `MutuallyComparable` — R2's
machinery), but nothing at the quantity level consumed them, so the licensed sum at the
join was missing machinery — scored ⚠️ against PKC by rule 5. That machinery has since
landed, built to this requirement's specification: `PropertyKindCalculus.SpecializationLift`
(`Quantity.widen`, the curated `KindJoin` table, the sum and the comparison at the join),
and the cell is ✅ (`CaseStudies/HarmonicOscillator/Attempt4Pkc.lean`, section MR32).

---

## Tier 3 — Two objects

### MR7. Object identity

`m_A` and `m_B` are not interchangeable; `ω_A * x_B` is rejected.

*Fails today:* there is no expression anywhere in PhysLib for "the mass of *this* body as
opposed to that one". `RigidBody.mass` is *the* mass; `M₁.mass + M₂.mass` type-checks and
means nothing in particular.

### MR8. Aggregation is licensed per kind, in both directions

`m_A + m_B = m_pair` is licensed because mass is extensive. `ω_A + ω_B` is **not** the
frequency of the pair, and must be rejected. Both directions are the requirement: a scheme
that achieves the second by forbidding the first has failed.

The two rows differ in exactly one respect — whether the whole's value is the sum of the
parts' — and nothing in a dimension, a unit, or a magnitude distinguishes them.

### MR9. Whole-system quantities

A coupling constant `k_c` is a property of the *pair*, not of either member. It is not
`k_A`, not `k_B`, and not their sum.

*Fails today:* `RigidBody.centerOfMass` is exactly such a quantity, and its type does not
record it, so it is interchangeable with any other `Space d`.

### MR10. Provenance survives a function boundary

A quantity handed to a helper function arrives carrying what it is. The structure-bundling
defence — "the record *is* the object" — ends at the first function that takes a field
rather than the record.

---

## Tier 4 — Ergonomics

Scored by the same rules as everything else, and the tier PKC loses.

### MR11. Authoring ergonomics

How much ceremony surrounds the physics when the formula is written, and how much is needed
to stand a model up before any formula can be written at all.

This is the strongest objection to the whole proposal and it is
[partly correct](CaseStudies/HarmonicOscillator/README.md#tier-4-the-ranking-reverses).
[MR28](#mr28-kind-generic) is the answer to it — and `kind_algebra`
(`PropertyKindCalculus.KindAlgebra`, minted from this MR's verdict) has since collapsed the
stand-up cost to the kind equations themselves, one declaration per model.

### MR12. Rendering ergonomics

Whether the source can be presented back as typeset mathematics with the bookkeeping
elided — so the ceremony the author writes is ceremony the reader never sees.

---

## Tier 5 — Computation

### MR13. Carrier parametricity

One model definition instantiated at more than one carrier: `ℝ` for proofs, `Float` for
execution, with both being *the same model* rather than two declarations that happen to
agree.

*Fails today, and PhysLib says so:* `Units/Basic.lean` records that other Lean unit
libraries "allow for or work in Floats, allowing computability and the use of `#eval`. This
is currently not possible with the more theoretical implementation here in Physlib which is
based exclusively on Reals."

### MR14. Complex-valued quantities

A quantity whose value is *fundamentally* complex — a mechanical impedance, a wavefunction
amplitude — is held and combined, not merely stored.

### MR15. Exec and spec agree

`Float` addition is not associative, so a law proved over `ℝ` is not automatically true of
the code that ships. The relationship between them must be a theorem.

---

## Tier 6 — Geometry

### MR16. A carrier morphism cannot change the kind

A change of *numbers* — `ℝ ↪ ℂ`, `ℝ → Float` — carries the quantity to the same kind at a
new carrier. It is not an opportunity to reinterpret what the quantity is.

### MR17. A vector quantity is one quantity

ISO 80000-2 §18: a vector quantity is a single quantity whose value is a numerical array,
not a tuple of independent scalar quantities. Refusing the meaningless componentwise product
by refusing to multiply anything is **not** a solution.

### MR18. Frame covariance, and what survives it

Components carry the frame they were read in. Two readings in different frames have
different types; a scalar product is invariant under an orthonormal change of frame, and an
extracted component is emphatically **not**.

*Fails today:* `angularVelocity` (lab, `Ω = Ṙ Rᵀ`) and `bodyAngularVelocity` (body,
`Ω = Rᵀ Ṙ`) are both `RigidBodyMotion 3 → Time → Fin 3 → ℝ`. The frame is the substring
`body`. See [M5](MOTIVATION.md#m5-a-correctness-constraint-enforced-by-not-using-an-abbreviation).

### MR19. An indexed family is not a set of vector components

`ω : Fin d → ℝ` — one independent frequency per degree of freedom — and a position
`x : Fin d → ℝ` are written identically and obey different laws under a change of frame.
PhysLib's own `HarmonicOscillator` structure contains both.

---

## Tier 7 — Systems and assemblies

The gap between *formalised physics* and *physics you can apply to a built thing*. PhysLib
addresses none of this, reasonably, because nothing in its charter said it should.

### MR20. A quantity belongs to a named part of a named system

`DedicatedKind`'s `System — Component ; kind` triple. A quantity is not "a mass"; it is "the
mass of the left-front wheel of rover 1".

**Acceptance criterion — two rovers.** Declare two systems, `rover1` and `rover2`, each with
chassis, four wheels, four drive motors, a mast. Then:

1. `rover1.totalMass` is **verifiably** the sum of the masses of rover 1's own components —
   a theorem, not a definition that happens to add the right things.
2. Substituting any of rover 2's component masses into rover 1's total **fails to compile**.
3. The exhaustiveness in (1) is checked: omitting a component of rover 1 from the sum is
   also a failure, so the total cannot silently under-count.

Two rovers rather than one, because a single system cannot distinguish "the sum of the
parts" from "the sum of some masses of the right dimension". The second rover is what makes
the requirement falsifiable.

### MR21. Assembly is licensed per kind and two-sided

Masses of parts sum to the mass of the whole. Temperatures do not. Angular velocities do
not. `Extensive` is the licence. This is [MR8](#mr8-aggregation-is-licensed-per-kind-in-both-directions)
at system scale, and it is two-sided for the same reason.

*Relevant today:* the parallel-axis theorem
(`inertiaTensorAbout_eq_centerOfMass_add_pointMass`) is exactly an assembly law, and there is
no notion of "these bodies are the parts of that body" for it to be a law *about*.

### MR22. Whole-system quantities are not part quantities

A wheelbase, a total angular momentum about the assembly's own centre of mass, a coupling
constant. [MR9](#mr9-whole-system-quantities) generalised to an assembly of many parts.

### MR23. Interface quantities carry both systems they join

A motor delivers a torque *to* a wheel; a thermal model exchanges a flux *across* a
boundary. The quantity names both endpoints, so a torque intended for the left wheel cannot
be delivered to the right one.

*Contested.* This is systems engineering, not physics, and a maintainer is entitled to place
it in the layer above. See [PLAN.md](PLAN.md#what-a-maintainer-would-and-would-not-sign).

### MR24. A dedication carries provenance

Every part-quantity in an applied model is one of: measured, specified by requirement,
derived from others, or assumed. An equation whose inputs have no provenance is a proof; an
equation whose inputs do is an application.

*Contested*, on the same grounds as [MR23](#mr23-interface-quantities-carry-both-systems-they-join).

---

## Tier 8 — Write-once parametricity

**This is the tier that pays for [MR11](#mr11-authoring-ergonomics).** The ceremony is paid
per definition; the benefit is collected per instantiation. A library is exactly the setting
where that ratio is favourable.

A change of reference frame in 1D, 2D and 3D, for proofs in `ℝ` and for a `Float32` kernel,
for position and velocity and angular momentum, is **one** piece of mathematics. Written
without parametricity it is eighteen — and every one of the eighteen is a place where a name
prefix can disagree with the intent.

### MR25. Dimension-generic

One definition serves `d = 1, 2, 3`.

*PhysLib is good at this and deserves credit:* `Space d`, `GalileanGroup d`, `RigidBody d`,
`ReferenceFrame d`. But the parametricity stops where the metrology starts.
`angularVelocityTensor` is defined for all `d`; `angularVelocity` exists only at `d = 3`
because it needs the hat map; so `rotationalKineticEnergy`, `angularMomentum` and both König
theorems are `d = 3` only. `HarmonicOscillator` is hard-wired to `EuclideanSpace ℝ (Fin 1)`.
The library is dimension-generic in its geometry and dimension-specific in its mechanics.

### MR26. Frame-generic

The same equation instantiated in the lab frame and in the body frame, with the frame as a
type index rather than a name prefix. [MR18](#mr18-frame-covariance-and-what-survives-it) as
a library requirement.

*This is PhysLib's own request.* `ReferenceFrame.lean` §C: *"It intentionally records the
coordinate frame but not the physical dimension … Their different physical roles, units, and
transformation laws must be supplied by the surrounding definitions."* Three deferrals —
physical role, units, transformation law — which are `KindOfProperty`, `Dimension` and
`Variance`, item for item.

### MR27. Carrier-generic

One authored form, instantiated at `ℝ` for proofs and at `Float32`/`Float64` for execution,
with [MR15](#mr15-exec-and-spec-agree) relating them.
[MR13](#mr13-carrier-parametricity) as a library requirement.

This is the single largest obstacle to *applying* PhysLib. Today an applied user must
re-implement the equation, and the relationship between the formalisation and the code that
ships is prose.

### MR28. Kind-generic

A *combinator* — the chain rule, the parallel-axis theorem, the König split, a change of
frame — is stated once over an abstract kind and its `KindMul`/`KindDiv` result, and thereby
applies to every quantity of the right shape.

Carrier-generic means one definition runs at several *number types*. Kind-generic means one
theorem covers several *quantities*. **Without it the kind layer multiplies the theorem count
by the number of kinds and the ergonomic objection is correct.** With it, the ceremony is paid
once per operator in an `OperatorTable` and collected at every use.

This is the requirement that decides whether the transition is affordable, and the reason the
demonstration must use the `OperatorTable` idiom and never the longhand witness form.

---

## Tier 9 — Evidence and adoption

### MR29. Every satisfied requirement has a machine-checkable witness

PhysLib maintains `API-map.yaml` files with `done: true|false` and a `location:`. Today that
is a claim a human checked once. The proposal is one additional field:

```yaml
  - description: "…"
    done: true
    location: "Physlib/SpaceAndTime/Space/Module.lean (…)"
    checked_by: "Physlib/SpaceAndTime/Space/Metrology.lean (#kind_dimensional_coverage)"
```

*The failure mode this guards against:* `Space` requirement 12 reads "*The API contains the
type `LengthUnit` of choices of length unit, with scaling and concrete units*". It is **fully
satisfied as written** — and `LengthUnit` is imported by no part of `Space`. The requirement
is true and the API is not connected. The improvement is the *missing* requirement this makes
visible: "the API contains the checked statement that `Space`'s coordinates carry dimension L
and that `LengthUnit` is the unit of that kind."

### MR30. The unkinded surface is measured

`#kind_unkinded` / `#kind_unkinded_clean`, with one tier PhysLib needs that the soil-moisture
model did not: **erased to reach a Mathlib API**. Every quantity eventually becomes an `ℝ` to
reach `fderiv`, `MeasureTheory.integral`, `InnerProductSpace`. That is legitimate and
permanent. The requirement is that it be counted and located, not that it be zero.

*Canonical instance:* `origin t₂ -ᵥ origin t₁ = (t₂ - t₁).val • velocity` is dimensionally
correct only because `.val` erased `Time` to a bare `ℝ` first. The balance is carried **by**
the erasure rather than checked **through** it.

### MR31. Adoption is scoped and monotone

A clean audit is a claim about its scope, never about the library. `#kind_mint_ratchet` per
module root, so `SpaceAndTime/Space` can be covered while `QFT` is not — no flag day, no
coordination cost between contributors.

---

## Index

| tier | requirements |
|---|---|
| 1 · dimensional analysis | [MR1](#mr1-dimensional-homogeneity) [MR2](#mr2-derived-dimensions-are-computed-not-annotated) [MR3](#mr3-unit-change-covariance) |
| 2 · what dimension cannot see | [MR4](#mr4-same-dimension-kinds-stay-apart) [MR5](#mr5-scale-type-gates-the-operators) [MR6](#mr6-degrees-of-freedom-are-distinguishable) [MR32](#mr32-specialization-keeps-kinds-comparable) *(appended)* |
| 3 · two objects | [MR7](#mr7-object-identity) [MR8](#mr8-aggregation-is-licensed-per-kind-in-both-directions) [MR9](#mr9-whole-system-quantities) [MR10](#mr10-provenance-survives-a-function-boundary) |
| 4 · ergonomics | [MR11](#mr11-authoring-ergonomics) [MR12](#mr12-rendering-ergonomics) |
| 5 · computation | [MR13](#mr13-carrier-parametricity) [MR14](#mr14-complex-valued-quantities) [MR15](#mr15-exec-and-spec-agree) |
| 6 · geometry | [MR16](#mr16-a-carrier-morphism-cannot-change-the-kind) [MR17](#mr17-a-vector-quantity-is-one-quantity) [MR18](#mr18-frame-covariance-and-what-survives-it) [MR19](#mr19-an-indexed-family-is-not-a-set-of-vector-components) |
| 7 · systems and assemblies | [MR20](#mr20-a-quantity-belongs-to-a-named-part-of-a-named-system) [MR21](#mr21-assembly-is-licensed-per-kind-and-two-sided) [MR22](#mr22-whole-system-quantities-are-not-part-quantities) [MR23](#mr23-interface-quantities-carry-both-systems-they-join) [MR24](#mr24-a-dedication-carries-provenance) |
| 8 · write-once parametricity | [MR25](#mr25-dimension-generic) [MR26](#mr26-frame-generic) [MR27](#mr27-carrier-generic) [MR28](#mr28-kind-generic) |
| 9 · evidence and adoption | [MR29](#mr29-every-satisfied-requirement-has-a-machine-checkable-witness) [MR30](#mr30-the-unkinded-surface-is-measured) [MR31](#mr31-adoption-is-scoped-and-monotone) |

---

## Traceability to PKC's own catalogue

PKC carries its own requirement catalogue, `R1–R25`
(`requirements/PropertyKindCalculus/Requirements/Catalogue.lean`), with a generated
traceability matrix in its blueprint. The MR list is not that catalogue: an R is a
specification of PKC, discharged inside PKC; an MR is a benchmark obligation, scored
against four designs and against PhysLib as shipped. Where they meet, **the MR is the
adversarial restatement of the R** — the same claim handed a physics problem that rival
designs attempt first — so this table is requirement *validation* in the systems
engineering sense, and it ran in both directions: R21–R25 were minted into PKC's
catalogue from this list. The full account is the blueprint's *Requirement validation —
the ForPhysLib benchmark* section.

| MR | traces to | how |
|---|---|---|
| MR1 | R7 + R4 | delegated to the dimension layer PKC consumes |
| MR2 | R5 + R7 | delegated — dimension of a product is computed by the homomorphism |
| MR3 | R17 + R16 | delegated — unit covariance and the reference round-trip |
| MR4 | R1 | restated: discriminate within a dimension |
| MR5 | R6 | restated: scale gates the operators |
| MR6 | R1 + R19 | per-axis kinds are distinct kinds of distinct roles |
| MR7 | R19 | restated: object identity in the type |
| MR8 | R9 | restated: extensive aggregates, intensive does not — both directions |
| MR9 | R22 | a whole-system quantity is a dedication to the *pair* |
| MR10 | R19 + R23 | identity survives the boundary; provenance records the crossing |
| MR11 | **R21** | *minted from this MR* — the ceremony is pure, proved |
| MR12 | **R25** | *minted from this MR* — rendering pinned by `#guard_msgs` |
| MR13 | R10 | restated: carrier parametricity |
| MR14 | R10 | the complexified carrier is the same kind layer over `Complex R` |
| MR15 | R10 — **not R15** | traces to the `CarrierRefinement` exec/spec bridge; PKC's R15 is the *sharper* claim (adequacy at the scale of the input uncertainties) and no MR states it yet |
| MR16 | R10 + R1 | a carrier morphism moves `R`, never `k` |
| MR17 | R11 | restated: ISO 80000-2 §18, one quantity |
| MR18 | R20 | restated: frame and variance indices, invariance as a theorem |
| MR19 | R11 + R20 | an indexed family is not a reading in a basis |
| MR20 | **R22** | *minted from this MR* — the two-rover construction |
| MR21 | R9 + R22 | licensed assembly, at system scale, two-sided |
| MR22 | R22 | a whole-system dedication is not a part dedication |
| MR23 | — | **not minted**: no PKC interface machinery yet; gated on Exhibit D ([PLAN.md](PLAN.md#what-this-benchmark-did-to-pkcs-own-requirements)) |
| MR24 | **R23** | *minted from this MR* — provenance with a boundary contract |
| MR25 | — | **not minted**: gated on the kind-generic König split (Exhibit A) |
| MR26 | R20 | frame-generic is the functorial frame action |
| MR27 | R10 | restated: prove at `ℝ`, run at `Float32`, agreement as a theorem |
| MR28 | R12 | a combinator is a kind-law instantiating at the quantity level |
| MR29 | R12 + R24 | a witness is a certificate; the API map is its adoption vehicle |
| MR30 | **R24** | *minted from this MR* — the enumerable unkinded surface, with the interface tier |
| MR31 | **R24** | *minted from this MR* — the scoped, monotone ratchet |
| MR32 | **R2** | *the near miss, closed in both directions* — comparability without identity, on the oscillator's own `H = T + V`; the lattice is R2's theorems, and the quantity-level sum at the join is now R2's machinery too (`SpecializationLift`, minted from this MR) |

**Not validated by this benchmark:**

- R13 (scale-spanning units) — the surveyed physics presents no such unit: no decibel,
  no logarithmic scale anywhere in the two mechanics directories.
- R14 (uncertainty ladder) — no quantity in the survey carries a measured uncertainty.
- R15 (numerical adequacy) — falls with R14: the benchmark does exercise `Float`
  carriers (Tier 5), but R15 is defined relative to *input uncertainties*, which never
  appear.
- R18 (coverage intervals) — no acceptance or conformity decision occurs in the
  surveyed physics.

R2 was the fifth entry — the near miss, its subject matter (`H = T + V`) on the page with
no MR asking anything of it. [MR32](#mr32-specialization-keeps-kinds-comparable), appended,
now asks; the probes are in the case study, so R2 has left the list — validated in both
directions: the same probes first exposed the quantity-level machinery R2's lattice still
lacked, and that machinery (`SpecializationLift`) has since landed and flipped the probe.

[PLAN.md](PLAN.md#what-this-benchmark-did-to-pkcs-own-requirements) stages a hypothetical
case study for each of the remaining four.
