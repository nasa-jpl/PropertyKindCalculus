/-
# Attempt 4 — PKC: a kind layer above the dimension layer

The fourth attempt keeps everything attempts 2 and 3 got right and adds the two axes they
were missing. It does **not** replace PhysLib's `Dimension`: `DimensionedKind` *carries* one,
and `DimensionedKind.toDimension` is the forgetful functor down to it. MR1, MR2 and MR3 are
therefore satisfied by delegation, exactly as attempt 2 satisfies them — that layer is right,
and nothing here second-guesses it.

What is added is two independent axes that a dimension, being a free commutative group, cannot
supply:

  * **the kind** (`KindOfProperty`, Dybkær §6.19) — which carries a *scale type* and an
    *examination principle*, so quantities sharing a dimension can still differ. This settles
    MR4 (frequency vs angular frequency), MR5 (interval vs ratio scale) and the kind half of
    MR8/MR9.
  * **the object** (`IndividualQuantity o k R`, and `DedicatedKind`'s
    `System — Component ; kind` triple) — so quantities of the same kind belonging to
    different individuals are distinguishable *without* being made unaddable. This settles
    MR6, MR7, MR9 and MR10.

The dilemma that defeated attempt 3 dissolves because kind and object are independent: two
masses share a *kind* (so `Extensive` licenses their sum) and differ in *object* (so they do
not substitute). One axis cannot do both; two can.

Scored against `README.md`:
- MR1 ✅
- MR2 ✅
- MR3 ✅
- MR4 ✅
- MR5 ✅
- MR6 ✅
- MR7 ✅
- MR8 ✅
- MR9 ✅
- MR10 ✅
- MR11 ⚠️
- MR12 ✅
- MR13 ✅
- MR14 ✅
- MR15 ✅
- MR16 ✅
- MR17 ✅
- MR18 ✅
- MR19 ✅
- MR32 ✅ (appended — ⚠️ at first scoring; the lift it exposed as owed has since landed)

**Where this attempt loses is MR11**, and the file says so in the same terms it uses for
everyone else. Written longhand, every multiplication carries a `ProductKind` witness and
every witness needs its result kind declared first, so the infix operators vanish from the
source and PKC is the *worst* of the four at authoring ergonomics. Two things soften that
without erasing it: the witness is exactly what `@[pkc_math]` deletes when rendering (Tier 4,
MR12), and `OperatorTable` moves the cost from the call site to a one-time per-model
registration — which is what turns MR11 from ❌ into ⚠️ rather than into ✅. A third move,
`kind_algebra` (minted from this very verdict), collapses the registration itself to one
declaration whose lines are the model's kind equations, so the residue sits at its floor:
what remains is the information, not its scaffolding. The verdict stays ⚠️ all the same, by
this file's own criterion — a per-model burden attempt 1 does not have, however small, is a
burden.

The file runs the requirements in order, tier by tier, so it can be read end to end as one
account of a single idea rather than as a row of a table.
-/
import PropertyKindCalculus.Dimension
import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part4
import PropertyKindCalculus.QuantityReal
import PropertyKindCalculus.Complex
import PropertyKindCalculus.FrameReal
import PropertyKindCalculus.SpecializationLift
import PropertyKindCalculus.KindAlgebra
import PropertyKindCalculus.DocGenMath
import Physlib.Units.WithDim.Basic

namespace PropertyKindCalculus.Examples.HarmonicOscillator.Attempt4

open PropertyKindCalculus Dimension

/-! ## The kinds

Each is a `DimensionedKind`: a `KindOfProperty` (identity, scale type, optionally an
examination principle) paired with the PhysLib `Dimension` of its quantities. The dimension
component is attempt 2's, unchanged. -/

/-- Angular frequency ω (rad/s), `T⁻¹`. ISO 80000-3 item 3-18 — the catalogue's own
entry. -/
def angularFrequency : DimensionedKind := Iso80000.Part3.angularFrequency

/-- Ordinary frequency f (Hz), `T⁻¹`. ISO 80000-3 item 3-17.1 — a *different item* of the
catalogue at the same dimension (cycles counted per unit time, not radians). -/
def frequency : DimensionedKind := Iso80000.Part3.frequency

/-- Mass, `M` — ISO 80000-4 item 4-1, the catalogue's own entry. -/
def mass : DimensionedKind := Iso80000.Part4.mass

/-- The **absolute energy of a Hamiltonian** — gauge-dependent, because the zero of the
potential is a free choice, so *interval* scale: differences are meaningful, ratios are not.
The same stance PKC takes for ISO 80000-5 Celsius temperature and IEC 80000-6 electric
potential. -/
def absoluteEnergy : DimensionedKind :=
  { kind := { id := "energy of a Hamiltonian", scale := .interval }, dim := Dim.energy }

/-- An **energy difference** — gauge-independent, hence *ratio* scale. Same dimension as
`absoluteEnergy`, different scale type: the distinction dimensional analysis cannot carry. -/
def energyDifference : DimensionedKind :=
  { kind := { id := "energy difference", scale := .ratio }, dim := Dim.energy }

/-- A dimensionless ratio of energy differences. -/
def energyRatio : DimensionedKind :=
  { kind := { id := "ratio of energy differences", scale := .ratio }, dim := 1 }

/-- Action, `M·L²·T⁻¹` — the kind of `ℏ`. ISO 80000-4 item 4-32, the catalogue's own
entry. -/
def action : DimensionedKind := Iso80000.Part4.action

/-- The characteristic length squared, `L²`. -/
def characteristicArea : DimensionedKind :=
  { kind := { id := "characteristic area", scale := .ratio }, dim := Dim.area }

/-- Spring constant, `M·T⁻²`. -/
def springConstant : DimensionedKind :=
  { kind := { id := "spring constant", scale := .ratio },
    dim := Dim.mass * Dim.time⁻¹ * Dim.time⁻¹ }

/-! ## MR1 ✅, MR2 ✅, MR3 ✅ — delegated to the dimension layer

PKC does not re-derive these. `DimensionedKind.toDimension` is a homomorphism into PhysLib's
group, so every dimensional fact attempt 2 proves is available verbatim, and the kind layer
sits above it. -/

/-! **MR1 holds.** `Quantity.add` is gated on the kind index, so a mass and a characteristic
area cannot be summed — and the gate is *finer* than attempt 2's, since two kinds at one
dimension are also kept apart (MR4 below). -/
#check_failure (fun (m : Quantity mass.kind ℝ) (a : Quantity characteristicArea.kind ℝ) =>
  Quantity.add (DifferenceKind.ofScale) m a)

/-- **MR2 holds (dimension).** `ℏ / (m · ω)` is an area — the identical computation attempt 2
performs, in the identical group. -/
theorem xiSq_dimension :
    action.toDimension / (mass.toDimension * angularFrequency.toDimension)
      = characteristicArea.toDimension := by decide

/-- **MR2 holds (kind).** And the *kind* is certified too, by a `QuotientKind` law that the
dimension layer alone cannot state: the characteristic area is the quotient kind of action by
`mass × angular frequency`. -/
theorem xiSq_kind_law :
    QuotientKind action.kind
      { id := "mass × angular frequency", scale := .ratio } characteristicArea.kind :=
  QuotientKind.ofRatio _ _ _

/-- **MR3 holds.** The unit-scale factor is a function of the dimension, and `toDimension` is
multiplicative, so a kind's scale factor is determined by the kinds it is built from — the
covariance of attempt 2, lifted through the functor. -/
theorem dimScale_of_kind_product (u₁ u₂ : LTMCTUnitChoices) (a b : DimensionedKind) :
    u₁.dimScale u₂ ((a.times b).toDimension)
      = u₁.dimScale u₂ a.toDimension * u₁.dimScale u₂ b.toDimension := by
  rw [DimensionedKind.toDimension_times]; exact map_mul _ _ _

/-! ## MR4 ✅ — the rad/s trap, closed

Frequency and angular frequency share a dimension and are *not* the same kind: the
standard itself lists them as two items (3-17.1 and 3-18), and the two kinds here are
those two catalogue entries' own projections — the individuation is the standard's, not
a label chosen for convenience. So the collapse attempt 2 proved by `rfl` is exactly
what fails to happen here. -/

/-- The dimension layer still cannot tell them apart — PKC does not pretend otherwise. -/
theorem freq_same_dimension : frequency.toDimension = angularFrequency.toDimension := rfl

/-- **MR4 holds.** But they are distinct *kinds*. -/
theorem freq_ne_angFreq : frequency.kind ≠ angularFrequency.kind := by decide

/-- **MR4 holds** — and distinct for a *reason*: the two kinds are the catalogue's own
entries for two separately listed items, so the distinction is the standard's rather
than a hand-chosen identity string. -/
theorem freq_individuated_by_catalogue :
    Iso80000.Part3.frequencyCK.item ≠ Iso80000.Part3.angularFrequencyCK.item
      ∧ Iso80000.Part3.frequencyCK.qk = frequency
      ∧ Iso80000.Part3.angularFrequencyCK.qk = angularFrequency :=
  ⟨by decide, rfl, rfl⟩

/-! **MR4 holds, at the type level.** A frequency in hertz is not accepted where an angular
frequency is required. This is attempt 2's silent `2π` bug, rejected at elaboration. -/
#check_failure (fun (ν : Quantity frequency.kind ℝ) => (ν : Quantity angularFrequency.kind ℝ))

/-- **MR4, the capstone.** Two kinds, one dimension — the harmonic oscillator's instance of
`Dimension.dim_not_injective`, and the reason a dimension-only layer cannot carry this. -/
theorem mr4_capstone :
    frequency.kind ≠ angularFrequency.kind
      ∧ frequency.toDimension = angularFrequency.toDimension :=
  ⟨freq_ne_angFreq, rfl⟩

/-! ## MR5 ✅ — scale type gates the operators

The absolute energy of a Hamiltonian is interval-scale, so `−` is licensed and `÷` is not.
`ProductKind`/`QuotientKind` carry the ratio-scale precondition (Dybkær §13.3.5), and
`DifferenceKind` carries the interval one, so the gate is in the witness the operation
demands. -/

/-- Subtraction *is* licensed on absolute energies: interval scale allows differences. -/
theorem energy_difference_licensed : DifferenceKind absoluteEnergy.kind :=
  DifferenceKind.ofScale

/-! **MR5 holds.** Division is *not* licensed: `QuotientKind.ofRatio` cannot be built at
interval scale, so the gauge-dependent ratio `E₁ / E₀` has no witness and cannot be formed.
Attempt 2 accepted it without comment. -/
#check_failure (QuotientKind.ofRatio absoluteEnergy.kind absoluteEnergy.kind energyRatio.kind)

/-- The gate is not a blanket refusal: the *meaningful* operation — a ratio of energy
*differences*, which is gauge-independent and ratio-scale — is licensed. -/
theorem energy_difference_ratio_licensed :
    QuotientKind energyDifference.kind energyDifference.kind energyRatio.kind :=
  QuotientKind.ofRatio _ _ _

/-- **MR5, the capstone.** One dimension, two scale types, opposite operator availability. -/
theorem mr5_capstone :
    absoluteEnergy.toDimension = energyDifference.toDimension
      ∧ ¬ absoluteEnergy.kind.IsRational
      ∧ energyDifference.kind.IsRational := by
  refine ⟨rfl, ?_, rfl⟩
  simp [KindOfProperty.IsRational, absoluteEnergy]

/-! ## The two oscillators, as systems and components

Dybkær Ch. 3: a *system* is a demarcated arrangement of elements. The pair is a system; each
oscillator is a system; each degree of freedom of an oscillator is a system. `DedicatedKind`
(Ch. 20) then binds a kind to a system *and* a pertinent component, in the IUPAC/IFCC
`System — Component ; kind` syntax. -/

/-- Oscillator A, as a system. -/
def oscA : System := { id := "oscillator A" }
/-- Oscillator B, as a system. -/
def oscB : System := { id := "oscillator B" }
/-- The coupled pair, as a system — the whole that A and B are parts of. -/
def pair : System := { id := "coupled pair A–B" }

/-! ## MR7 ✅ — object identity

`IndividualQuantity o k R` carries the object in the *type*, and `add`/`mul`/`div` are gated
on a shared `o`. The mixed Hamiltonian is a type error. -/

/-- A's mass, `3`. -/
noncomputable def mA : IndividualQuantity oscA mass.kind ℝ := ⟨3⟩
/-- B's mass, `5`. -/
noncomputable def mB : IndividualQuantity oscB mass.kind ℝ := ⟨5⟩
/-- A's angular frequency, `2`. -/
noncomputable def ωA : IndividualQuantity oscA angularFrequency.kind ℝ := ⟨2⟩
/-- B's angular frequency, `4`. -/
noncomputable def ωB : IndividualQuantity oscB angularFrequency.kind ℝ := ⟨4⟩

/-- The product law licensing `m × ω` (the two factors of a Hamiltonian coefficient). -/
theorem massTimesAngFreq :
    ProductKind mass.kind angularFrequency.kind
      { id := "mass × angular frequency", scale := .ratio } :=
  ProductKind.ofRatio _ _ _

/-- Within one oscillator the product is fine. -/
noncomputable def coeffA :
    IndividualQuantity oscA { id := "mass × angular frequency", scale := .ratio } ℝ :=
  IndividualQuantity.mul massTimesAngFreq mA ωA

/-! **MR7 holds.** A's mass with B's angular frequency: rejected. Attempt 2 accepted this;
attempt 3 also rejected it, but at the cost of MR8 below — here nothing is paid. -/
#check_failure (IndividualQuantity.mul massTimesAngFreq mA ωB)

/-! The rejection pinned, so that *why* the coefficient is ill-typed cannot drift. Both
factors are at the kinds the product law demands — `mass.kind` and `angularFrequency.kind`,
both `LTMCTDimensionBase`-dimensioned, both over `ℝ`. The mismatch is in the object index
alone: `oscB` where `oscA` was required. Dimensional analysis has no field in which to
record this difference, so no dimensional discipline can raise this error. -/
/--
error: Application type mismatch: The argument
  ωB
has type
  IndividualQuantity oscB (angularFrequency.kind LTMCTDimensionBase) ℝ
but is expected to have type
  IndividualQuantity oscA (angularFrequency.kind LTMCTDimensionBase) ℝ
in the application
  IndividualQuantity.mul massTimesAngFreq mA ωB
---
info: IndividualQuantity.mul massTimesAngFreq mA
  sorry : IndividualQuantity oscA { id := "mass × angular frequency", scale := ScaleType.ratio } ℝ
-/
#guard_msgs in
#check (IndividualQuantity.mul massTimesAngFreq mA ωB)

/-! **MR7 holds.** B's mass cannot stand in for A's. -/
#check_failure (mB : IndividualQuantity oscA mass.kind ℝ)

/-! The gate is on *provenance*, not on the number. B's angular frequency may still enter a
coefficient of A — but only by an explicit re-attribution that names both systems and
survives in the source. -/

/-- B's angular frequency, re-attributed to A: the driving frequency that A is subjected to.
Writing this is the act the type system requires; it cannot happen by omission. -/
noncomputable def ωBDrivingA : IndividualQuantity oscA angularFrequency.kind ℝ :=
  ⟨ωB.magnitude⟩

/-- With the re-attribution written down, the coefficient is well-typed again. -/
noncomputable def coeffADriven :
    IndividualQuantity oscA { id := "mass × angular frequency", scale := .ratio } ℝ :=
  IndividualQuantity.mul massTimesAngFreq mA ωBDrivingA

/-- **MR7, the point.** `3 × 4 = 12` is exactly the arithmetic the unchecked version would
have performed. PKC does not forbid the number; it forbids arriving at it silently. -/
theorem coeffADriven_magnitude : coeffADriven.magnitude = 12 := by
  norm_num [coeffADriven, IndividualQuantity.mul, ωBDrivingA, ωB, mA]

/-! ## MR10 ✅ — provenance survives a function boundary

The object and the kind are both type indices, so a helper's signature pins both. Attempt 1
lost everything here; attempt 2 kept the dimension; attempt 4 keeps the object too. -/

/-- The zero-point energy of a *named* oscillator, as a helper. -/
noncomputable def zeroPointEnergy (o : System)
    (_m : IndividualQuantity o mass.kind ℝ)
    (ω : IndividualQuantity o angularFrequency.kind ℝ) :
    IndividualQuantity o absoluteEnergy.kind ℝ :=
  ⟨ω.magnitude / 2⟩

/-- The intended call. -/
noncomputable example : IndividualQuantity oscA absoluteEnergy.kind ℝ :=
  zeroPointEnergy oscA mA ωA

/-! **MR10 holds.** The cross-object call is rejected *inside the helper's signature*, not by
a convention at the call site. -/
#check_failure (zeroPointEnergy oscA mA ωB)

/-! **MR10 holds.** And the swapped-argument call, which attempt 1 accepted. -/
#check_failure (zeroPointEnergy oscA ωA mA)

/-! ## MR6 ✅ — degrees of freedom

A degree of freedom is itself a demarcated system, so the same machinery applies one level
down: `ω 0` and `ω 1` of an anisotropic oscillator belong to different systems and are
therefore not interchangeable — while isotropy remains, correctly, a statement that two
*magnitudes* agree. -/

/-- The x degree of freedom of an anisotropic oscillator. -/
def dofX : System := { id := "oscillator C — x axis" }
/-- The y degree of freedom of the same oscillator. -/
def dofY : System := { id := "oscillator C — y axis" }

/-- The x-axis angular frequency, `2`. -/
noncomputable def ωX : IndividualQuantity dofX angularFrequency.kind ℝ := ⟨2⟩
/-- The y-axis angular frequency, `7`. -/
noncomputable def ωY : IndividualQuantity dofY angularFrequency.kind ℝ := ⟨7⟩

/-! **MR6 holds.** The two degrees of freedom do not substitute for one another — attempt 2's
`Fin d` index could not prevent this. -/
#check_failure (ωY : IndividualQuantity dofX angularFrequency.kind ℝ)

/-- **MR6 holds.** And isotropy stays what PhysLib's `IsIsotropic` makes it — a claim about
magnitudes, provable or refutable, never a type-level identification of the two degrees of
freedom. Here it is refuted, because `2 ≠ 7`. -/
theorem not_isotropic : ωX.magnitude ≠ ωY.magnitude := by
  norm_num [ωX, ωY]

/-- The point MR6 is really testing: even a *degenerate* oscillator, whose two frequencies
have equal magnitude, keeps two distinct degrees of freedom. Accidental degeneracy is a fact
about numbers; it is not an identification of axes. -/
noncomputable example (a : IndividualQuantity dofX angularFrequency.kind ℝ)
    (b : IndividualQuantity dofY angularFrequency.kind ℝ) (_h : a.magnitude = b.magnitude) :
    Prop := a.magnitude = b.magnitude

/-! ## MR8 ✅ — licensed aggregation, both directions

This is the requirement no single-axis scheme can satisfy. Mass and angular frequency have
the *same* status at every layer attempts 1–3 offer — same shape of expression, same
dimension arithmetic, same types — and differ in exactly one respect: mass is **extensive**
over the decomposition of the pair and angular frequency is not.

`Extensive k m` (Dybkær §13.5) is that property, quantified over the mereology, and it is
what licenses the sum. -/

/-- The pair, decomposed into its two oscillators. -/
def pairDecomposition : Decomposition System := .union (.atom oscA) (.atom oscB)

/-- The mass numeral of any sub-system: `3` for A, `5` for B, and the *sum* over a union. -/
def massNumeral : Decomposition System → Int
  | .atom s => if s = oscA then 3 else if s = oscB then 5 else 0
  | .union a b => massNumeral a + massNumeral b

/-- Mass, measured over the decomposition. -/
def massMeasurement : Measurement System :=
  fun d => { kind := mass.kind, numeral := massNumeral d, reference := "kg" }

/-- **MR8 holds (the accepting half).** Mass is extensive: the whole's mass is the sum of the
parts'. This is the *licence*, and it is a proof obligation discharged once per kind. -/
theorem mass_extensive : Extensive mass.kind massMeasurement where
  ofKind := fun _ => rfl
  additive := fun _ _ => rfl

/-- The licence cashed out: the pair's total mass is `3 + 5 = 8`. -/
theorem total_mass : (massMeasurement pairDecomposition).numeral = 8 := by
  decide

/-- And the aggregation law holds to arbitrary depth, by `extensive_additive` — not for this
decomposition only. -/
theorem total_mass_is_leafSum :
    (massMeasurement pairDecomposition).numeral = leafSum massMeasurement pairDecomposition :=
  extensive_additive mass_extensive pairDecomposition

/-- The angular-frequency numeral: `2` for A, `4` for B — and `5` for the pair, which is the
upper normal mode `ω₊`, not `2 + 4`. -/
def angFreqNumeral : Decomposition System → Int
  | .atom s => if s = oscA then 2 else if s = oscB then 4 else 0
  | .union _ _ => 5

/-- Angular frequency, measured over the same decomposition. -/
def angFreqMeasurement : Measurement System :=
  fun d => { kind := angularFrequency.kind, numeral := angFreqNumeral d,
             reference := "rad/s" }

/-- **MR8 holds (the rejecting half).** Angular frequency is **not** extensive: the pair's
`ω₊ = 5` is not `2 + 4`. So there is no licence, and the sum attempts 1 and 2 both formed
without complaint is unavailable. -/
theorem angFreq_not_extensive : ¬ Extensive angularFrequency.kind angFreqMeasurement :=
  fun h => absurd (h.additive (.atom oscA) (.atom oscB)) (by decide)

/-- **MR8, the capstone — and the whole benchmark in one statement.** Two kinds at the same
layer, with the same dimensional behaviour and the same syntax. One aggregates over the
pair's decomposition; the other does not. Attempt 1 and attempt 2 accept both sums; attempt 3
rejects both; only a kind layer *distinguishes* them, because extensivity is a property of
the kind and of nothing below it. -/
theorem mr8_capstone :
    Extensive mass.kind massMeasurement
      ∧ ¬ Extensive angularFrequency.kind angFreqMeasurement
      ∧ (massMeasurement pairDecomposition).numeral = 8 :=
  ⟨mass_extensive, angFreq_not_extensive, total_mass⟩

/-! ## MR9 ✅ — whole-system quantities

`DedicatedKind` is the `System — Component ; kind` triple. The pair's normal modes and its
coupling are dedicated kinds *of the pair*, distinguished by their **component** — which is
exactly the datum neither a dimension nor an object index alone supplies. -/

/-- *"coupled pair A–B — oscillator A ; angular frequency"* — A's bare frequency, read as a
property of the pair. -/
def dkOmegaA : DedicatedKind :=
  angularFrequency.kind.dedicatedTo pair { id := "oscillator A" }

/-- *"… — oscillator B ; angular frequency"*. -/
def dkOmegaB : DedicatedKind :=
  angularFrequency.kind.dedicatedTo pair { id := "oscillator B" }

/-- *"… — normal mode + ; angular frequency"* — the upper normal mode. Same kind, same
dimension, same unit, different component. -/
def dkOmegaPlus : DedicatedKind :=
  angularFrequency.kind.dedicatedTo pair { id := "normal mode +" }

/-- *"… — coupling A↔B ; spring constant"* — the coupling constant. A property of the pair
through a component that is **neither** oscillator, so it has no home in a per-object scheme
at all. -/
def dkCoupling : DedicatedKind :=
  springConstant.kind.dedicatedTo pair { id := "coupling A↔B" }

/-- **MR9 holds.** The normal-mode frequency is a different dedicated kind from either bare
frequency — distinct **because the components differ**, not by a hand-chosen label. -/
theorem omegaPlus_ne_omegaA : dkOmegaPlus ≠ dkOmegaA :=
  DedicatedKind.distinct_of_component (by decide)

/-- Likewise for B. -/
theorem omegaPlus_ne_omegaB : dkOmegaPlus ≠ dkOmegaB :=
  DedicatedKind.distinct_of_component (by decide)

/-- And the two bare frequencies from each other. -/
theorem omegaA_ne_omegaB : dkOmegaA ≠ dkOmegaB :=
  DedicatedKind.distinct_of_component (by decide)

/-- The coupling is distinguished by its *kind*, not only its component — it is a spring
constant, not a frequency. -/
theorem coupling_ne_omegaA : dkCoupling ≠ dkOmegaA :=
  DedicatedKind.distinct_of_kind (by decide)

/-- The systematic terms, rendered in the IUPAC/IFCC syntax the construct comes from. -/
example : dkOmegaPlus.systematicTerm =
    "coupled pair A–B — normal mode + ; angular frequency" := rfl

example : dkCoupling.systematicTerm =
    "coupled pair A–B — coupling A↔B ; spring constant" := rfl

/-- **MR9, the capstone — the object-level `dim_not_injective`.** Three pairwise-distinct
dedicated kinds sharing one underlying kind, hence one dimension and one unit (rad/s). Every
layer below the kind layer identifies all three; substituting `ω_A` for `ω₊` is the bug MR9
names, and in the symmetric case it even returns the right number. -/
theorem mr9_capstone :
    dkOmegaA ≠ dkOmegaB ∧ dkOmegaPlus ≠ dkOmegaA ∧ dkOmegaPlus ≠ dkOmegaB
      ∧ dkOmegaA.kind = dkOmegaB.kind ∧ dkOmegaPlus.kind = dkOmegaA.kind :=
  ⟨omegaA_ne_omegaB, omegaPlus_ne_omegaA, omegaPlus_ne_omegaB, rfl, rfl⟩

/-! ## Why the tagging dilemma does not arise

Attempt 3's `tagging_dilemma` showed that within `WithDim`, "addable" and "distinguishable"
are each other's negation, because both reduce to a comparison of one datum — the dimension.
Here they reduce to comparisons of *two independent* data:

  * **addable** is a question about the **kind** — settled by `Extensive`, a quantified law
    over the mereology (`mass_extensive`);
  * **distinguishable** is a question about the **object** — settled by the type index
    (`#check_failure (mB : IndividualQuantity oscA mass.kind ℝ)`).

A and B's masses are the *same kind* and *different objects*, so both hold at once. There is
no dilemma because there is no longer one axis being asked to answer two questions. -/

/-- **The resolution.** A's and B's masses share a kind — which is what licenses their sum via
`mass_extensive` — while belonging to different objects, which is what makes them
non-substitutable. Attempt 3 could not write this conjunction down; the two conjuncts were
contradictory there. -/
theorem no_dilemma :
    (mA.toIndividualProperty.kind = mB.toIndividualProperty.kind)
      ∧ (mA.toIndividualProperty.carrier ≠ mB.toIndividualProperty.carrier) := by
  refine ⟨rfl, ?_⟩
  decide

/-! # Tier 4 — ergonomics (MR11 ⚠️, MR12 ✅)

The axis on which this attempt is worst, followed by the axis on which it is best, and the
finding is that the two are the *same object seen twice*: the `ProductKind` witness that makes
MR11 painful is exactly what the rendering pipeline deletes.

The formula throughout is the potential energy of a harmonic oscillator at displacement `x`:

$$ V = m \cdot \omega^2 \cdot x^2 $$

Five factors, four multiplications. The `½` is dropped, because attempts 2 and 3 cannot write
a bare numeric coefficient without a further cast and the comparison should not turn on that. -/

namespace Tier4

open PropertyKindCalculus.DocGenMath

/-! ## MR11, longhand — the worst case, stated as such

Every multiplication demands a witness naming the full kind equation, and each witness needs
its result kind declared first. Four multiplications therefore cost three intermediate kind
declarations and four witnesses before a line of physics is written, and the expression itself
becomes a right-nested tower of `IndividualQuantity.mul` applications in which the operator
symbols have disappeared.

This is the real ergonomic complaint about PKC and it should be stated without softening: the
formula below is unreadable as physics. -/

/-- Displacement — the catalogue's own 3-1.11. -/
def lengthK : KindOfProperty := (Iso80000.Part3.displacement).kind
/-- Intermediate: angular frequency squared. -/
def kω2 : KindOfProperty := { id := "angular frequency squared", scale := .ratio }
/-- Intermediate: displacement squared. -/
def kx2 : KindOfProperty := { id := "displacement squared", scale := .ratio }
/-- Intermediate: `mass × angular frequency²` (a spring constant). -/
def kmω2 : KindOfProperty := { id := "mass × angular frequency²", scale := .ratio }
/-- The result: potential energy — the catalogue's own 4-28.1. -/
def energyK : KindOfProperty := (Iso80000.Part4.potentialEnergy).kind

theorem pω2 : ProductKind angularFrequency.kind angularFrequency.kind kω2 :=
  ProductKind.ofRatio _ _ _
theorem px2 : ProductKind lengthK lengthK kx2 := ProductKind.ofRatio _ _ _
theorem pmω2 : ProductKind mass.kind kω2 kmω2 := ProductKind.ofRatio _ _ _
theorem pe : ProductKind kmω2 kx2 energyK := ProductKind.ofRatio _ _ _

/-- **MR11, longhand.** 7 declarations of scaffolding (4 witnesses + 3 intermediate kinds)
before the formula, and the formula itself has no visible operators. This is the worst cell in
the benchmark, and it is PKC's. -/
noncomputable def energyPkc (o : System)
    (m : IndividualQuantity o mass.kind ℝ)
    (ω : IndividualQuantity o angularFrequency.kind ℝ)
    (x : IndividualQuantity o lengthK ℝ) : IndividualQuantity o energyK ℝ :=
  IndividualQuantity.mul pe
    (IndividualQuantity.mul pmω2 m (IndividualQuantity.mul pω2 ω ω))
    (IndividualQuantity.mul px2 x x)

/-! ## MR11 with the operator table — the same formula, the same guarantees

`PropertyKindCalculus.OperatorTable` is the curated operator layer over the same kind-laws:

  * **`KindMul k₁ k₂ k` — a curated instance table**, registered once per application next to
    its kind declarations, at most one entry per operand pair. The result kind is an
    `outParam`, so instance search *computes* the interior kinds of a chained product.
  * **Scoped `HMul` / `HDiv`**, on `Quantity` and `IndividualQuantity` alike, so `x * y`
    elaborates through the table and an unregistered pair **fails to elaborate**.

The discipline is not weakened: there is deliberately no `Mul` instance on `Quantity` itself,
the instances are opt-in per file, and each entry is an authored declaration `grep` finds.

**And the witness is still in the term.** `hmul_eq_mul_individual` proves
`x * y = IndividualQuantity.mul KindMul.law x y` by `rfl`, so the operator form and the witness
form are the *same* elaborated expression, `Lift` still sees the witness, and MR12 below is
untouched. The ceremony moves from the call site to a registration. -/

open scoped PropertyKindCalculus.OperatorTable

instance : KindMul angularFrequency.kind angularFrequency.kind kω2 := ⟨pω2⟩
instance : KindMul lengthK lengthK kx2 := ⟨px2⟩
instance : KindMul mass.kind kω2 kmω2 := ⟨pmω2⟩
instance : KindMul kmω2 kx2 energyK := ⟨pe⟩

/-- **MR11, with the table.** Character for character the formula a physicist writes over bare
reals — and every Tier-2 and Tier-3 guarantee is still enforced. -/
@[pkc_math_symbol "V"]
noncomputable def energyPkcOperators (o : System)
    (m : IndividualQuantity o mass.kind ℝ)
    (ω : IndividualQuantity o angularFrequency.kind ℝ)
    (x : IndividualQuantity o lengthK ℝ) : IndividualQuantity o energyK ℝ :=
  m * (ω * ω) * (x * x)

/-- **Nothing was weakened.** The operator version is the *same term* as the longhand one, so
every certificate proved of either holds of both. -/
theorem energyPkcOperators_eq (o : System)
    (m : IndividualQuantity o mass.kind ℝ)
    (ω : IndividualQuantity o angularFrequency.kind ℝ)
    (x : IndividualQuantity o lengthK ℝ) :
    energyPkcOperators o m ω x = energyPkc o m ω x := rfl

/-! **The object gate survives the notation.** A cross-object product does not elaborate —
MR7, unchanged, now enforced by instance resolution failing to unify `oscA` with `oscB`. -/
#check_failure (fun (m : IndividualQuantity oscA mass.kind ℝ)
    (ω : IndividualQuantity oscB angularFrequency.kind ℝ) => m * ω)

/-! **And so does the curation.** `mass × mass` is not a registered edge, so it does not
elaborate: the compile error a naked magnitude cannot give. Infix notation did not open the
gate — it made the gate silent until it is violated, which is what one wants from a gate. -/
#check_failure (fun (o : System) (m₁ m₂ : IndividualQuantity o mass.kind ℝ) => m₁ * m₂)

/-! ## MR11 with `kind_algebra` — the registration, generated

`PropertyKindCalculus.KindAlgebra` (minted from this verdict) collapses what remains — the
derived-kind declarations and their table entries — to the kind equations themselves, one
line each. The block below stands up the *kinetic* side of the oscillator's energy
(`T = m·v²`, again without the `½`): one base kind by hand — base kinds carry the
semantics, the examination principle, and stay hand-written — then both derived kinds and
both table entries in one declaration. The expansion is exactly the hand-written spelling
above, so nothing is weakened, and the block is the authored declaration `grep` finds. -/

/-- Velocity — a base kind, and a catalogue lookup (3-10.1) as base kinds should be. -/
def velocityK : KindOfProperty := (Iso80000.Part3.velocity).kind

kind_algebra
  kv2      : "velocity squared"  := velocityK * velocityK
  kineticK : "mass × velocity²"  := mass.kind * kv2

/-- **MR11, with the algebra generated.** The formula is attempt 1's, and the whole
stand-up cost for it was one base-kind declaration and one two-line `kind_algebra`
block. -/
noncomputable def kineticPkc (o : System)
    (m : IndividualQuantity o mass.kind ℝ)
    (v : IndividualQuantity o velocityK ℝ) : IndividualQuantity o kineticK ℝ :=
  m * (v * v)

/-! ## The MR11 verdict

| | per-formula cost | per-model cost | operators visible |
|---|---|---|---|
| longhand | 4 witnesses | 3 kind declarations | **no** |
| with the table | **none** | 3 kind declarations + 4 table entries | **yes** |
| with `kind_algebra` | **none** | 1 base kind + 1 block, one line per kind equation | **yes** |

So MR11 is ⚠️ rather than ❌ or ✅, and the honest statement is narrower than "PKC is
unergonomic": *writing formulas* costs nothing once the table is registered, and what remains
is a one-time declaration burden attempt 1 does not have. It is still a real cost. It is paid
where a model's algebra is declared, and it does not grow with the size of the formulas —
which is the opposite of attempt 2, whose cast is paid at every named result. And
`kind_algebra` collapses even that to the kind equations themselves, so the burden sits at
its information floor: what remains to write is the model's algebra, which is precisely
what the guarantees are about. The verdict stays ⚠️ by this file's own criterion — a
per-model cost attempt 1 does not pay, however small, is a cost. -/

/-! ## MR12 ✅ — rendering ergonomics

`@[pkc_math]` lifts the authored surface to a `MathTerm`, drops the witnesses and instance
arguments, normalizes (`x·x → x²`), and writes `$$…$$` LaTeX into the declaration's own
docstring, so doc-gen4 and the InfoView typeset it with no special support.

Below: the equation, then the *derivation* the PR thread's ergonomics concern is really about
— substituting `ω² = k/m` to reach the spring-constant form. The demo uses one dimensionless
ratio kind so the witness is a single `pk` and the focus stays on rendering; the kind-tracked
version is `energyPkc` above. -/

/-- One dimensionless ratio kind for the rendering demo. -/
def dl : KindOfProperty := { id := "1", scale := .ratio }

/-- The product law `dl = dl × dl`. -/
theorem pk : ProductKind dl dl dl := ⟨rfl, rfl, rfl⟩
/-- The quotient law `dl = dl / dl`. -/
theorem qk : QuotientKind dl dl dl := ⟨rfl, rfl, rfl⟩

/-- The squared natural frequency of an oscillator, `ω² = k/m`. -/
@[pkc_math_symbol "\\omega^2"]
def omegaSq (k m : Quantity dl Float) : Quantity dl Float := Quantity.div qk k m

/-- The potential energy `V = m·ω²·x²`, with `ω²` left as a named helper so the derivation
below has something to substitute. -/
@[pkc_math_symbol "V", pkc_math substituting omegaSq]
def potentialV (k m x : Quantity dl Float) : Quantity dl Float :=
  Quantity.mul pk (Quantity.mul pk m (omegaSq k m)) (Quantity.mul pk x x)

/-! `#guard_msgs` makes the rendering a build artifact: a regression in any stage of the
pipeline is a compile error, not a visual change someone might not notice. -/

/-- info: V = m\,\omega^2\left(k, m\right)\,x^{2} -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``potentialV)
  Lean.logInfo s

/-! **The derivation step.** The same equation with `omegaSq` inlined — this is
`delta`-substitution, hence meaning-preserving: every equation in the chain denotes the same
quantity. -/

/-- info: V = m\,\frac{k}{m}\,x^{2} -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatexSubst ``potentialV #[``omegaSq])
  Lean.logInfo s

/-! ## MR12 — rendering the object-indexed layer

The named combinators `IndividualQuantity.mul` / `div` / `add` are in `Lift`'s operator table
beside their `Quantity` twins, and a model written through `OperatorTable` arrives as
`HMul.hMul`, which the binary branch already matched. So the longhand and the operator
spellings render **identically** — the rendering-side statement of `energyPkcOperators_eq`. -/

attribute [pkc_math_symbol "V"] energyPkc

/-- info: V = m\,\omega^{2}\,x^{2} -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``energyPkc)
  Lean.logInfo s

/-- info: V = m\,\omega^{2}\,x^{2} -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``energyPkcOperators)
  Lean.logInfo s

/-! ### The object index is the notation

A definition generic in its object renders unsubscripted, as above. When the object is
*concrete*, the leaf carries it as a **subscript**, so the two oscillators' energies — types
that Tier 3 keeps rigorously apart — are also kept apart on the page:

$$ V_A = m_A\,\omega_A^2\,x_A^2 \qquad V_B = m_B\,\omega_B^2\,x_B^2 $$

which is how a physicist writes a coupled system. Without it the object index would be
invisible in the output and the two equations would reach the reader as the same string —
MR9's confusion surviving into the presentation layer. -/

/-- Oscillator A, with the short label its descriptive `id` does not supply. -/
@[pkc_math_symbol "A"]
def sysA : System := { id := "oscillator A" }

/-- Oscillator B. -/
@[pkc_math_symbol "B"]
def sysB : System := { id := "oscillator B" }

/-- A's potential energy. -/
@[pkc_math_symbol "V"]
noncomputable def energyOscA
    (m : IndividualQuantity sysA mass.kind ℝ)
    (ω : IndividualQuantity sysA angularFrequency.kind ℝ)
    (x : IndividualQuantity sysA lengthK ℝ) : IndividualQuantity sysA energyK ℝ :=
  m * (ω * ω) * (x * x)

/-- B's potential energy — a different object, hence a different type. -/
@[pkc_math_symbol "V"]
noncomputable def energyOscB
    (m : IndividualQuantity sysB mass.kind ℝ)
    (ω : IndividualQuantity sysB angularFrequency.kind ℝ)
    (x : IndividualQuantity sysB lengthK ℝ) : IndividualQuantity sysB energyK ℝ :=
  m * (ω * ω) * (x * x)

/-- info: V = m_{A}\,\omega_{A}^{2}\,x_{A}^{2} -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``energyOscA)
  Lean.logInfo s

/-- info: V = m_{B}\,\omega_{B}^{2}\,x_{B}^{2} -/
#guard_msgs in
run_cmd do
  let s ← Lean.Elab.Command.liftTermElabM (quantityToLatex ``energyOscB)
  Lean.logInfo s

/-! Two definitions with the same body, kept apart on the page because they are kept apart in
the types. The subscript is not decoration: it is the object index, which is what MR7, MR9 and
MR10 are about, made visible where the reader is.

**The MR12 verdict.** The witnesses are in the source and absent from every rendered line
above — `Lift` drops exactly the arguments MR11 charges for, so the bookkeeping the author
writes is bookkeeping the reader never sees. MR12 is ✅ on three counts, each pinned rather
than asserted: the equation renders; a derivation renders; and the object index reaches the
page as a subscript. -/

end Tier4

/-! # Tier 5 — computation (MR13 ✅, MR14 ✅, MR15 ✅)

In what numbers is the quantity carried, and can the same model be carried in more than one?
Not a software-engineering aside: Dybkær §13.3.3 has a quantity value as a *number and a
reference*, and "which numbers" is a free axis. A model written for the proof carrier `ℝ` and
one written for the executable carrier `Float` are the same physics, and must not be two
source files — or the thing that runs is not the thing that was verified. -/

namespace Tier5

/-! ## MR13 ✅ — one model, two carriers

`Quantity k R` is parametric in `R` over the `Carrier` class, and the *same* definition is
instantiated at the proof carrier and the executable one. The kind gating is unchanged in
both: `R` is orthogonal to `k`. -/

/-- The oscillator's stiffness relation `k = m · ω²`, written **once**, over any scalar carrier
with multiplication. This is the definition both instantiations below use. -/
def stiffness {R : Type} [Mul R] [ScalarCarrier R] {km kω kk : KindOfProperty}
    (p₁ : ProductKind km kω kω) (p₂ : ProductKind kω kω kk)
    (_p : ProductKind km kk kk)
    (m : Quantity km R) (ω : Quantity kω R) : Quantity kk R :=
  Quantity.mul p₂ (Quantity.mul p₁ m ω) ω

/-- A single ratio kind, enough to exercise the carrier axis. -/
def dl : KindOfProperty := { id := "1", scale := .ratio }
theorem pk : ProductKind dl dl dl := ⟨rfl, rfl, rfl⟩

/-- **MR13 holds (proof carrier).** The model at `ℝ`, where the laws live. -/
noncomputable def stiffnessReal (m ω : Quantity dl ℝ) : Quantity dl ℝ :=
  stiffness pk pk pk m ω

/-- **MR13 holds (executable carrier).** The *same* definition at `Float` — and it runs. -/
def stiffnessFloat (m ω : Quantity dl Float) : Quantity dl Float :=
  stiffness pk pk pk m ω

/-! `m = 5`, `ω = 2` gives `k = 20`, computed rather than asserted. `#guard` is the evidence
form for an executable fact: it *runs* the definition at elaboration time and fails the build
on mismatch, without adding a compiler-trust axiom the way `native_decide` would. -/
#guard (stiffnessFloat ⟨5⟩ ⟨2⟩).magnitude == 20.0

/-- **MR13's real content.** The additivity law is proved **once**, over an arbitrary
`LawfulCarrier`, and therefore holds at `ℝ`, at `Int`, and at every other lawful carrier
without a second proof. This is what "one model, many carriers" has to mean to be worth
anything. -/
theorem add_comm_any_lawful_carrier {R : Type} [LawfulCarrier R] (h : DifferenceKind dl)
    (x y : Quantity dl R) : Quantity.add h x y = Quantity.add h y x :=
  Quantity.add_comm h x y

/-- Instantiated at the proof carrier, with no `ℝ`-specific proof. -/
theorem add_comm_real (h : DifferenceKind dl) (x y : Quantity dl ℝ) :
    Quantity.add h x y = Quantity.add h y x :=
  add_comm_any_lawful_carrier h x y

/-! ## MR14 ✅ — complex-valued quantities

The harmonic oscillator has several quantities whose value is *fundamentally* complex, and
none of them is exotic:

  * **The driven oscillator's mechanical impedance** `Z(ω) = c + i(mω − k/ω)` — one kind, one
    dimension `M·T⁻¹`, real part the mechanical resistance and imaginary part the reactance.
    The mechanical twin of IEC 80000-6's complex electrical impedance, and the worked case
    below.
  * **The complex amplitude (phasor)** `A = |A|e^{iφ}` of the steady-state response — amplitude
    and phase as one quantity, which is the whole reason the phasor is used.
  * **The complex eigenfrequency of a damped oscillator**, `ω_d + iγ`: real part an angular
    frequency, imaginary part a decay rate — *the same dimension* `T⁻¹` in the two components,
    which is MR4's collision reappearing inside a single value.
  * **The coherent-state parameter** `α`, defined by `a|α⟩ = α|α⟩`. The ladder operator is not
    self-adjoint, so `α ∈ ℂ` irreducibly.

And it is not only *this* file's physics that needs them. PhysLib's own
`QuantumMechanics.HarmonicOscillator d` carries real parameters (`m : ℝ`, `ω : Fin d → ℝ`) over
a **complex** state space — `HS := SpaceDHilbertSpace d`, with
`hamiltonian : Q.HS →ₗ.[ℂ] Q.HS` — so the question is settled upstream, not raised here.

The stance PKC takes (`PropertyKindCalculus.Complex`) is what this requirement tests:
*complex-ness is a property of the carrier, not of the kind*. An impedance is **one** kind,
dimension `M·T⁻¹`, ratio-scale, whose value happens to be complex. It is not two kinds and it
is not a new dimension. -/

/-- Mechanical impedance, `M·T⁻¹` — one kind, ratio-scale. Its *value* is complex; its *kind*
is not. -/
def impedance : DimensionedKind :=
  { kind := { id := "mechanical impedance", scale := .ratio }
    dim := Dim.mass * Dim.time⁻¹ }

/-- **MR14 holds.** The impedance `Z = 3 + 4i`, as one quantity of one kind at a complexified
executable carrier. Note `Complex` here is PKC's carrier functor `R ↦ Complex R`, not
Mathlib's `ℂ`: `ℂ` is `{re im : ℝ}` and `ℝ` does not reduce, so no `ℂ`-valued program runs.
`Complex Float` runs. -/
def Z : Quantity impedance.kind (PropertyKindCalculus.Complex Float) := ⟨⟨3, 4⟩⟩

/-- It is one kind at one dimension — the complexity is nowhere in the kind layer. -/
example : impedance.toDimension = Dim.mass * Dim.time⁻¹ := rfl

/-- **MR14 holds.** And it *computes*: the same `Quantity.mul`, the same `ProductKind` gate,
now performing a complex product. `Z² = (3+4i)² = −7 + 24i`. -/
def ZSq : Quantity impedance.kind (PropertyKindCalculus.Complex Float) :=
  Quantity.mul (ProductKind.ofRatio _ _ _) Z Z

#guard ZSq.magnitude.re == -7.0
#guard ZSq.magnitude.im == 24.0

/-! The modulus `|Z| = 5`, computed through the carrier: `|Z|² = 3² + 4² = 25`. -/
#guard Z.magnitude.abs2 == 25.0

/-! ### The component roles — where the carrier stops and the kind layer starts

`Quantity.re`/`im` project a complex-carried quantity to its real-carried components at the
same kind, which is the right default: both components of an impedance are
impedance-dimensioned. But the standard names them as *distinct kinds* — IEC 80000-6 lists
resistance and reactance separately, both in ohms — and their scale types differ from the polar
components' (a modulus is ratio-scale, an argument is interval-scale, its origin being a choice
of `t = 0`).

That is a **kind-layer** statement, not a carrier one, and it is available: the two components
are a `DedicatedKind` pair on one system, distinguished by component exactly as the normal
modes were in MR9. This is where MR14 hands back to Tier 2 — a dimension cannot say it, and
neither can a carrier. -/

/-- The driven oscillator, as a system. -/
def driven : System := { id := "driven oscillator" }

/-- Mechanical resistance — the in-phase component of the impedance. -/
def resistance : DedicatedKind :=
  impedance.kind.dedicatedTo driven { id := "in-phase component" }

/-- Mechanical reactance — the quadrature component. Same dimension, same unit, distinct
kind. -/
def reactance : DedicatedKind :=
  impedance.kind.dedicatedTo driven { id := "quadrature component" }

/-- **The two components of one complex quantity are distinct dedicated kinds** — MR9's
capstone, met again inside a single value. -/
theorem resistance_ne_reactance : resistance ≠ reactance :=
  DedicatedKind.distinct_of_component (by decide)

/-! ## MR15 ✅ — exec/spec agreement

`Float` addition is not associative, so `Float` is a `Carrier` and deliberately **not** a
`LawfulCarrier`: the line is drawn exactly there. That is the honest position, and it leaves a
real obligation — to say how the executable carrier's answer relates to the specification
carrier's, rather than to change the subject. -/

/-- **MR15 holds.** `Float` is a `Carrier` — quantities can be carried in it and the model
runs — while *not* being a `LawfulCarrier`, so no law is silently claimed for it. The
distinction is the type system's, not a comment. -/
example : Carrier Float := inferInstance

/-- **MR15 holds.** `CarrierRefinement E S` is the bridge and `Quantity.add_refines` is the
kind-indexed capstone: a law over the lawful spec carrier descends to the exec carrier as one
rounding step. `Torch` instantiates it at genuine IEEE binary32. Named here rather than
re-derived — the point for this benchmark is that the obligation is *discharged somewhere*
instead of being invisible. -/
example {E S : Type} [Carrier E] [Carrier S] [CarrierRefinement E S]
    {k : KindOfProperty} (h : DifferenceKind k) (x y : Quantity k E) :
    (Quantity.toSpec (Quantity.add h x y) : Quantity k S)
      = Quantity.roundBy (CarrierRefinement.round (E := E))
          (Quantity.add h (Quantity.toSpec x) (Quantity.toSpec y)) :=
  Quantity.add_refines h x y

/-! ### The scope of that ✅, stated — because the oscillator is outside it

Rule 5 of the benchmark applies here more sharply than anywhere else in this file.
`CarrierRefinement` carries exactly two laws, `toSpec_zero` and `toSpec_add`, so the descent
above is available for **aggregation** and for nothing else. There is no `mul_refines`.

Every formula this oscillator computes is multiplicative. `stiffness` is `m · ω · ω`;
`ξ² = ℏ/(mω)` is a quotient; the potential energy is a four-fold product; `Z²` is a complex
product; and Tier 6's scalar product is a sum *of products*. So `stiffnessFloat ⟨5⟩ ⟨2⟩ == 20.0`
above is a `#guard` — a computation that happened — with **nothing relating it to
`stiffnessReal`**, and MR15's ✅ rests on a theorem that does not reach the arithmetic the model
actually performs.

The honest reading is that the *obligation is named and the mechanism exists*, which is what
separates attempt 4 from attempts 1–3 (they have no exec/spec distinction at all, so there is
no gap for them to have a scope for). What it is not is a closed case. The multiplicative
forward-error story does exist in this library — `Uncertainty.Adequacy.DagBound`'s
`dag_fp32_error_bound` accumulates per-node half-ulp budgets across an `add`/`sub`/`mul`/`div`
DAG, with a product's operands correctly weighted by each other's magnitude, grounded in
TorchLean's `FP32.{mul,div}_abs_error` — but it is stated over an untyped expression tree
rather than over `Quantity k R`, so it does not connect to the kind index here. Routing it
through `CarrierRefinement` is the open decision recorded in `UNCERTAINTY.md` §7. -/

end Tier5

/-! # Tier 6 — geometry (MR16 ✅, MR17 ✅, MR18 ✅, MR19 ✅)

Tier 5 asked *which numbers*. This tier asks the two questions that remain once a model leaves
one dimension: **how numbers may be changed**, and **what happens when the same physics is
written in a different coordinate system**. Both are representation questions, and neither is
a dimension question — which is why they are a tier and not a footnote to Tier 1. -/

namespace Tier6

open PropertyKindCalculus.Complex

/-! ## MR16 ✅ — a carrier morphism cannot change the kind

The move this requirement is about is in PhysLib's own source. `HarmonicOscillator.hamiltonian`
acts on a complex Hilbert space while `potentialFunction` is real-valued, and the two are
joined by

```
def potentialOperator : Q.HS →ₗ.[ℂ] Q.HS := 𝓜 volume (ofReal ∘ Q.potentialFunction)
```

`ofReal ∘ Q.potentialFunction` is a change of *numbers* inside a single model: the same
physical quantity — the potential energy at a configuration — re-carried from `ℝ` into `ℂ` so
that it can act as a multiplication operator. It has no dimensional content whatsoever, and
nothing in PhysLib prevents such a composition from also changing what the value *is*.

In PKC the guarantee is by parametricity rather than by care, and it is legible in the
signature alone: `k` is fixed across the arrow, so there is no way to change a kind with a
carrier map. -/

/-- info: @Quantity.castCarrier : {k : KindOfProperty} → {R S : Type} → (R → S) → Quantity k R → Quantity k S -/
#guard_msgs in
#check @Quantity.castCarrier

/-- **MR16 holds.** The `ℝ ↪ Complex ℝ` embedding — PhysLib's `ofReal`, in this library's
vocabulary — applied to a mass. The result type is *forced* to be a mass. -/
noncomputable def massComplexified (q : Quantity mass.kind ℝ) :
    Quantity mass.kind (PropertyKindCalculus.Complex ℝ) :=
  q.castCarrier ofReal

/-- The value is carried across unchanged; only the representation moved. -/
theorem massComplexified_re (q : Quantity mass.kind ℝ) :
    (massComplexified q).magnitude.re = q.magnitude := rfl

/-! **MR16 holds.** And the kind cannot be changed on the way. There is no argument of
`castCarrier` in which a different kind could be supplied, so the attempt is not a wrong
value — it is a type error. -/
#check_failure (fun (q : Quantity mass.kind ℝ) =>
  (q.castCarrier ofReal : Quantity absoluteEnergy.kind (PropertyKindCalculus.Complex ℝ)))

/-! The same holds in the other direction, and for the executable carrier: narrowing,
widening, rounding and complexifying are all one operation with one guarantee. -/

/-- Down to the executable carrier, at the same kind. -/
def massAsFloat (q : Quantity mass.kind Nat) : Quantity mass.kind Float :=
  q.castCarrier Nat.toFloat

/-! ## MR17 ✅ — a vector quantity is one quantity

ISO 80000-2 §18: a vector quantity is a *numerical* array multiplied by a **single scalar
unit**, not a collection of per-coordinate quantity values each with its own number and unit.
That is `Quantity k (Fin n → R)`: one kind, one unit, `n` components.

The two oscillators now sit in a plane, so a position is a `Fin 2 → ℝ`. -/

/-- Position, `L` — one kind for the whole vector: the catalogue's own position vector
(3-1.10). -/
def position : DimensionedKind := Iso80000.Part3.positionVector

/-- Velocity, `L·T⁻¹` — the catalogue's own 3-10.1. -/
def velocity : DimensionedKind := Iso80000.Part3.velocity

/-- Speed squared, `L²·T⁻²` — what a velocity contracted with itself lands at. -/
def speedSq : DimensionedKind :=
  { kind := { id := "speed squared", scale := .ratio },
    dim := Dim.length * Dim.length * Dim.time⁻¹ * Dim.time⁻¹ }

/-- **MR17 holds.** A's velocity in the plane, `(3, 4)` — *one* quantity of *one* kind whose
magnitude is a numerical 2-vector. Not two quantities, and not a new dimension. -/
noncomputable def vA : Quantity velocity.kind (Fin 2 → ℝ) :=
  ⟨fun i => if i = 0 then 3 else 4⟩

/-- **MR17 holds.** A component read off a vector quantity is a quantity of the *same* kind —
the unit belongs to the whole vector (§18), so reading one component keeps it. -/
noncomputable example : Quantity velocity.kind ℝ := ⟨vA.magnitude 0⟩

/-- **MR17 holds.** The additivity laws transfer to the vector carrier by the *same*
parametric proof used for scalars — nothing about the array is re-proved. -/
theorem vector_add_comm (h : DifferenceKind velocity.kind)
    (x y : Quantity velocity.kind (Fin 2 → ℝ)) :
    Quantity.add h x y = Quantity.add h y x :=
  Quantity.add_comm h x y

/-! **MR17 holds, and this is the sharp half.** Lean supplies a pointwise `Mul (Fin 2 → ℝ)`,
so before the `ScalarCarrier` gate the componentwise product of two velocities elaborated as
a `speedSq`-kinded quantity: correctly kinded, correctly dimensioned, and not a physical
operation of any sort. It no longer does. -/
#check_failure (fun (x y : Quantity velocity.kind (Fin 2 → ℝ)) =>
  Quantity.mul (ProductKind.ofRatio velocity.kind velocity.kind speedSq.kind) x y)

/-! ## MR18 ✅ — frame covariance, and what survives it

The oscillators sit in a plane, and the plane has no preferred axes. Two frames, related by
the Pythagorean rotation `cos θ = 3/5`, `sin θ = 4/5` — chosen so every entry is rational and
every fact below is `norm_num`-decidable, and *not* a quarter turn, which merely permutes the
axes and would hide the phenomenon MR19 turns on. -/

/-- The laboratory frame. -/
def lab : Frame := { id := "laboratory" }
/-- A frame rotated in the plane of the oscillators. Nothing distinguishes it physically. -/
def rotated : Frame := { id := "rotated by arctan 4/5" }

/-- The change of frame: `[[3/5, −4/5], [4/5, 3/5]]`. -/
noncomputable def turn : FrameChange 2 ℝ lab rotated :=
  ⟨fun i j => if i = 0 then (if j = 0 then 3/5 else -(4/5))
              else (if j = 0 then 4/5 else 3/5)⟩

/-- It is a rotation — orthonormal, so the invariance theorem applies to it. -/
theorem turn_isOrthonormal : turn.IsOrthonormal := by
  rw [isOrthonormal_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [turn, Fin.sum_univ_succ] <;> norm_num

/-- A's velocity, read in the laboratory frame. -/
noncomputable def vLab : InFrame lab .vector velocity.kind (Fin 2 → ℝ) := ⟨vA⟩

/-- The same velocity, read in the rotated frame. **One quantity, two readings** — this is
not a second velocity. -/
noncomputable def vRot : InFrame rotated .vector velocity.kind (Fin 2 → ℝ) :=
  InFrame.toFrameVector turn vLab

/-! **MR18 holds.** Two readings taken in different frames cannot be added. There is no wrong
answer to write here: the sum does not elaborate, because the frame is an index of the type
and `lab` is not `rotated`. This is the error the whole tier exists for — dimension, unit,
kind, object and carrier all agree, and the sum is meaningless. -/
#check_failure (InFrame.add (DifferenceKind.ofScale) vLab vRot)

/-- The product law licensing `velocity × velocity = speed²`. -/
theorem vv : ProductKind velocity.kind velocity.kind speedSq.kind :=
  ProductKind.ofRatio _ _ _

/-- **MR18 holds — the payoff.** The speed squared computed from the laboratory components and
from the rotated components is the *same number*. This is what "a change of representation does
not change the physical equations" means, discharged rather than asserted: every scalar a
mechanical model reads off a configuration is a contraction of vector quantities, and
contractions do not move. -/
theorem speedSq_frame_invariant :
    (InFrame.normSq vv vRot).components = (InFrame.normSq vv vLab).components :=
  normSq_toFrameVector turn_isOrthonormal vv vLab

/-- And concretely: `3² + 4² = 25` in the laboratory frame. -/
theorem speedSq_lab : (InFrame.normSq vv vLab).components = 25 := by
  simp [InFrame.normSq, InFrame.dot, InFrame.components, vLab, vA]
  norm_num

/-- **MR18 holds — the other half, stated so it cannot be over-read.** A *component* is not
invariant. The same velocity has first component `3` in the laboratory frame and `−7/5` in the
rotated one, so a discipline that tracks components rather than quantities is tracking
something that depends on a choice nobody wrote down. -/
theorem component_frame_dependent :
    (vRot.component 0).components ≠ (vLab.component 0).components := by
  simp [vRot, vLab, InFrame.component, InFrame.toFrameVector, FrameChange.mulVec,
    InFrame.components, vA, turn, sumFin]
  norm_num

/-- **MR18, the capstone.** The contraction is invariant; the components are not; and both
facts are about *one* quantity. A scheme that has only the second half has recorded numbers
without recording what they are numbers of. -/
theorem mr18_capstone :
    (InFrame.normSq vv vRot).components = (InFrame.normSq vv vLab).components
      ∧ (vRot.component 0).components ≠ (vLab.component 0).components :=
  ⟨speedSq_frame_invariant, component_frame_dependent⟩

/-! ## MR19 ✅ — an indexed family is not a set of vector components

This is the requirement PhysLib's own structure raises. `HarmonicOscillator d` carries

```
ω : Fin d → ℝ
potentialMatrix := diagonal ((2⁻¹ * m) • ω ^ 2)
```

and a configuration is likewise a `Fin d → ℝ`. **The two are the same Lean type and transform
completely differently.**

  * A position or velocity is a **vector**: its components mix under a change of frame, and
    `MR18` above is the account of what survives.
  * `ω` is not a vector at all. It is the diagonal of a rank-2 object *in its own principal
    frame*, and under a change of frame `M ↦ C M Cᵀ` a diagonal matrix does not stay diagonal
    — so `ω` does not survive as a list of numbers. Rotating an anisotropic oscillator's frame
    destroys `ω`.

`IsIsotropic : ∀ i j, ω i = ω j` is exactly the condition under which it does survive, which is
why MR6's requirement and this one are the same fact seen from two sides: the anisotropic
oscillator has a preferred frame, and the isotropic one does not.

PKC keeps the two apart in three independent ways, none of which is available below the kind
layer. -/

/-- The stiffness matrix `M = diag(ω₀², ω₁²)` of the anisotropic oscillator of MR6, whose
frequencies are `2` and `7`. -/
noncomputable def stiffnessMatrix : InFrame lab .rank2 springConstant.kind (Fin 2 → Fin 2 → ℝ) :=
  ⟨⟨fun i j => if i = j then (if i = 0 then 4 else 49) else 0⟩⟩

/-- **MR19 holds.** Turn the frame and the matrix acquires an off-diagonal entry: the
`(0,1)` component of `C M Cᵀ` is `−108/5`, not `0`. There is no list of two frequencies in the
rotated frame — the axes the list was indexed by are gone. -/
theorem stiffness_not_diagonal_after_turn :
    (InFrame.toFrameRank2 turn stiffnessMatrix).components 0 1 = -(108/5) := by
  simp [InFrame.toFrameRank2, FrameChange.conj, stiffnessMatrix, InFrame.components,
    turn, sumFin]
  norm_num

/-- **MR19 holds (1/3) — the variance is in the type.** The stiffness matrix is `rank2` and a
velocity is `vector`, so the vector transformation law cannot be applied to the stiffness
matrix: the mistake this requirement names is not a wrong answer but a non-expression. -/
example : Variance := .rank2

/-! **MR19 holds (1/3).** Applying the *vector* law to the rank-2 reading does not elaborate. -/
#check_failure (InFrame.toFrameVector turn stiffnessMatrix)

/-! **MR19 holds (2/3) — and the dual mistake is closed too.** A mass is a `scalar`, so the
vector law cannot be applied to it either. This is the error that makes a `Fin 3 → ℝ` of three
masses rotate into three numbers that are masses of nothing. -/
#check_failure (fun (m : InFrame lab .scalar mass.kind ℝ) => InFrame.toFrameVector turn m)

/-- **MR19 holds (3/3) — the degrees of freedom stay individuated.** MR6 established that the
two axes of an anisotropic oscillator are distinct *systems*, so their frequencies are not
interchangeable. That is the kind-layer reading of the same fact: `ω 0` and `ω 1` are two
quantities of two systems, not two components of one quantity — which is why no frame change
acts on them, and why writing them as a `Fin 2 → ℝ` was the category error all along. -/
theorem mr19_frequencies_are_not_components :
    dofX ≠ dofY ∧ ωX.magnitude ≠ ωY.magnitude :=
  ⟨by decide, not_isotropic⟩

/-- **MR19, the capstone.** One Lean type, `Fin 2 → ℝ`, carrying two things that differ in what
a change of frame does to them: a velocity's contraction is invariant, and the frequency list's
matrix stops being a frequency list. Nothing in a dimension, a unit, a kind, an object or a
carrier separates these — the separating datum is the variance, and this tier is where it is
written down. -/
theorem mr19_capstone :
    (InFrame.normSq vv vRot).components = (InFrame.normSq vv vLab).components
      ∧ (InFrame.toFrameRank2 turn stiffnessMatrix).components 0 1 ≠ 0 := by
  refine ⟨speedSq_frame_invariant, ?_⟩
  rw [stiffness_not_diagonal_after_turn]
  norm_num

end Tier6

/-! ## MR32 ✅ — the lattice is theorems, and now the sum consumes them (appended)

Appended after the first scoring pass; see `Attempt1Reals` for the occasion. At first
scoring this cell was ⚠️: `Specializes` and `MutuallyComparable` carried the lattice at the
*kind* level, but nothing above that level consumed them — `Quantity`'s addition was
same-kind, and there was no lift of a `Quantity kineticEnergy R` to the join it provably
specializes — so with the kinds kept honest, `H = T + V` was exactly as unwritable here as
in Attempt 3. The difference between the two failures was named then and mattered:
Attempt 3's obstruction is *structural* (the tag is a group element; removing it destroys
what it bought), while this one was *missing machinery with a stated design* — a
kind-changing map licensed by a `Specializes` proof, the specialization twin of
`Extensive`'s licensed aggregation.

That machinery has since landed, built to this benchmark's specification
(`PropertyKindCalculus.SpecializationLift`): `Quantity.widen` re-classifies a quantity
along a proved specialization, magnitude untouched, and the curated `KindJoin` table — the
join twin of `KindMul` — licenses the sum *at the join*, through the same scoped operator
discipline as the rest of the algebra. The probes below now show both halves at once:
the kinds stay distinct, and the Hamiltonian is writable, landing where physics says it
lives. -/

section MR32

open scoped PropertyKindCalculus.OperatorTable

/-- The join of the family: the catalogue's mechanical energy (4-28.3) — exactly the
`T + V` sum the join licenses. -/
def energyGeneral : KindOfProperty := (Iso80000.Part4.mechanicalEnergy).kind

/-- Kinetic energy — the catalogue's own 4-28.2 (`½·m·⟪v,v⟫` from a mass and a speed). -/
def kineticEnergy : KindOfProperty := (Iso80000.Part4.kineticEnergy).kind

/-- Potential energy — the catalogue's own 4-28.1 (`½·k·⟪x,x⟫` from a stiffness and a
displacement). -/
def potentialEnergy : KindOfProperty := (Iso80000.Part4.potentialEnergy).kind

/-- The specialization edges of the family. -/
inductive EnergyEdge : KindOfProperty → KindOfProperty → Prop where
  | kinetic   : EnergyEdge kineticEnergy energyGeneral
  | potential : EnergyEdge potentialEnergy energyGeneral

/-- Distinguishability: the kinds are distinct — decided, off the derived `DecidableEq`. -/
theorem mr32_kinds_distinct : kineticEnergy ≠ potentialEnergy := by decide

/-- Comparability: kinetic and potential energy are mutually comparable, witnessed by the
join — R2's lattice, as a theorem rather than a convention. -/
theorem mr32_comparable : MutuallyComparable EnergyEdge kineticEnergy potentialEnergy :=
  ⟨energyGeneral, .of_edge .kinetic, .of_edge .potential⟩

/-- The join-table entry: kinetic and potential energy join at energy — the same two edge
proofs `mr32_comparable` exhibits, plus the scale gate for `+` discharged at the join. -/
instance : KindJoin EnergyEdge kineticEnergy potentialEnergy energyGeneral :=
  ⟨.of_edge .kinetic, .of_edge .potential, .ofScale⟩

/-- The symmetric entry, so `V + T` lands too — from the first, witnesses unrestated. -/
instance : KindJoin EnergyEdge potentialEnergy kineticEnergy energyGeneral :=
  KindJoin.symm inferInstance

/-- At the join, the sum was always licensed: energy + energy is energy. -/
example (T V : Quantity energyGeneral Float) : Quantity energyGeneral Float := T + V

/-- **The gap, closed.** With the kinds kept distinct, the Hamiltonian is writable — and
it lands at the join, where physics says it lives, not at either sub-kind. -/
def hamiltonian (T : Quantity kineticEnergy Float)
    (V : Quantity potentialEnergy Float) : Quantity energyGeneral Float :=
  T + V

/-- The join sum is not a new addition — it erases to the bare-real sum, `rfl`. -/
theorem hamiltonian_magnitude (T : Quantity kineticEnergy Float)
    (V : Quantity potentialEnergy Float) :
    (hamiltonian T V).magnitude = T.magnitude + V.magnitude := rfl

/-! **Still not identity.** Comparability licenses the sum at the join and only there —
the Hamiltonian does not land at either sub-kind: -/
#check_failure (fun (T : Quantity kineticEnergy Float) (V : Quantity potentialEnergy Float) =>
  (T + V : Quantity kineticEnergy Float))

/-! **And the curation still gates.** Kinds with no registered join do not add: a mass and
a kinetic energy have no common super-kind on file, so their sum does not elaborate — the
compile error the bare magnitude cannot give, preserved through the lift. -/
#check_failure (fun (m : Quantity mass.kind Float) (T : Quantity kineticEnergy Float) =>
  m + T)

/-- **And the object gate survives the join.** On one oscillator, the join sum carries the
object through: A's total energy is A's. -/
example (T : IndividualQuantity oscA kineticEnergy Float)
    (V : IndividualQuantity oscA potentialEnergy Float) :
    IndividualQuantity oscA energyGeneral Float := T + V

/-! Oscillator A's kinetic energy does not add to oscillator B's potential energy,
licensed lattice or not — instance resolution fails to unify the objects: -/
#check_failure (fun (T : IndividualQuantity oscA kineticEnergy Float)
    (V : IndividualQuantity oscB potentialEnergy Float) => T + V)

/-- **MR32, the capstone.** Both requirements at once, in one `Prop`: the kinds are
distinct, they are mutually comparable, and the Hamiltonian erases to the bare-real sum.
Distinctness without over-rejection — the conjunction no other attempt can state. -/
theorem mr32_capstone :
    kineticEnergy ≠ potentialEnergy
      ∧ MutuallyComparable EnergyEdge kineticEnergy potentialEnergy
      ∧ ∀ (T : Quantity kineticEnergy Float) (V : Quantity potentialEnergy Float),
          (hamiltonian T V).magnitude = T.magnitude + V.magnitude :=
  ⟨mr32_kinds_distinct, mr32_comparable, fun _ _ => rfl⟩

end MR32

end PropertyKindCalculus.Examples.HarmonicOscillator.Attempt4
