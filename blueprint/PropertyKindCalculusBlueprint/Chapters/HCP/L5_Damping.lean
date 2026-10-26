import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "HCP.L5_Damping"

#doc (Manual) "L5 — The oscillation dies out" =>
%%%
tag := "hcp-l5"
%%%

# Synopsis

## Purpose

Optional. Add a viscous damper to oscillator A, so that its energy is no longer conserved. Three quantities are easy to confuse here: PhysLib's damping constant γ (kg/s); ISO 80000-3's damping coefficient δ = γ/(2m) (s⁻¹), which PhysLib calls the decay rate; and the angular frequency ω₀ (rad/s), which has the same dimension as δ. The lesson gives each its own kind, so adding δ to ω₀ fails to type-check. `decayRateOf` computes δ from one oscillator's γ and mass with `IndividualQuantity.div`, so oscillator B's mass cannot be used for oscillator A's δ.

## PKC vocabulary in scope

New at this step:
- `KindOfProperty` (`id`, `scale`) — define a kind of property; the lesson defines its own kind for γ.
- `ScaleType.ratio` — the scale type that licenses × and ÷.
- `dampingCoefficient` — ISO 80000-3 damping coefficient δ, dimension T⁻¹.
- `KindDiv`, `QuotientKind.ofRatio` — a curated quotient law, here δ = γ/(2m).
- `Quantity.add` — kind- and scale-gated addition.
- `IndividualQuantity.toQuantity` — forget the bearer.
- `angularFrequencyK` — the oscillator's ω.

Carried from earlier steps: DimensionedKind, `IndividualQuantity` and its `add`/`div`, `DifferenceKind.ofScale`, `SortOfSystem`, `Sorted`, `Designated`, `massK`, `springConstantK`.

## Verifiable properties

- The damped oscillator's energy decreases at the rate stated by PhysLib's energy-dissipation theorem (theorem) `HCP.L5_Damping#energy_dissipation`.
- `decayRateOf` divides A's γ by A's 2m, and its magnitude equals PhysLib's `decayRate`; using B's mass instead fails with a type mismatch (refused) `HCP.L5_Damping#kinds_and_decay_rate`.
- δ and ω₀ have the same dimension, T⁻¹, and adding them fails to type-check (refused) `HCP.L5_Damping#same_dimension_different_kinds`.
- PhysLib's `IsUnderdamped` is equivalent to δ < ω₀. Comparing the two as kinded quantities fails with a type mismatch, because their kinds differ; `IsUnderdamped` implies that the magnitude of δ is less than the magnitude of ω₀ (theorem) `HCP.L5_Damping#underdamped_regime`.
- Subtracting an earlier record of A's δ from a later one type-checks as an `IndividualQuantity` about A of the damping-coefficient kind, whose magnitude is the difference of the two decay rates; subtracting B's δ from A's fails with a type mismatch (type-checked) `HCP.L5_Damping#same_oscillator_states`.

## Errors prevented

- Similar names, different kinds: PhysLib's damping constant γ (kg/s) used as ISO's damping coefficient δ (s⁻¹) (`HCP.L5_Damping#kinds_and_decay_rate`).
- Same dimension, different kind: δ + ω₀, which dimensions alone accept (`HCP.L5_Damping#same_dimension_different_kinds`).
- Cross-system contamination: oscillator B's mass used in oscillator A's δ (`HCP.L5_Damping#kinds_and_decay_rate`).

# Lesson


The oscillator loses energy. This optional rung adds a damper to the nominally named
whole-system model. One name is one system; records under that name are its states at
different times, configurations, or rival estimates of it—comparing them is the point;
distinct names are distinct systems.

```anchor damped_rig_and_parts
/--
One name is one system; records under that name are its states at different times,
configurations, or rival estimates of it—comparing them is the point. Distinct names
are distinct systems.
-/
inductive Osc | A | B
deriving DecidableEq, Repr

structure DampedRig (o : Osc) where
  osc : _root_.ClassicalMechanics.DampedHarmonicOscillator

inductive DampedPart | Body | Spring | Damper
deriving DecidableEq, Repr

structure PartOf (o : Osc) where
  part : DampedPart
deriving DecidableEq, Repr

def dampedPartS : SortOfSystem := ⟨"damped oscillator component"⟩

instance {o : Osc} : Sorted (PartOf o) := ⟨fun _ => dampedPartS⟩

instance {o : Osc} : Designated (PartOf o) where
  designation
    | ⟨.Body⟩ => ⟨"body"⟩
    | ⟨.Spring⟩ => ⟨"spring"⟩
    | ⟨.Damper⟩ => ⟨"damper"⟩
  designation_inj {x y} h := by
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    cases x <;> cases y <;> first | rfl | exact absurd (System.mk.inj h) (by decide)

def bodyPart (o : Osc) : PartOf o := ⟨.Body⟩
def springPart (o : Osc) : PartOf o := ⟨.Spring⟩
def damperPart (o : Osc) : PartOf o := ⟨.Damper⟩

def massOf {o : Osc} (r : DampedRig o) :
    IndividualQuantity o massK ℝ :=
  ⟨r.osc.m⟩

def springConstantOf {o : Osc} (r : DampedRig o) :
    IndividualQuantity (springPart o) springConstantK ℝ :=
  ⟨r.osc.k⟩
```

_1. Energy is no longer conserved._ The HCP state wraps PhysLib's damped oscillator,
so the upstream dissipation results apply to `r.osc`. L0–L4's conservation assumption
ends here:

```anchor energy_dissipation
/-- Dissipation: Proves that under oscillator O's damped equation, the energy derivative is −γ times the squared speed. -/
lemma energy_dissipation_on_state {o : Osc} (r : DampedRig o)
    (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time)
    (h1 : r.osc.EquationOfMotion xₜ) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (r.osc.energy xₜ) t =
      - r.osc.γ * inner ℝ (∂ₜ xₜ t) (∂ₜ xₜ t) :=
  r.osc.energy_dissipation_rate xₜ t h1 hx

/-- Dissipation: Proves that positive γ and nonzero velocity make oscillator O's energy derivative strictly negative. -/
lemma energy_not_conserved_on_state {o : Osc} (r : DampedRig o)
    (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time)
    (h1 : r.osc.EquationOfMotion xₜ) (hx : ContDiff ℝ ∞ xₜ)
    (hdx : ∂ₜ xₜ t ≠ 0) (hγ : 0 < r.osc.γ) :
    ∂ₜ (r.osc.energy xₜ) t < 0 :=
  r.osc.energy_not_conserved xₜ t h1 hx hdx hγ
```

_2. One name, two kinds._ `γ` is the viscous damping constant read on the damper
(kg/s), and `m` is measured on the body. Both quantities retain the whole oscillator's
bearer `o`. ISO 3-24's damping coefficient `δ` (s⁻¹) is instead PhysLib's `decayRate`,
attached to the whole. The local quotient law makes the typed `γ/(m + m)` formula possible:

```anchor kinds_and_decay_rate
def viscousDampingConstantK : KindOfProperty :=
  { id := "viscous damping constant", scale := .ratio }

def dampingCoefficientK : KindOfProperty :=
  Iso80000.Part3.dampingCoefficient.kind

def dampingConstantOf {o : Osc} (r : DampedRig o) :
    IndividualQuantity o viscousDampingConstantK ℝ :=
  ⟨r.osc.γ⟩

instance : KindDiv viscousDampingConstantK massK dampingCoefficientK :=
  ⟨QuotientKind.ofRatio _ _ _⟩

def decayRateOf {o : Osc} (r : DampedRig o) :
    IndividualQuantity o dampingCoefficientK ℝ :=
  -- Write 2m as m + m to keep the mass on the oscillator bearer.
  IndividualQuantity.div
    (KindDiv.law (k₁ := viscousDampingConstantK) (k₂ := massK)
      (k := dampingCoefficientK))
    (dampingConstantOf r)
    (IndividualQuantity.add DifferenceKind.ofScale (massOf r) (massOf r))

/-- Kind vs dimension: Proves that oscillator O's indexed damping-coefficient magnitude equals PhysLib's decayRate γ/(2m). -/
lemma decayRateOf_magnitude {o : Osc} (r : DampedRig o) :
    (decayRateOf r).magnitude = r.osc.decayRate := by
  simp only [decayRateOf, IndividualQuantity.div_magnitude,
    IndividualQuantity.add_magnitude, dampingConstantOf, massOf]
  change r.osc.γ / (r.osc.m + r.osc.m) = r.osc.decayRate
  rw [← two_mul, r.osc.gamma_eq_two_mul_m_mul_decayRate]
  have hm : (2 * r.osc.m) ≠ 0 :=
    mul_ne_zero (by norm_num) r.osc.m_ne_zero
  field_simp [hm]

def angularFrequencyOf {o : Osc} (r : DampedRig o) :
    IndividualQuantity o angularFrequencyK ℝ :=
  ⟨r.osc.ω⟩

/-- Kind vs dimension: Proves that oscillator O's indexed angular-frequency magnitude equals its angular frequency ω. -/
lemma angularFrequencyOf_magnitude {o : Osc} (r : DampedRig o) :
    (angularFrequencyOf r).magnitude = r.osc.ω := rfl

-- Kind vs dimension: Bare reals let Lean compare oscillator A's γ (kg/s) with ω (s⁻¹), despite their different dimensions; this is not the δ < ω regime test.
example (r : DampedRig .A) : Prop := r.osc.γ < r.osc.ω

-- Kind vs dimension: Proves that oscillator A's indexed decay-rate magnitude equals PhysLib's decayRate.
example (r : DampedRig .A) :
    (decayRateOf r).magnitude = r.osc.decayRate :=
  decayRateOf_magnitude r

-- Dissipation: Proves that PhysLib's law for oscillator A is γ = 2m·decayRate, relating damper reading, body mass, and decay rate.
example (r : DampedRig .A) :
    r.osc.γ = 2 * r.osc.m * r.osc.decayRate :=
  r.osc.gamma_eq_two_mul_m_mul_decayRate

-- Bearer safety: Refused: type mismatch between oscillator B's mass bearer and oscillator A's quotient bearer; this prevents computing A's decay rate with B's mass.
/--
error: Application type mismatch: The argument
  b
has type
  DampedRig Osc.B
but is expected to have type
  DampedRig Osc.A
in the application
  massOf b
-/
#guard_msgs in
example (a : DampedRig .A) (b : DampedRig .B) :=
  IndividualQuantity.div
    (KindDiv.law (k₁ := viscousDampingConstantK) (k₂ := massK)
      (k := dampingCoefficientK))
    (dampingConstantOf a) (massOf b)
```

The real-valued `γ < ω` above is accepted, but wrong: `γ` is kg/s, not the whole
system's decay rate. `massOf` and `dampingConstantOf` both retain the oscillator's
nominal bearer: mass is measured on the designated body and `γ` on the designated damper.
Writing `2m` as `m + m` keeps the quotient bearer-safe; the pinned refusal below prevents
dividing A's damper reading by B's mass.

_3. Same dimension, different kind._ Both `δ` and natural angular frequency `ω₀` have
dimension `T⁻¹`; the bare-real sum is accepted, while the kinded sum is refused:

```anchor same_dimension_different_kinds
-- Kind vs dimension: Proves that damping coefficient δ and angular frequency ω both have dimension T⁻¹; matching dimensions alone do not license mixing them.
example :
    Iso80000.Part3.dampingCoefficient.dim =
      Iso80000.Part3.angularFrequency.dim :=
  rfl

-- Kind vs dimension: Proves that dampingCoefficientK and angularFrequencyK are distinct kinds despite their shared T⁻¹ dimension.
example : dampingCoefficientK ≠ angularFrequencyK := by
  decide

-- Kind vs dimension: Bare reals accept oscillator A's δ + ω as a real although the decay-rate and angular-frequency kinds differ; no sum kind is recorded.
example (r : DampedRig .A) : ℝ :=
  r.osc.decayRate + r.osc.ω

-- Kind vs dimension: Refused: type mismatch between dampingCoefficientK and angularFrequencyK quantities; this prevents summing δ and ω despite their shared T⁻¹ dimension.
/--
error: Application type mismatch: The argument
  (angularFrequencyOf r).toQuantity
has type
  Quantity angularFrequencyK ℝ
but is expected to have type
  Quantity dampingCoefficientK ℝ
in the application
  Quantity.add ⋯ (decayRateOf r).toQuantity (angularFrequencyOf r).toQuantity
-/
#guard_msgs in
example (r : DampedRig .A) :=
  Quantity.add DifferenceKind.ofScale
    (decayRateOf r).toQuantity (angularFrequencyOf r).toQuantity
```

_4. Regime._ PhysLib's `isUnderdamped_iff_decayRate_lt` reduces the regime to the
numerical condition. Its kinded `<` is refused; the accepted HCP comparison states
explicitly that magnitudes are being compared:

```anchor underdamped_regime
-- Regime: Proves that oscillator A is underdamped exactly when its numerical decay rate δ is below ω.
example (r : DampedRig .A) :
    r.osc.IsUnderdamped ↔ r.osc.decayRate < r.osc.ω :=
  r.osc.isUnderdamped_iff_decayRate_lt

-- Regime: Refused: type mismatch between angularFrequencyK and dampingCoefficientK; direct comparison erases the magnitude conversion and assumes rad = 1.
/--
error: Type mismatch
  (angularFrequencyOf r).toQuantity
has type
  Quantity angularFrequencyK ℝ
but is expected to have type
  Quantity dampingCoefficientK ℝ
-/
#guard_msgs in
example (r : DampedRig .A) :=
  (decayRateOf r).toQuantity < (angularFrequencyOf r).toQuantity

/-- Regime: Proves that an underdamped oscillator O has indexed decay-rate magnitude below its indexed angular-frequency magnitude. -/
lemma underdamped_magnitude_test {o : Osc} (r : DampedRig o)
    (h : r.osc.IsUnderdamped) :
    (decayRateOf r).magnitude < (angularFrequencyOf r).magnitude := by
  rw [decayRateOf_magnitude, angularFrequencyOf_magnitude]
  exact r.osc.isUnderdamped_decayRate h
```

The honest criterion is the dimensionless ratio `δ/ω₀ < 1`. Directly ordering the
kinded quantities erases that conversion and silently assumes `rad = 1`.

_5. States of one oscillator._ Two `DampedRig .A` records can describe the same
oscillator before and after its damper ages. Their typed difference computes the change
from those states; B remains a different system:

```anchor same_oscillator_states
def decayRateChange (earlier later : DampedRig .A) :
    IndividualQuantity Osc.A dampingCoefficientK ℝ :=
  IndividualQuantity.add DifferenceKind.ofScale
    (decayRateOf later) (-(decayRateOf earlier))

/-- Same-name records: Proves that oscillator A's indexed decay-rate difference has magnitude later decay rate minus earlier decay rate. -/
lemma decayRateChange_magnitude (earlier later : DampedRig .A) :
    (decayRateChange earlier later).magnitude =
      later.osc.decayRate - earlier.osc.decayRate := by
  simp [decayRateChange, IndividualQuantity.add_magnitude,
    IndividualQuantity.neg_magnitude, decayRateOf_magnitude]
  change later.osc.decayRate + -(earlier.osc.decayRate) =
    later.osc.decayRate - earlier.osc.decayRate
  ring

-- Bearer safety: Refused: type mismatch between oscillator A's and oscillator B's damping-coefficient bearers; this prevents subtracting one oscillator's decay rate from the other's.
/--
error: Type mismatch
  -decayRateOf b
has type
  IndividualQuantity Osc.B dampingCoefficientK ℝ
but is expected to have type
  IndividualQuantity Osc.A dampingCoefficientK ℝ
-/
#guard_msgs in
example (a : DampedRig .A) (b : DampedRig .B) :=
  IndividualQuantity.add DifferenceKind.ofScale
    (decayRateOf a) (-(decayRateOf b))
```

`Body`, `Spring`, and `Damper` are designated particulars of the damped oscillator.
`γ` is measured on the damper; `δ` and `IsUnderdamped` describe the whole. Records
under one name may be states, configurations, or rival estimates; distinct names are
distinct systems. L5 is optional and revisits the no-dissipation assumption left by L0–L4.
