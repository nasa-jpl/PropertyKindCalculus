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

Optional. Add a damper to oscillator A and drop energy conservation. PhysLib's damping constant γ (kg/s), ISO's damping coefficient δ = γ/(2m) (s⁻¹) and angular frequency ω₀ share names or dimensions; kinds keep them apart, and δ is computed from the oscillator's own γ and mass.

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

- The damped oscillator's energy decreases at the rate PhysLib states (theorem) `HCP.L5_Damping#energy_dissipation`.
- δ is computed from oscillator A's own γ and mass; B's mass is refused (refused) `HCP.L5_Damping#kinds_and_decay_rate`.
- δ and ω₀ have the same dimension, and adding them is refused (refused) `HCP.L5_Damping#same_dimension_different_kinds`.
- The underdamped test reduces to δ < ω₀; the kinded comparison is refused and the magnitude form is accepted (theorem) `HCP.L5_Damping#underdamped_regime`.
- Two states of oscillator A give a typed change in δ (type-checked) `HCP.L5_Damping#same_oscillator_states`.

## Errors prevented

- One name, two kinds: PhysLib's damping constant γ confused with ISO's damping coefficient δ (`HCP.L5_Damping#kinds_and_decay_rate`).
- Same dimension, different kind: δ + ω₀ accepted by dimensions (`HCP.L5_Damping#same_dimension_different_kinds`).
- Cross-system contamination: oscillator B's mass in oscillator A's decay rate (`HCP.L5_Damping#kinds_and_decay_rate`).


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
lemma energy_dissipation_on_state {o : Osc} (r : DampedRig o)
    (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time)
    (h1 : r.osc.EquationOfMotion xₜ) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (r.osc.energy xₜ) t =
      - r.osc.γ * inner ℝ (∂ₜ xₜ t) (∂ₜ xₜ t) :=
  r.osc.energy_dissipation_rate xₜ t h1 hx

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

lemma angularFrequencyOf_magnitude {o : Osc} (r : DampedRig o) :
    (angularFrequencyOf r).magnitude = r.osc.ω := rfl

example (r : DampedRig .A) : Prop := r.osc.γ < r.osc.ω

example (r : DampedRig .A) :
    (decayRateOf r).magnitude = r.osc.decayRate :=
  decayRateOf_magnitude r

example (r : DampedRig .A) :
    r.osc.γ = 2 * r.osc.m * r.osc.decayRate :=
  r.osc.gamma_eq_two_mul_m_mul_decayRate

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
example :
    Iso80000.Part3.dampingCoefficient.dim =
      Iso80000.Part3.angularFrequency.dim :=
  rfl

example : dampingCoefficientK ≠ angularFrequencyK := by
  decide

example (r : DampedRig .A) : ℝ :=
  r.osc.decayRate + r.osc.ω

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
example (r : DampedRig .A) :
    r.osc.IsUnderdamped ↔ r.osc.decayRate < r.osc.ω :=
  r.osc.isUnderdamped_iff_decayRate_lt

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

lemma decayRateChange_magnitude (earlier later : DampedRig .A) :
    (decayRateChange earlier later).magnitude =
      later.osc.decayRate - earlier.osc.decayRate := by
  simp [decayRateChange, IndividualQuantity.add_magnitude,
    IndividualQuantity.neg_magnitude, decayRateOf_magnitude]
  change later.osc.decayRate + -(earlier.osc.decayRate) =
    later.osc.decayRate - earlier.osc.decayRate
  ring

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
