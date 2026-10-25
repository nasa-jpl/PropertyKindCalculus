/-
# L5 — The oscillation dies out

Solution for the worksheet HCP/Worksheets/L5_Damping.lean.

Five build-checked probes of damping, decay rate, regime, and oscillator states.
-/

module

public import ForPhysLib.ClassicalMechanics.Feasibility
public import Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic
public import PropertyKindCalculus
public import PropertyKindCalculus.Iso80000.Part3

@[expose] public section

open PropertyKindCalculus ForPhysLib.ClassicalMechanics
open InnerProductSpace Time ContDiff
open scoped PropertyKindCalculus.OperatorTable

noncomputable section

namespace HCP.L5_Damping

-- ANCHOR: damped_rig_and_parts
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

-- ANCHOR_END: damped_rig_and_parts

-- ANCHOR: energy_dissipation
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
-- ANCHOR_END: energy_dissipation

-- ANCHOR: kinds_and_decay_rate
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
-- ANCHOR_END: kinds_and_decay_rate

-- ANCHOR: same_dimension_different_kinds
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
-- ANCHOR_END: same_dimension_different_kinds

-- ANCHOR: underdamped_regime
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
-- ANCHOR_END: underdamped_regime

-- ANCHOR: same_oscillator_states
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
-- ANCHOR_END: same_oscillator_states

end HCP.L5_Damping
