/-
# L5 — The oscillation dies out

Five build-checked probes of damping, decay rate, regime, and oscillator states.

Edit this worksheet in place, build with `lake build HCP.Worksheets.L5_Damping`,
and compare with the solution at `HCP/L5_Damping.lean`.
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

namespace HCP.Worksheets.L5_Damping

-- EXERCISE: damped_rig_and_parts
-- GIVEN:
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

-- TODO: place mass on the rig and stiffness on its spring bearer.
def massOf {o : Osc} (r : DampedRig o) :
    IndividualQuantity o massK ℝ := by
  sorry

def springConstantOf {o : Osc} (r : DampedRig o) :
    IndividualQuantity (springPart o) springConstantK ℝ := by
  sorry
-- EXERCISE_END: damped_rig_and_parts

-- EXERCISE: energy_dissipation
-- TODO: apply the oscillator's energy-dissipation result and show energy decreases.
lemma energy_dissipation_on_state {o : Osc} (r : DampedRig o)
    (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time)
    (h1 : r.osc.EquationOfMotion xₜ) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (r.osc.energy xₜ) t =
      - r.osc.γ * inner ℝ (∂ₜ xₜ t) (∂ₜ xₜ t) := by
  sorry

lemma energy_not_conserved_on_state {o : Osc} (r : DampedRig o)
    (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time)
    (h1 : r.osc.EquationOfMotion xₜ) (hx : ContDiff ℝ ∞ xₜ)
    (hdx : ∂ₜ xₜ t ≠ 0) (hγ : 0 < r.osc.γ) :
    ∂ₜ (r.osc.energy xₜ) t < 0 := by
  sorry
-- EXERCISE_END: energy_dissipation

-- EXERCISE: kinds_and_decay_rate
-- TODO: define the damping kinds, use the kind division law, and index the result by one rig.
def viscousDampingConstantK : KindOfProperty :=
  { id := "viscous damping constant", scale := .ratio }

def dampingCoefficientK : KindOfProperty :=
  Iso80000.Part3.dampingCoefficient.kind

def dampingConstantOf {o : Osc} (r : DampedRig o) :
    IndividualQuantity o viscousDampingConstantK ℝ := by
  sorry

instance : KindDiv viscousDampingConstantK massK dampingCoefficientK := by
  sorry

def decayRateOf {o : Osc} (r : DampedRig o) :
    IndividualQuantity o dampingCoefficientK ℝ := by
  sorry

lemma decayRateOf_magnitude {o : Osc} (r : DampedRig o) :
    (decayRateOf r).magnitude = r.osc.decayRate := by
  sorry

def angularFrequencyOf {o : Osc} (r : DampedRig o) :
    IndividualQuantity o angularFrequencyK ℝ := by
  sorry

lemma angularFrequencyOf_magnitude {o : Osc} (r : DampedRig o) :
    (angularFrequencyOf r).magnitude = r.osc.ω := by
  sorry

-- Kind vs dimension: Bare reals let Lean compare oscillator A's γ (kg/s) with ω (s⁻¹), despite their different dimensions; this is not the δ < ω regime test.
example (r : DampedRig .A) : Prop := r.osc.γ < r.osc.ω

-- Kind vs dimension: Proves that oscillator A's indexed decay-rate magnitude equals PhysLib's decayRate.
example (r : DampedRig .A) :
    (decayRateOf r).magnitude = r.osc.decayRate := by
  sorry

-- Dissipation: Proves that PhysLib's law for oscillator A is γ = 2m·decayRate, relating damper reading, body mass, and decay rate.
example (r : DampedRig .A) :
    r.osc.γ = 2 * r.osc.m * r.osc.decayRate := by
  sorry

-- TODO: uncomment the cross-rig division and explain the bearer mismatch.
-- Bearer safety: Refused: type mismatch between oscillator B's mass bearer and oscillator A's quotient bearer; this prevents computing A's decay rate with B's mass.
-- example (a : DampedRig .A) (b : DampedRig .B) :=
--   IndividualQuantity.div
--     (KindDiv.law (k₁ := viscousDampingConstantK) (k₂ := massK)
--       (k := dampingCoefficientK))
--     (dampingConstantOf a) (massOf b)
-- EXERCISE_END: kinds_and_decay_rate

-- EXERCISE: same_dimension_different_kinds
-- TODO: prove equal dimensions but distinct kinds; explain the raw-real comparison.
-- Kind vs dimension: Proves that damping coefficient δ and angular frequency ω both have dimension T⁻¹; matching dimensions alone do not license mixing them.
example :
    Iso80000.Part3.dampingCoefficient.dim =
      Iso80000.Part3.angularFrequency.dim := by
  sorry

-- Kind vs dimension: Proves that dampingCoefficientK and angularFrequencyK are distinct kinds despite their shared T⁻¹ dimension.
example : dampingCoefficientK ≠ angularFrequencyK := by
  sorry

-- TODO: explain why this dimensionally invalid comparison still type-checks as reals.
-- Kind vs dimension: Bare reals accept oscillator A's δ + ω as a real although the decay-rate and angular-frequency kinds differ; no sum kind is recorded.
example (r : DampedRig .A) : ℝ :=
  r.osc.decayRate + r.osc.ω

-- TODO: uncomment the kinded sum and read why the two kinds cannot be added.
-- Kind vs dimension: Refused: type mismatch between dampingCoefficientK and angularFrequencyK quantities; this prevents summing δ and ω despite their shared T⁻¹ dimension.
-- example (r : DampedRig .A) :=
--   Quantity.add DifferenceKind.ofScale
--     (decayRateOf r).toQuantity (angularFrequencyOf r).toQuantity
-- EXERCISE_END: same_dimension_different_kinds

-- EXERCISE: underdamped_regime
-- TODO: relate underdamping to the decay-rate inequality using the kinded magnitudes.
-- Regime: Proves that oscillator A is underdamped exactly when its numerical decay rate δ is below ω.
example (r : DampedRig .A) :
    r.osc.IsUnderdamped ↔ r.osc.decayRate < r.osc.ω := by
  sorry

-- TODO: uncomment the direct kinded comparison and inspect the type error.
-- Regime: Refused: type mismatch between angularFrequencyK and dampingCoefficientK; direct comparison erases the magnitude conversion and assumes rad = 1.
-- example (r : DampedRig .A) :=
--   (decayRateOf r).toQuantity < (angularFrequencyOf r).toQuantity

lemma underdamped_magnitude_test {o : Osc} (r : DampedRig o)
    (h : r.osc.IsUnderdamped) :
    (decayRateOf r).magnitude < (angularFrequencyOf r).magnitude := by
  sorry
-- EXERCISE_END: underdamped_regime

-- EXERCISE: same_oscillator_states
-- TODO: subtract two decay-rate records for oscillator A and prove the magnitude equation.
def decayRateChange (earlier later : DampedRig .A) :
    IndividualQuantity Osc.A dampingCoefficientK ℝ := by
  sorry

lemma decayRateChange_magnitude (earlier later : DampedRig .A) :
    (decayRateChange earlier later).magnitude =
      later.osc.decayRate - earlier.osc.decayRate := by
  sorry

-- TODO: uncomment the cross-oscillator addition and explain the bearer mismatch.
-- Bearer safety: Refused: type mismatch between oscillator A's and oscillator B's damping-coefficient bearers; this prevents subtracting one oscillator's decay rate from the other's.
-- example (a : DampedRig .A) (b : DampedRig .B) :=
--   IndividualQuantity.add DifferenceKind.ofScale
--     (decayRateOf a) (-(decayRateOf b))
-- EXERCISE_END: same_oscillator_states

end HCP.Worksheets.L5_Damping

end
