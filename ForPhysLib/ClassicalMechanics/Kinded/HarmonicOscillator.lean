/-
# Stage 2 — kinded re-authoring of `Physlib/ClassicalMechanics/HarmonicOscillator`

The third rung of [the adoption ladder](../../PLAN.md#stage-2-kinded-re-authoring-with-definitional-erasure)
for the campaign's third directory, oscillator half. Every quantity at its kind, the
naked form recovered definitionally or by upstream's own lemma.

**The re-authoring follows the subtree's own derivation order.**

* **The kinetic energy through the Legendre edge.** `½⟪p, v⟫` — one numeral, two table
  products (`m·v → p`, `p·v → 2T`) — erases to upstream's `½m⟪ẋ,ẋ⟫` by the inner
  product's component expansion: the MR11 answer at PhysLib's own oscillator, measured
  against the case study's reconstruction.
* **The pentad — the stress test.** The five formulations of the equation of motion,
  re-stated with their kinded readings — Newton's `m·a` through the table, Hamilton's
  momentum trajectory through the kinded canonical momentum, both variational
  integrands *being* the Lagrangian mint and the kinded Hamiltonian — and the whole
  `List.TFAE` closed by `equationOfMotion_tfae` **verbatim**: the upstream proof term
  is the proof, because every kinded spelling erases definitionally.
* **The trajectory from its data.** `cos(ω·t)·x₀ + sin(ω·t)·(v₀/ω)` — the phase
  through the trig-boundary edge, the second summand through the `v/ω` edge, the sum
  same-kind — erasing to upstream's `trajectory`. The normal form (`A·cos(ω·t − φ)`)
  and the periodicity (`x(t + T) = x(t)`, the period through the `2π/ω` crossing) are
  consumed at the same reading.
* **Conservation as a kind statement.** `∂ₜE` is read at the *power* kind (the
  Stage-1 edge), and the conservation theorem says the reading vanishes on shell; the
  constant on-shell energy value is consumed at the join.
* **The geometric subtree, at one reading.** The mass Riemannian metric is `2T` in
  disguise: `geometricKineticEnergy` ingests at the kinetic kind and upstream's own
  coordinate formula is the erasure — the manifold plumbing (charts, tangent
  coordinates) is carrier structure the kind layer rides unchanged.
-/

import ForPhysLib.ClassicalMechanics.Feasibility
import ForPhysLib.ClassicalMechanics.Metrology
import Physlib.ClassicalMechanics.HarmonicOscillator.Geometric.KineticEnergy

namespace ForPhysLib.ClassicalMechanics.Kinded

open PropertyKindCalculus
open ForPhysLib.ClassicalMechanics
open Time ContDiff InnerProductSpace
open scoped Manifold
open scoped PropertyKindCalculus.OperatorTable

local notation "HO" => _root_.ClassicalMechanics.HarmonicOscillator
local notation "E1" => EuclideanSpace ℝ (Fin 1)

noncomputable section

/-! ## One vocabulary

`Feasibility.lean`'s probe kinds and Stage 0's literals are the *same* kinds,
definitionally — the probes looked them up from the catalogue (or minted locally),
Stage 0 copied the literals, and both routes land on one structure. Stated once, so
everything below freely composes Feasibility's quantities with the Stage-0/Stage-1
vocabulary. -/

example : massK = Kinds.mass := rfl
example : momentumK = Kinds.momentum := rfl
example : forceK = Kinds.force := rfl
example : kineticEnergyK = Kinds.kineticEnergy := rfl
example : potentialEnergyK = Kinds.potentialEnergy := rfl
example : mechanicalEnergyK = Kinds.mechanicalEnergy := rfl
example : momentOfInertiaK = Kinds.momentOfInertia := rfl
example : angularMomentumK = Kinds.angularMomentum := rfl
example : displacementK = Kinds.displacement := rfl
example : velocityK = Kinds.velocity := rfl
example : accelerationK = Kinds.acceleration := rfl
example : angularFrequencyK = Kinds.angularFrequency := rfl
example : angularVelocityK = Kinds.angularVelocity := rfl
example : periodDurationK = Kinds.periodDuration := rfl
example : phaseAngleK = Kinds.phaseAngle := rfl
example : durationK = Kinds.duration := rfl
example : springConstantK = Kinds.springConstant := rfl
example : omegaSquaredK = Kinds.squaredAngularFrequency := rfl
example : lagrangianK = Kinds.lagrangian := rfl
example : translationalKineticEnergyK = Kinds.translationalKineticEnergy := rfl
example : rotationalKineticEnergyK = Kinds.rotationalKineticEnergy := rfl

/-! ## The kinetic energy through the Legendre edge -/

/-- A pointwise velocity reading along the trajectory. -/
@[kindIngest]
def velocityAtQ (xₜ : Time → E1) (t : Time) : Quantity velocityK ℝ :=
  .attest "the trajectory's time derivative, component 0" (∂ₜ xₜ t 0)

@[simp] theorem velocityAtQ_magnitude (xₜ : Time → E1) (t : Time) :
    (velocityAtQ xₜ t).magnitude = ∂ₜ xₜ t 0 := rfl

/-- `½⟪p, v⟫` — the kinetic energy authored through the table: `m·v → p` (4-8), then
`p·v → 2T` (the Legendre pairing), the `½` on the numeral action. -/
def kineticFromTableQ (mq : Quantity massK ℝ) (vq : Quantity velocityK ℝ) :
    Quantity kineticEnergyK ℝ :=
  (1 / 2 : ℝ) •
    (Quantity.mul Metrology.momentum_mul_velocity (mq * vq : Quantity momentumK ℝ) vq :
      Quantity kineticEnergyK ℝ)

/-- **The MR11 erasure**: the table-built kinetic energy *is* upstream's
`½m⟪ẋ,ẋ⟫` — the inner product's one-component expansion is the whole proof. -/
theorem kineticFromTableQ_erases (S : HO) (xₜ : Time → E1) (t : Time) :
    (kineticFromTableQ (massQ S) (velocityAtQ xₜ t)).magnitude =
      S.kineticEnergy xₜ t := by
  show 1 / 2 * (S.m * (∂ₜ xₜ t 0) * (∂ₜ xₜ t 0)) =
    (1 / (2 : ℝ)) * S.m * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ
  rw [show (⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ) = ∂ₜ xₜ t 0 * ∂ₜ xₜ t 0 by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_one]]
  ring

/-! ## The pentad — the stress test

The five formulations of the equation of motion, each re-stated with its kinded
reading, the whole equivalence closed by `equationOfMotion_tfae` *verbatim*. Newton's
side is Feasibility's (`equationOfMotion_iff_kinded_newton`); the remaining readings
are authored here. -/

/-- The configuration, read whole at its kind (MR19 — the wrap is of the vector;
components stay plain indexing beneath it). -/
@[kindIngest]
def displacementE1Q (xₜ : Time → E1) (t : Time) : Quantity displacementK E1 :=
  .attest "the configuration, read whole" (xₜ t)

/-- The velocity, read whole at its kind. -/
@[kindIngest]
def velocityE1Q (xₜ : Time → E1) (t : Time) : Quantity velocityK E1 :=
  .attest "the velocity, read whole" (∂ₜ xₜ t)

/-- **Hamilton's formulation, kinded**: the momentum trajectory is built through the
kinded canonical momentum — the kind-changing map — and the equivalence is
`equationOfMotion_tfae` consumed at positions 0 and 2, nothing re-proved. -/
theorem equationOfMotion_iff_kinded_hamilton (S : HO) (xₜ : Time → E1)
    (hx : ContDiff ℝ ∞ xₜ) :
    S.EquationOfMotion xₜ ↔
      S.hamiltonEqOp
        (fun t =>
          (toCanonicalMomentumQ S t (displacementE1Q xₜ t) (velocityE1Q xₜ t)).magnitude)
        xₜ = 0 :=
  (S.equationOfMotion_tfae xₜ hx).out 0 2

/-- The action's integrand *is* the Lagrangian mint — definitionally: upstream's
`lagrangian S t (q' t) (fderiv ℝ q' t 1)` and the kinded `T − V` crossing erase to
the same real. -/
theorem action_integrand_is_the_mint (S : HO) (q' : Time → E1) (t : Time) :
    S.lagrangian t (q' t) (fderiv ℝ q' t 1) =
      (lagrangianQ (kineticQ S q' t) (potentialQ S (q' t))).magnitude := rfl

/-- The Hamilton action's integrand carries the kinded Hamiltonian — definitionally. -/
theorem hamilton_integrand_is_the_kinded_reading (S : HO) (t : Time) (p x : E1) :
    S.hamiltonian t p x =
      (hamiltonianQ S t (.attest "the phase-space momentum" p)
        (.attest "the phase-space displacement" x)).magnitude := rfl

/-- **The pentad, kinded — and the upstream proof term is the proof.** All five
formulations with their kinded spellings: Newton through the `m·a` table product,
Hamilton through the kinded canonical momentum, the action's integrand the Lagrangian
mint, the Hamilton action's integrand the kinded Hamiltonian. Every spelling erases
definitionally, so `equationOfMotion_tfae` closes the list *verbatim* — the
verbatim-survival stress test, passed at the strongest possible grade. -/
theorem equationOfMotion_pentad (S : HO) (xₜ : Time → E1) (hx : ContDiff ℝ ∞ xₜ) :
    List.TFAE [
      S.EquationOfMotion xₜ,
      ∀ t, S.m • ∂ₜ (∂ₜ xₜ) t = S.force (xₜ t),
      S.hamiltonEqOp
        (fun t =>
          (toCanonicalMomentumQ S t (displacementE1Q xₜ t) (velocityE1Q xₜ t)).magnitude)
        xₜ = 0,
      (δ (q':=xₜ), ∫ t,
        (lagrangianQ (kineticQ S q' t) (potentialQ S (q' t))).magnitude) = 0,
      (δ (pq' := fun t =>
          ((toCanonicalMomentumQ S t (displacementE1Q xₜ t) (velocityE1Q xₜ t)).magnitude,
            xₜ t)), ∫ t,
        ⟪(pq' t).1, ∂ₜ (Prod.snd ∘ pq') t⟫_ℝ -
          (hamiltonianQ S t (.attest "the phase-space momentum" (pq' t).1)
            (.attest "the phase-space displacement" (pq' t).2)).magnitude) = 0] :=
  S.equationOfMotion_tfae xₜ hx

/-! ## The trajectory from its data -/

/-- The trajectory, authored from its initial data: the phase through the
trig-boundary edge, `v₀/ω` through the velocity/angular-frequency edge, the numerals
`cos`/`sin` on the numeral action, the sum same-kind. -/
def trajectoryFromDataQ (S : HO)
    (IC : _root_.ClassicalMechanics.HarmonicOscillator.InitialConditions) (t : Time) :
    Quantity displacementK ℝ :=
  Real.cos ((phaseQ (omegaQ (omegaSqQ S)) (durationQ t)).magnitude) • displacement0Q IC
    + Real.sin ((phaseQ (omegaQ (omegaSqQ S)) (durationQ t)).magnitude) •
        (velocity0Q IC / omegaQ (omegaSqQ S))

/-- **The erasure**: the authored trajectory is upstream's, at component 0. -/
theorem trajectoryFromDataQ_erases (S : HO)
    (IC : _root_.ClassicalMechanics.HarmonicOscillator.InitialConditions) (t : Time) :
    (trajectoryFromDataQ S IC t).magnitude = IC.trajectory S t 0 := by
  show Real.cos (S.ω * t.val) * IC.x₀ 0
      + Real.sin (S.ω * t.val) * (IC.v₀ 0 / S.ω) =
    (Real.cos (S.ω * t) • IC.x₀ + (Real.sin (S.ω * t) / S.ω) • IC.v₀) 0
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The phase offset, read off the polar pair — `arg z`, at the phase-angle kind. -/
@[kindIngest]
def phaseOffsetQ (S : HO)
    (IC : _root_.ClassicalMechanics.HarmonicOscillator.InitialConditions) :
    Quantity phaseAngleK ℝ :=
  .attest "arg z — the phase read from the polar pair"
    ((_root_.ClassicalMechanics.HarmonicOscillator.AmplitudePhase.fromInitialConditions
      S IC).φ)

/-- **The normal form, consumed at the kinded reading**: every trajectory is one
shifted cosine — the amplitude a displacement (Feasibility's crossing), the shift a
same-kind difference of phase angles, upstream's `trajectory_eq_cos` the proof. -/
theorem trajectoryFromDataQ_normal_form (S : HO)
    (IC : _root_.ClassicalMechanics.HarmonicOscillator.InitialConditions) (t : Time) :
    (trajectoryFromDataQ S IC t).magnitude =
      (amplitudeQ (displacement0Q IC)
          (velocity0Q IC / omegaQ (omegaSqQ S))).magnitude *
        Real.cos ((phaseQ (omegaQ (omegaSqQ S)) (durationQ t)).magnitude -
          (phaseOffsetQ S IC).magnitude) := by
  rw [trajectoryFromDataQ_erases]
  have h0 := congrArg (fun v : E1 => v 0) (IC.trajectory_eq_cos S t)
  simp at h0
  exact h0

/-- **Periodicity, consumed at the kinded reading**: the trajectory repeats after one
period — the shift entering through the `2π/ω` crossing, upstream's
`trajectory_periodic` the proof. -/
theorem trajectoryFromDataQ_periodic (S : HO)
    (IC : _root_.ClassicalMechanics.HarmonicOscillator.InitialConditions) (t : Time) :
    (trajectoryFromDataQ S IC
        (t + ((periodQ (omegaQ (omegaSqQ S))).magnitude : ℝ))).magnitude =
      (trajectoryFromDataQ S IC t).magnitude := by
  rw [trajectoryFromDataQ_erases, trajectoryFromDataQ_erases]
  exact congrArg (fun v : E1 => v 0)
    (_root_.ClassicalMechanics.HarmonicOscillator.trajectory_periodic S IC t)

/-! ## Conservation as a kind statement -/

/-- The energy's rate of change, read at the *power* kind — the Stage-1 edge
`mechanicalEnergy / duration → power` is what `∂ₜE` means. -/
@[kindIngest]
def energyRateQ (S : HO) (xₜ : Time → E1) (t : Time) : Quantity Kinds.power ℝ :=
  .attest "∂ₜE — conservation's reading, at the watt" (∂ₜ (S.energy xₜ) t)

/-- **Conservation**: on shell, the power reading vanishes — upstream's
`energy_conservation_of_equationOfMotion`, consumed at the kinded reading. -/
theorem energyRateQ_vanishes_on_shell (S : HO) (xₜ : Time → E1)
    (hx : ContDiff ℝ ∞ xₜ) (h : S.EquationOfMotion xₜ) (t : Time) :
    (energyRateQ S xₜ t).magnitude = 0 := by
  have h0 := congrFun (S.energy_conservation_of_equationOfMotion xₜ hx h) t
  simp at h0
  exact h0

/-- The on-shell energy value, consumed at the join: the `T + V` sum along any
solution trajectory is the constant `½(m‖v₀‖² + k‖x₀‖²)`. -/
theorem energyQ_on_trajectory (S : HO)
    (IC : _root_.ClassicalMechanics.HarmonicOscillator.InitialConditions) (t : Time) :
    (energyQ (kineticQ S (IC.trajectory S) t)
        (potentialQ S (IC.trajectory S t))).magnitude =
      1 / 2 * (S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2) := by
  have h := congrFun (IC.trajectory_energy S) t
  exact h

/-! ## The geometric subtree, at one reading -/

/-- The metric-induced kinetic energy, ingested at the kinetic kind: the mass
Riemannian metric is `2T` in disguise, and the manifold plumbing (the single chart,
the tangent coordinate) is carrier structure the kind layer rides unchanged. -/
@[kindIngest]
def geometricKineticEnergyQ (S : HO)
    (q : _root_.ClassicalMechanics.HarmonicOscillator.ConfigurationSpace)
    (v : TangentSpace 𝓘(ℝ, E1) q) : Quantity kineticEnergyK ℝ :=
  .attest "½·g_m(v,v) — the mass metric's kinetic energy"
    (_root_.ClassicalMechanics.HarmonicOscillator.geometricKineticEnergy S q v)

/-- **The coordinate erasure**: upstream's own formula recovers `½m⟪·,·⟫` in the
global tangent coordinate. -/
theorem geometricKineticEnergyQ_erases (S : HO)
    (q : _root_.ClassicalMechanics.HarmonicOscillator.ConfigurationSpace)
    (v : TangentSpace 𝓘(ℝ, E1) q) :
    (geometricKineticEnergyQ S q v).magnitude =
      (1 / 2 : ℝ) * S.m *
        ⟪_root_.ClassicalMechanics.HarmonicOscillator.tangentCoord q v,
          _root_.ClassicalMechanics.HarmonicOscillator.tangentCoord q v⟫_ℝ :=
  _root_.ClassicalMechanics.HarmonicOscillator.geometricKineticEnergy_massMetric_eq
    S q v

end

end ForPhysLib.ClassicalMechanics.Kinded
