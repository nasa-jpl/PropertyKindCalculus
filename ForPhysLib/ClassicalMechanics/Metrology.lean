/-
# Stage 1 — the metrology annex of `Physlib/ClassicalMechanics` (two subtrees)

The second rung of [the adoption ladder](../PLAN.md#stage-1-the-metrology-annex), for
the campaign's third directory: each Stage-0 kind paired with its PhysLib `Dimension`
as a `DimensionedKind` — the lookups by *referencing the catalogue's own entries*, the
mints alone as constructed records — the directory's kind algebra authored as laws, and
`#kind_dimensional_coverage` pinned over it with `#guard_msgs` — at **zero cost to
existing code**: nothing in PhysLib changes, or even imports this.

**And the lookup is definitional.** Stage 0's kinds *are* the catalogue entries'
own projections; this module records the identification kind by kind (`rfl` — there
is no second spelling to drift) and checks each pairing's dimension against the
catalogue's.

**The registry now shows the collisions — this directory's whole point.** Six pairings
at the joule (kinetic, potential, mechanical, the Lagrangian, König's two species),
two at `T⁻¹` (the two ω's), two at `T` (duration and period): ten of the
twenty-two rows collide with another row. Upstream, every one of the ten is `ℝ`.

**The laws are the two subtrees' own equations.** Fourteen edges, each one a formula
the directory's physics writes: Hooke's `F = −k·x`; the radicand `ω² = k/m`; the
canonical momentum in both directions (`m·v` and `p/m`); Newton's `m·a`; the Legendre
`⟪p, v⟫`; the trig boundary's `ω·t`; the trajectory's `v₀/ω` and the amplitude–phase
`A·ω`; the period's `2π/ω` (the `2π` a full turn of phase); the rigid body's `I·ω`
and `ω·L`; the decomposition's `ω × r`; and conservation's `∂ₜE`.
-/

module

public import ForPhysLib.ClassicalMechanics.Kinds
public import PropertyKindCalculus.Dimension
public import PropertyKindCalculus.DimensionalCoverage
public import PropertyKindCalculus.Iso80000.Part3
public import PropertyKindCalculus.Iso80000.Part4

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace ForPhysLib.ClassicalMechanics.Metrology

open PropertyKindCalculus ForPhysLib.ClassicalMechanics.Kinds

/-! ## The pairings -/

/-- Mass is `M`. -/
def massDK : DimensionedKind := Iso80000.Part4.mass
/-- Momentum is `M·L·T⁻¹`. -/
def momentumDK : DimensionedKind := Iso80000.Part4.momentum
/-- Force is `M·L·T⁻²`. -/
def forceDK : DimensionedKind := Iso80000.Part4.force
/-- Potential energy is `M·L²·T⁻²` — the joule. -/
def potentialEnergyDK : DimensionedKind := Iso80000.Part4.potentialEnergy
/-- Kinetic energy is the *same* joule — the first collision. -/
def kineticEnergyDK : DimensionedKind := Iso80000.Part4.kineticEnergy
/-- Mechanical energy — the same joule again. -/
def mechanicalEnergyDK : DimensionedKind := Iso80000.Part4.mechanicalEnergy
/-- The Lagrangian — the same joule, fourth kind. -/
def lagrangianDK : DimensionedKind :=
  { kind := lagrangian, dim := Iso80000.Part4.MDim.energy }
/-- Translational kinetic energy — the same joule, fifth kind. -/
def translationalKineticEnergyDK : DimensionedKind :=
  { kind := translationalKineticEnergy, dim := Iso80000.Part4.MDim.energy }
/-- Rotational kinetic energy — the same joule, sixth kind: the registry's largest
collision family. -/
def rotationalKineticEnergyDK : DimensionedKind :=
  { kind := rotationalKineticEnergy, dim := Iso80000.Part4.MDim.energy }
/-- Power is `M·L²·T⁻³`. -/
def powerDK : DimensionedKind := Iso80000.Part4.power
/-- The moment of inertia is `M·L²`. -/
def momentOfInertiaDK : DimensionedKind := Iso80000.Part4.momentOfInertia
/-- Angular momentum is `M·L²·T⁻¹`. -/
def angularMomentumDK : DimensionedKind := Iso80000.Part4.angularMomentum
/-- Displacement is `L`. -/
def displacementDK : DimensionedKind := Iso80000.Part3.displacement
/-- Velocity is `L·T⁻¹`. -/
def velocityDK : DimensionedKind := Iso80000.Part3.velocity
/-- Acceleration is `L·T⁻²`. -/
def accelerationDK : DimensionedKind := Iso80000.Part3.acceleration
/-- Angular velocity is `T⁻¹` — the rigid body's `ω`. -/
def angularVelocityDK : DimensionedKind := Iso80000.Part3.angularVelocity
/-- Angular frequency is the *same* `T⁻¹` — the oscillator's `ω`: the shared-letter
collision, visible as a repeated dimension. -/
def angularFrequencyDK : DimensionedKind := Iso80000.Part3.angularFrequency
/-- Period duration is `T`. -/
def periodDurationDK : DimensionedKind := Iso80000.Part3.periodDuration
/-- Duration is the *same* `T` — the repetition interval is not the trajectory
parameter. -/
def durationDK : DimensionedKind := Iso80000.Part3.duration
/-- The phase angle is dimensionless — the trig boundary's licence. -/
def phaseAngleDK : DimensionedKind := Iso80000.Part3.phaseAngle
/-- The spring constant is `M·T⁻²` — the mint's dimension, certified below as force
per displacement. -/
def springConstantDK : DimensionedKind :=
  { kind := springConstant, dim := Dim.mass / (Dim.time * Dim.time) }
/-- The squared angular frequency is `T⁻²` — the radicand's dimension. -/
def squaredAngularFrequencyDK : DimensionedKind :=
  { kind := squaredAngularFrequency, dim := (Dim.time * Dim.time)⁻¹ }

/-! ## The lookup, definitional

Stage 0's vocabulary *is* `Iso80000` Parts 3 and 4's — each lookup kind is the
catalogue entry's own projection, so the identification is `rfl` and drift is
impossible by construction. The five mints have no catalogue row — that they *cannot*
be looked up is their finding — but their dimensions are checked against the
catalogue's below. -/

example : mass = Iso80000.Part4.mass.kind := rfl
example : momentum = Iso80000.Part4.momentum.kind := rfl
example : force = Iso80000.Part4.force.kind := rfl
example : potentialEnergy = Iso80000.Part4.potentialEnergy.kind := rfl
example : kineticEnergy = Iso80000.Part4.kineticEnergy.kind := rfl
example : mechanicalEnergy = Iso80000.Part4.mechanicalEnergy.kind := rfl
example : power = Iso80000.Part4.power.kind := rfl
example : momentOfInertia = Iso80000.Part4.momentOfInertia.kind := rfl
example : angularMomentum = Iso80000.Part4.angularMomentum.kind := rfl
example : displacement = Iso80000.Part3.displacement.kind := rfl
example : velocity = Iso80000.Part3.velocity.kind := rfl
example : acceleration = Iso80000.Part3.acceleration.kind := rfl
example : angularVelocity = Iso80000.Part3.angularVelocity.kind := rfl
example : angularFrequency = Iso80000.Part3.angularFrequency.kind := rfl
example : periodDuration = Iso80000.Part3.periodDuration.kind := rfl
example : phaseAngle = Iso80000.Part3.phaseAngle.kind := rfl
example : duration = Iso80000.Part3.duration.kind := rfl

example : massDK.dim = Iso80000.Part4.mass.dim := rfl
example : momentumDK.dim = Iso80000.Part4.momentum.dim := rfl
example : forceDK.dim = Iso80000.Part4.force.dim := rfl
example : potentialEnergyDK.dim = Iso80000.Part4.potentialEnergy.dim := rfl
example : kineticEnergyDK.dim = Iso80000.Part4.kineticEnergy.dim := rfl
example : mechanicalEnergyDK.dim = Iso80000.Part4.mechanicalEnergy.dim := rfl
example : powerDK.dim = Iso80000.Part4.power.dim := rfl
example : momentOfInertiaDK.dim = Iso80000.Part4.momentOfInertia.dim := rfl
example : angularMomentumDK.dim = Iso80000.Part4.angularMomentum.dim := rfl
example : displacementDK.dim = Iso80000.Part3.displacement.dim := rfl
example : velocityDK.dim = Iso80000.Part3.velocity.dim := rfl
example : accelerationDK.dim = Iso80000.Part3.acceleration.dim := rfl
example : angularVelocityDK.dim = Iso80000.Part3.angularVelocity.dim := rfl
example : angularFrequencyDK.dim = Iso80000.Part3.angularFrequency.dim := rfl
example : periodDurationDK.dim = Iso80000.Part3.periodDuration.dim := rfl
example : phaseAngleDK.dim = Iso80000.Part3.phaseAngle.dim := rfl
example : durationDK.dim = Iso80000.Part3.duration.dim := rfl

/- The mints' dimensions, checked against the catalogue's arithmetic. The four
joule-mints share the catalogue's energy — the six-way collision is a checked fact,
not a slogan. -/
example : lagrangianDK.dim = Iso80000.Part4.mechanicalEnergy.dim := rfl
example : translationalKineticEnergyDK.dim = Iso80000.Part4.kineticEnergy.dim := rfl
example : rotationalKineticEnergyDK.dim = Iso80000.Part4.kineticEnergy.dim := rfl
/- The spring constant is force per displacement — Hooke's law fixes the mint. -/
example : springConstantDK.dim = Iso80000.Part4.MDim.force / Dim.length := by decide
/- The radicand's `T⁻²` is the catalogue's angular acceleration dimension — a
*different kind* at that dimension (3-13 measures a rotation's rate change, the
radicand a stiffness-to-inertia ratio). -/
example : squaredAngularFrequencyDK.dim = Iso80000.Part3.angularAcceleration.dim := by
  decide

/-! ## The directory's kind algebra, and its dimensional audit

Fourteen authored edges — the equations the two subtrees actually write.
`#kind_dimensional_coverage` then walks every authored edge and checks it in PhysLib's
dimension group. -/

/-- `F = −k·x` — Hooke's law (`force_eq_linear`): the spring constant's defining
edge, and the certificate that fixes the mint's dimension. -/
theorem springConstant_mul_displacement :
    ProductKind springConstant displacement force :=
  ProductKind.ofRatio _ _ _

/-- `ω² = k/m` — the radicand (`ω_sq`): the input data's only route to the
oscillator's clock, and the edge the root crossing stands on. -/
theorem springConstant_div_mass :
    QuotientKind springConstant mass squaredAngularFrequency :=
  QuotientKind.ofRatio _ _ _

/-- `p = m·v` — the canonical momentum (`toCanonicalMomentum_eq`): the 4-8 edge, the
kind-*changing* map upstream types as `E ≃ₗ E`. -/
theorem mass_mul_velocity : ProductKind mass velocity momentum :=
  ProductKind.ofRatio _ _ _

/-- `v = p/m` — the inverse direction, which the source also writes
(`toCanonicalMomentum.symm` is `(1/m) • p`). -/
theorem momentum_div_mass : QuotientKind momentum mass velocity :=
  QuotientKind.ofRatio _ _ _

/-- `m·a = F` — Newton's second law, the tfae's second formulation. -/
theorem mass_mul_acceleration : ProductKind mass acceleration force :=
  ProductKind.ofRatio _ _ _

/-- `⟪p, v⟫` — the Legendre transform's pairing (`hamiltonian`'s first term): a
momentum times a velocity lands at the kinetic kind (`⟪p,v⟫ = 2T`; the `½` rides the
numeral action). -/
theorem momentum_mul_velocity : ProductKind momentum velocity kineticEnergy :=
  ProductKind.ofRatio _ _ _

/-- `ω·t` — the trig boundary (`cos (S.ω * t)` throughout `Solution.lean`): an
angular frequency times a duration is a phase angle, and only the phase reaches
`cos`/`sin`. -/
theorem angularFrequency_mul_duration :
    ProductKind angularFrequency duration phaseAngle :=
  ProductKind.ofRatio _ _ _

/-- `v₀/ω` — the trajectory's own second term (`(sin (ω t)/ω) • v₀`) and the
amplitude–phase embedding's imaginary part: a velocity per angular frequency is a
displacement. -/
theorem velocity_div_angularFrequency :
    QuotientKind velocity angularFrequency displacement :=
  QuotientKind.ofRatio _ _ _

/-- `A·ω` — the amplitude–phase velocity (`v₀ = A ω sin φ`): the same edge run the
other way. -/
theorem angularFrequency_mul_displacement :
    ProductKind angularFrequency displacement velocity :=
  ProductKind.ofRatio _ _ _

/-- `T = 2π/ω` — the period (`period`): a *phase angle* (the full turn `2π`) per
angular frequency is a period duration. The numerator's kind is why the numeral `2π`
is not dimensionless noise. -/
theorem phaseAngle_div_angularFrequency :
    QuotientKind phaseAngle angularFrequency periodDuration :=
  QuotientKind.ofRatio _ _ _

/-- `L = I·ω` — the rigid body's angular momentum
(`angularMomentum_eq_inertiaTensor_mulVec`): the 4-7 × 3-12 edge. -/
theorem momentOfInertia_mul_angularVelocity :
    ProductKind momentOfInertia angularVelocity angularMomentum :=
  ProductKind.ofRatio _ _ _

/-- `T_rot = ½ ω·L` — the rotational kinetic energy
(`rotationalKineticEnergy_eq_angularMomentum`): the contraction lands at König's
rotational species. -/
theorem angularVelocity_mul_angularMomentum :
    ProductKind angularVelocity angularMomentum rotationalKineticEnergy :=
  ProductKind.ofRatio _ _ _

/-- `ω × r` — the Landau–Lifshitz velocity decomposition's rotational term
(`velocity_eq_angularVelocity`): an angular velocity times a displacement from the
centre of mass is a velocity. Grown at Stage-2 time for the rigid body's
decomposition — the pilot's stage-growth pattern. -/
theorem angularVelocity_mul_displacement :
    ProductKind angularVelocity displacement velocity :=
  ProductKind.ofRatio _ _ _

/-- `∂ₜE` — what energy conservation says vanishes
(`energy_conservation_of_equationOfMotion`): a mechanical energy per duration is a
power. -/
theorem mechanicalEnergy_div_duration :
    QuotientKind mechanicalEnergy duration power :=
  QuotientKind.ofRatio _ _ _

/--
info: dimensional coverage:
[coherent] angularFrequency · displacement → velocity
[coherent] angularFrequency · duration → phaseAngle
[coherent] angularVelocity · angularMomentum → rotationalKineticEnergy
[coherent] angularVelocity · displacement → velocity
[coherent] mass · acceleration → force
[coherent] mass · velocity → momentum
[coherent] mechanicalEnergy / duration → power
[coherent] momentOfInertia · angularVelocity → angularMomentum
[coherent] momentum / mass → velocity
[coherent] momentum · velocity → kineticEnergy
[coherent] phaseAngle / angularFrequency → periodDuration
[coherent] springConstant / mass → squaredAngularFrequency
[coherent] springConstant · displacement → force
[coherent] velocity / angularFrequency → displacement
14 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage ForPhysLib.ClassicalMechanics.Metrology

end ForPhysLib.ClassicalMechanics.Metrology

end -- pkc-blanket-expose
end -- pkc-blanket
