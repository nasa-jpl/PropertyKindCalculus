/-
# L3 — The body opens up

Seven build-checked probes of composition, weighted means, and frame-specific rotation.

Edit this worksheet in place, build with `lake build HCP.Worksheets.L3_TheBodyOpens`,
and compare with the solution at `HCP/L3_TheBodyOpens.lean`.
-/

module

public import ForPhysLib.Exhibits.Composition.Findings
public import ForPhysLib.Exhibits.RigidBody.Findings
public import ForPhysLib.ClassicalMechanics.SolidSphereInertia
public import ForPhysLib.ClassicalMechanics.Feasibility

@[expose] public section

open PropertyKindCalculus
open ForPhysLib.Exhibits.Composition

noncomputable section

namespace HCP.Worksheets.L3_TheBodyOpens

-- EXERCISE: opened_body
-- GIVEN:
/--
One pair name is one system. Records under that name describe states, configurations, or
rival estimates of it; distinct names denote distinct systems.
-/
inductive PairId | P | Q
deriving DecidableEq, Repr

inductive Body | A | B
deriving DecidableEq, Repr

def halfS : SortOfSystem := ⟨"half of a rigid body"⟩

structure HalfOf (π : PairId) (b : Body) where
  half : Half
deriving DecidableEq, Repr

instance {π : PairId} {b : Body} : Sorted (HalfOf π b) :=
  ⟨fun _ => halfS⟩

instance {π : PairId} {b : Body} : Designated (HalfOf π b) where
  designation
    | ⟨.left⟩ => ⟨"left half"⟩
    | ⟨.right⟩ => ⟨"right half"⟩
  designation_inj {x y} h := by
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    cases x <;> cases y <;> first | rfl | exact absurd (System.mk.inj h) (by decide)

structure OpenBody (π : PairId) (b : Body) where
  mass : Half → ℝ
  position : Half → ℝ

def halfPart (π : PairId) (b : Body) (h : Half) : HalfOf π b := ⟨h⟩

def bodyHalves : Decomposition Half := .union (.atom .left) (.atom .right)

-- TODO: assemble the body's mass from its two half-bearers.
def massOf {π : PairId} {b : Body} (state : OpenBody π b) (h : HalfOf π b) :
    IndividualQuantity
      (Composite.part (σ := rigidBodyS) h)
      massK ℝ := by
  sorry

def bodyMass {π : PairId} {b : Body} (state : OpenBody π b) :
    IndividualQuantity
      (Composite.whole : Composite rigidBodyS (HalfOf π b))
      massK ℝ := by
  sorry

theorem bodyMass_magnitude {π : PairId} {b : Body} (state : OpenBody π b) :
    (bodyMass state).magnitude = state.mass .left + state.mass .right := by
  sorry

-- GIVEN:
-- Composition law: Proves that PhysLib's union-mass law is mass(A ∪ B) = mass(A) + mass(B), the additive law used for body A's halves.
example := ForPhysLib.Exhibits.Composition.union_mass
-- Composition law: Proves that PhysLib's union-inertia law is I(A ∪ B) = I(A) + I(B) about a common origin; the theorem's type does not record the axis.
example := ForPhysLib.Exhibits.Composition.union_inertiaTensor

-- TODO: type a mass difference for one half of the same body across two records.
-- Same-name records: Constructs a massK IndividualQuantity about body A's left half in pair P, allowing earlier and later states of that half to be compared.
example (earlier later : OpenBody .P .A) :
    IndividualQuantity
      (Composite.part (σ := rigidBodyS) (halfPart .P .A .left))
      massK ℝ := by
  sorry

-- TODO: uncomment the cross-pair expression and explain the bearer mismatch.
-- Bearer safety: Refused: type mismatch between body A's left-half mass bearers in pairs P and Q; this prevents treating distinct pairs as one state history.
-- example (p : OpenBody .P .A) (q : OpenBody .Q .A) :=
--   IndividualQuantity.add DifferenceKind.ofScale
--     (massOf p (halfPart .P .A .left))
--     (massOf q (halfPart .Q .A .left))
-- EXERCISE_END: opened_body

-- EXERCISE: center_of_mass_mean
-- GIVEN:
-- Centre of mass: Proves that with nonzero masses, (mA + mB)·COM(A ∪ B) = mA·COM(A) + mB·COM(B), PhysLib's weighted-mean law.
example := ForPhysLib.Exhibits.Composition.union_centerOfMass

-- TODO: construct the weighted carving and prove its mean is the mass-weighted position.
noncomputable def centerOfMassCarving {π : PairId} {b : Body}
    (state : OpenBody π b)
    (h : state.mass .left + state.mass .right ≠ 0) :
    WeightedCarving ℝ Half where
  parts := bodyHalves
  weight := state.mass
  total_ne_zero := by
    sorry

theorem centerOfMass_eq {π : PairId} {b : Body} (state : OpenBody π b)
    (h : state.mass .left + state.mass .right ≠ 0) :
    (centerOfMassCarving state h).mean state.position =
      (state.mass .left * state.position .left + state.mass .right * state.position .right) /
        (state.mass .left + state.mass .right) := by
  sorry

-- GIVEN:
def unequalMassExample : OpenBody .P .A where
  mass
    | .left => 3
    | .right => 5
  position
    | .left => 0
    | .right => 10

-- TODO: evaluate the weighted mean for the unequal-mass example.
theorem unequalMassExample_centerOfMass :
    (centerOfMassCarving unequalMassExample (by norm_num [unequalMassExample])).mean
      unequalMassExample.position = (25 : ℝ) / 4 := by
  sorry

def positionOf {π : PairId} {b : Body} (state : OpenBody π b) (h : HalfOf π b) :
    IndividualQuantity
      (Composite.part (σ := rigidBodyS) h)
      ForPhysLib.ClassicalMechanics.displacementK ℝ := by
  sorry

-- TODO: uncomment the attempted displacement assembly and explain why the license is absent.
-- Centre of mass: Refused: no Assembles rigidBodyS displacementK instance; the halves' positions form a mass-weighted mean, not an additive total.
-- example {π : PairId} {b : Body} (state : OpenBody π b) :=
--   assemble (k := ForPhysLib.ClassicalMechanics.displacementK) rigidBodyS
--     (Composite.whole : Composite rigidBodyS (HalfOf π b))
--     (fun h : Half => Composite.part (σ := rigidBodyS) (halfPart π b h))
--     bodyHalves
--     (fun h => positionOf state (halfPart π b h))
-- EXERCISE_END: center_of_mass_mean

-- EXERCISE: massless_center_of_mass
-- TODO: inspect why the massless-body result has no center of mass.
-- GIVEN:
-- Centre of mass: proves that a massless body's `centerOfMass` is the origin, because PhysLib computes (1 / mass) • … and Lean's 1 / 0 = 0.
example := ForPhysLib.Exhibits.Composition.massless_centerOfMass
-- Centre of mass: Proves that the two mass-weighted halves have total weight 2 ≠ 0, supplying the license for their weighted mean.
example := ForPhysLib.Exhibits.Composition.halvesByMass_total_ne_zero
-- EXERCISE_END: massless_center_of_mass

-- EXERCISE: angular_velocity_intensive
-- TODO: compare the intensive angular-velocity result with the rejected assembly.
-- GIVEN:
-- Composition law: Proves that angular velocity is intensive: each rigid-body half reads 7 rad/s rather than receiving a share of a total.
example := ForPhysLib.Exhibits.Composition.omegaOfHalf_intensive
-- Composition law: Proves that angular velocity is not extensive across the rigid body's halves: both read 7 rad/s, not a summed 14 rad/s.
example := ForPhysLib.Exhibits.Composition.omegaOfHalf_not_extensive

-- TODO: uncomment the generic angular-velocity assembly attempt and read the error.
-- Licensed composition: Refused: no Assembles rigidBodyS angularVelocityK instance; angular velocity is constant across parts, not an additive total.
-- example :=
--   fun {π : PairId} {b : Body}
--       (ω : (h : Half) →
--         IndividualQuantity
--           (Composite.part (σ := rigidBodyS) (halfPart π b h))
--           angularVelocityK ℝ) =>
--     assemble (k := angularVelocityK) rigidBodyS
--       (Composite.whole : Composite rigidBodyS (HalfOf π b))
--       (fun h : Half => Composite.part (σ := rigidBodyS) (halfPart π b h))
--       bodyHalves ω
-- EXERCISE_END: angular_velocity_intensive

-- EXERCISE: bare_frame_mismatch
-- TODO: explain why the bare vector accepts a frame-mismatched energy argument.
-- Frame safety: The bare ℝ example accepts rotational energy from M's body inertia and lab-frame ω; it erases frame and motion bearer, hiding the invalid mix.
noncomputable example (M : RigidBodyMotion 3) (t : Time) : ℝ :=
  M.toRigidBody.rotationalKineticEnergy (M.angularVelocity t)
-- EXERCISE_END: bare_frame_mismatch

-- EXERCISE: framed_rotational_energy
-- TODO: uncomment the lab-frame argument to see the frame mismatch, then use bodyOmega.
-- Frame safety: Refused: type mismatch between lab-frame ω and the body-frame ω required by contraction; this prevents pairing body inertia with lab angular velocity.
-- noncomputable example (M : RigidBodyMotion 3) (t : Time) :=
--   ForPhysLib.Exhibits.RigidBody.rotationalContraction
--     ForPhysLib.Exhibits.RigidBody.inertia_mul_angularVelocity
--     ForPhysLib.Exhibits.RigidBody.angularVelocity_mul_angularMomentum
--     (ForPhysLib.Exhibits.RigidBody.bodyInertia M)
--     (ForPhysLib.Exhibits.RigidBody.labOmega M t)

-- Frame safety: Constructs a bearer-free body-frame kineticEnergyK scalar from M's body-frame inertia and angular velocity; the result retains frame and kind, not M.
example (M : RigidBodyMotion 3) (t : Time) :
    InFrame ForPhysLib.Exhibits.RigidBody.body .scalar
      ForPhysLib.Exhibits.RigidBody.kineticEnergyK ℝ := by
  sorry

-- GIVEN:
-- Frame safety: Proves that body-frame rotational contraction equals PhysLib's rotational kinetic energy for the motion's body-frame angular velocity.
example := ForPhysLib.Exhibits.RigidBody.rotationalContraction_eq_physlib
-- EXERCISE_END: framed_rotational_energy

-- EXERCISE: solid_sphere
-- TODO: inspect the proved solid-sphere inertia result.
-- GIVEN:
-- Composition law: Proves that the 3D solid sphere's inertia tensor is (2/5) m R² times the identity matrix.
example := ForPhysLib.ClassicalMechanics.SolidSphereInertia.solidSphere_inertiaTensor
-- EXERCISE_END: solid_sphere

end HCP.Worksheets.L3_TheBodyOpens

end
