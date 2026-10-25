/-
# L3 — The body opens up

Solution for the worksheet HCP/Worksheets/L3_TheBodyOpens.lean.

Seven build-checked probes of composition, weighted means, and frame-specific rotation.
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

namespace HCP.L3_TheBodyOpens

-- ANCHOR: opened_body
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

def massOf {π : PairId} {b : Body} (state : OpenBody π b) (h : HalfOf π b) :
    IndividualQuantity
      (Composite.part (σ := rigidBodyS) h)
      massK ℝ :=
  ⟨state.mass h.half⟩

def bodyMass {π : PairId} {b : Body} (state : OpenBody π b) :
    IndividualQuantity
      (Composite.whole : Composite rigidBodyS (HalfOf π b))
      massK ℝ :=
  assemble (k := massK) rigidBodyS
    (Composite.whole : Composite rigidBodyS (HalfOf π b))
    (fun h : Half => Composite.part (σ := rigidBodyS) (halfPart π b h))
    bodyHalves
    (fun h => massOf state (halfPart π b h))

/-- The mass of a body is the sum of the masses of its left and right halves. -/
theorem bodyMass_magnitude {π : PairId} {b : Body} (state : OpenBody π b) :
    (bodyMass state).magnitude = state.mass .left + state.mass .right := by
  rfl

-- Lean type-checks the composition rule for combining body A's two halves into a mass.
example := ForPhysLib.Exhibits.Composition.union_mass

-- Lean type-checks the composition rule for combining body A's halves into an inertia tensor.
example := ForPhysLib.Exhibits.Composition.union_inertiaTensor

-- Lean type-checks a mass difference between two records of body A on pair P, for its left half.
#guard_msgs in
example (earlier later : OpenBody .P .A) :
    IndividualQuantity
      (Composite.part (σ := rigidBodyS) (halfPart .P .A .left))
      massK ℝ :=
  IndividualQuantity.add DifferenceKind.ofScale
    (massOf later (halfPart .P .A .left))
    (-(massOf earlier (halfPart .P .A .left)))

-- Refused: Lean reports a type mismatch between body A's left-half mass bearers in pair P and pair Q.
/--
error: Application type mismatch: The argument
  massOf q (halfPart PairId.Q Body.A Half.left)
has type
  IndividualQuantity (Composite.part (halfPart PairId.Q Body.A Half.left)) massK ℝ
but is expected to have type
  IndividualQuantity (Composite.part (halfPart PairId.P Body.A Half.left)) massK ℝ
in the application
  IndividualQuantity.add ⋯ (massOf p (halfPart PairId.P Body.A Half.left))
    (massOf q (halfPart PairId.Q Body.A Half.left))
-/
#guard_msgs in
example (p : OpenBody .P .A) (q : OpenBody .Q .A) :=
  IndividualQuantity.add DifferenceKind.ofScale
    (massOf p (halfPart .P .A .left))
    (massOf q (halfPart .Q .A .left))
-- ANCHOR_END: opened_body

-- ANCHOR: center_of_mass_mean
-- Lean type-checks the composition rule for the center of mass of body A from its two halves.
example := ForPhysLib.Exhibits.Composition.union_centerOfMass

noncomputable def centerOfMassCarving {π : PairId} {b : Body}
    (state : OpenBody π b)
    (h : state.mass .left + state.mass .right ≠ 0) :
    WeightedCarving ℝ Half where
  parts := bodyHalves
  weight := state.mass
  total_ne_zero := by
    change state.mass .left + state.mass .right ≠ 0
    exact h

/-- The center of mass of body A's two halves is their mass-weighted position mean. -/
theorem centerOfMass_eq {π : PairId} {b : Body} (state : OpenBody π b)
    (h : state.mass .left + state.mass .right ≠ 0) :
    (centerOfMassCarving state h).mean state.position =
      (state.mass .left * state.position .left + state.mass .right * state.position .right) /
        (state.mass .left + state.mass .right) := by
  rfl

def unequalMassExample : OpenBody .P .A where
  mass
    | .left => 3
    | .right => 5
  position
    | .left => 0
    | .right => 10

/-- The example body with half masses 3 and 5 has center of mass at 25/4. -/
theorem unequalMassExample_centerOfMass :
    (centerOfMassCarving unequalMassExample (by norm_num [unequalMassExample])).mean
      unequalMassExample.position = (25 : ℝ) / 4 := by
  norm_num [centerOfMassCarving, unequalMassExample, WeightedCarving.mean, weightedSum,
    totalWeight, bodyHalves, Decomposition.fold, Carrier.add]

def positionOf {π : PairId} {b : Body} (state : OpenBody π b) (h : HalfOf π b) :
    IndividualQuantity
      (Composite.part (σ := rigidBodyS) h)
      ForPhysLib.ClassicalMechanics.displacementK ℝ :=
  ⟨state.position h.half⟩

-- Refused: Lean fails to type-check whole-body displacement assembly because no `Assembles rigidBodyS displacementK` instance exists.
/--
error: failed to synthesize instance of type class
  Assembles rigidBodyS ForPhysLib.ClassicalMechanics.displacementK

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {π : PairId} {b : Body} (state : OpenBody π b) :=
  assemble (k := ForPhysLib.ClassicalMechanics.displacementK) rigidBodyS
    (Composite.whole : Composite rigidBodyS (HalfOf π b))
    (fun h : Half => Composite.part (σ := rigidBodyS) (halfPart π b h))
    bodyHalves
    (fun h => positionOf state (halfPart π b h))
-- ANCHOR_END: center_of_mass_mean

-- ANCHOR: massless_center_of_mass
-- Lean type-checks the massless-body result, for which a center of mass requires nonzero total mass.
example := ForPhysLib.Exhibits.Composition.massless_centerOfMass

-- Lean type-checks the result that mass-weighted halves have a nonzero total weight.
example := ForPhysLib.Exhibits.Composition.halvesByMass_total_ne_zero
-- ANCHOR_END: massless_center_of_mass

-- ANCHOR: angular_velocity_intensive
-- Lean type-checks angular velocity as an intensive property of each half of body A.
example := ForPhysLib.Exhibits.Composition.omegaOfHalf_intensive

-- Lean type-checks the result that angular velocity is not extensive across body A's halves.
example := ForPhysLib.Exhibits.Composition.omegaOfHalf_not_extensive

-- Refused: Lean fails to type-check angular-velocity assembly over body A's halves because no `Assembles rigidBodyS angularVelocityK` instance exists.
/--
error: failed to synthesize instance of type class
  Assembles rigidBodyS angularVelocityK

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example :=
  fun {π : PairId} {b : Body}
      (ω : (h : Half) →
        IndividualQuantity
          (Composite.part (σ := rigidBodyS) (halfPart π b h))
          angularVelocityK ℝ) =>
    assemble (k := angularVelocityK) rigidBodyS
      (Composite.whole : Composite rigidBodyS (HalfOf π b))
      (fun h : Half => Composite.part (σ := rigidBodyS) (halfPart π b h))
      bodyHalves ω
-- ANCHOR_END: angular_velocity_intensive

-- ANCHOR: bare_frame_mismatch
-- Lean type-checks bare-vector rotational energy without recording whether angular velocity is in the lab or body frame.
noncomputable example (M : RigidBodyMotion 3) (t : Time) : ℝ :=
  M.toRigidBody.rotationalKineticEnergy (M.angularVelocity t)
-- ANCHOR_END: bare_frame_mismatch

-- ANCHOR: framed_rotational_energy
-- Refused: Lean reports a type mismatch between the lab-frame angular velocity and the body-frame angular velocity required by rotational contraction.
/--
error: Application type mismatch: The argument
  ForPhysLib.Exhibits.RigidBody.labOmega M t
has type
  InFrame ForPhysLib.Exhibits.RigidBody.lab Variance.vector ForPhysLib.Exhibits.RigidBody.angularVelocityK (Fin 3 → ℝ)
but is expected to have type
  InFrame ForPhysLib.Exhibits.RigidBody.body Variance.vector ForPhysLib.Exhibits.RigidBody.angularVelocityK (Fin 3 → ℝ)
in the application
  ForPhysLib.Exhibits.RigidBody.rotationalContraction ForPhysLib.Exhibits.RigidBody.inertia_mul_angularVelocity
    ForPhysLib.Exhibits.RigidBody.angularVelocity_mul_angularMomentum (ForPhysLib.Exhibits.RigidBody.bodyInertia M)
    (ForPhysLib.Exhibits.RigidBody.labOmega M t)
-/
#guard_msgs in
noncomputable example (M : RigidBodyMotion 3) (t : Time) :=
  ForPhysLib.Exhibits.RigidBody.rotationalContraction
    ForPhysLib.Exhibits.RigidBody.inertia_mul_angularVelocity
    ForPhysLib.Exhibits.RigidBody.angularVelocity_mul_angularMomentum
    (ForPhysLib.Exhibits.RigidBody.bodyInertia M)
    (ForPhysLib.Exhibits.RigidBody.labOmega M t)

-- Lean type-checks rotational contraction with body-frame inertia and angular velocity, yielding body-frame kinetic energy.
noncomputable example (M : RigidBodyMotion 3) (t : Time) :
    InFrame ForPhysLib.Exhibits.RigidBody.body .scalar
      ForPhysLib.Exhibits.RigidBody.kineticEnergyK ℝ :=
  ForPhysLib.Exhibits.RigidBody.rotationalContraction
    ForPhysLib.Exhibits.RigidBody.inertia_mul_angularVelocity
    ForPhysLib.Exhibits.RigidBody.angularVelocity_mul_angularMomentum
    (ForPhysLib.Exhibits.RigidBody.bodyInertia M)
    (ForPhysLib.Exhibits.RigidBody.bodyOmega M t)

-- Lean type-checks the equality identifying body-frame rotational contraction with PhysLib's rotational kinetic energy.
example := ForPhysLib.Exhibits.RigidBody.rotationalContraction_eq_physlib
-- ANCHOR_END: framed_rotational_energy

-- ANCHOR: solid_sphere
-- Lean type-checks PhysLib's solid-sphere inertia-tensor result.
example := ForPhysLib.ClassicalMechanics.SolidSphereInertia.solidSphere_inertiaTensor
-- ANCHOR_END: solid_sphere

end HCP.L3_TheBodyOpens
