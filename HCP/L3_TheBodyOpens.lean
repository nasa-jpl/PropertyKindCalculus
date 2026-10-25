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

/-- Composition law: Proves that the assembled whole-mass magnitude of a body equals the sum of its left- and right-half masses. -/
theorem bodyMass_magnitude {π : PairId} {b : Body} (state : OpenBody π b) :
    (bodyMass state).magnitude = state.mass .left + state.mass .right := by
  rfl

-- Composition law: Proves that PhysLib's union-mass law is mass(A ∪ B) = mass(A) + mass(B), the additive law used for body A's halves.
example := ForPhysLib.Exhibits.Composition.union_mass

-- Composition law: Proves that PhysLib's union-inertia law is I(A ∪ B) = I(A) + I(B) about a common origin; the theorem's type does not record the axis.
example := ForPhysLib.Exhibits.Composition.union_inertiaTensor

-- Same-name records: Constructs a massK IndividualQuantity about body A's left half in pair P, allowing earlier and later states of that half to be compared.
#guard_msgs in
example (earlier later : OpenBody .P .A) :
    IndividualQuantity
      (Composite.part (σ := rigidBodyS) (halfPart .P .A .left))
      massK ℝ :=
  IndividualQuantity.add DifferenceKind.ofScale
    (massOf later (halfPart .P .A .left))
    (-(massOf earlier (halfPart .P .A .left)))

-- Bearer safety: Refused: type mismatch between body A's left-half mass bearers in pairs P and Q; this prevents treating distinct pairs as one state history.
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
-- Centre of mass: Proves that with nonzero masses, (mA + mB)·COM(A ∪ B) = mA·COM(A) + mB·COM(B), PhysLib's weighted-mean law.
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

/-- Centre of mass: Proves that a body's two-half carving mean is (mL·xL + mR·xR)/(mL + mR) when total mass is nonzero. -/
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

/-- Centre of mass: Proves that body A in pair P, with half masses 3 and 5 at positions 0 and 10, has weighted-mean centre 25/4, not midpoint 5. -/
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

-- Centre of mass: Refused: no Assembles rigidBodyS displacementK instance; the halves' positions form a mass-weighted mean, not an additive total.
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
-- Centre of mass: proves that a massless body's `centerOfMass` is the origin, because PhysLib computes (1 / mass) • … and Lean's 1 / 0 = 0.
example := ForPhysLib.Exhibits.Composition.massless_centerOfMass

-- Centre of mass: Proves that the two mass-weighted halves have total weight 2 ≠ 0, supplying the license for their weighted mean.
example := ForPhysLib.Exhibits.Composition.halvesByMass_total_ne_zero
-- ANCHOR_END: massless_center_of_mass

-- ANCHOR: angular_velocity_intensive
-- Composition law: Proves that angular velocity is intensive: each rigid-body half reads 7 rad/s rather than receiving a share of a total.
example := ForPhysLib.Exhibits.Composition.omegaOfHalf_intensive

-- Composition law: Proves that angular velocity is not extensive across the rigid body's halves: both read 7 rad/s, not a summed 14 rad/s.
example := ForPhysLib.Exhibits.Composition.omegaOfHalf_not_extensive

-- Licensed composition: Refused: no Assembles rigidBodyS angularVelocityK instance; angular velocity is constant across parts, not an additive total.
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
-- Frame safety: The bare ℝ example accepts rotational energy from M's body inertia and lab-frame ω; it erases frame and motion bearer, hiding the invalid mix.
noncomputable example (M : RigidBodyMotion 3) (t : Time) : ℝ :=
  M.toRigidBody.rotationalKineticEnergy (M.angularVelocity t)
-- ANCHOR_END: bare_frame_mismatch

-- ANCHOR: framed_rotational_energy
-- Frame safety: Refused: type mismatch between lab-frame ω and the body-frame ω required by contraction; this prevents pairing body inertia with lab angular velocity.
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

-- Frame safety: Constructs a bearer-free body-frame kineticEnergyK scalar from M's body-frame inertia and angular velocity; the result retains frame and kind, not M.
noncomputable example (M : RigidBodyMotion 3) (t : Time) :
    InFrame ForPhysLib.Exhibits.RigidBody.body .scalar
      ForPhysLib.Exhibits.RigidBody.kineticEnergyK ℝ :=
  ForPhysLib.Exhibits.RigidBody.rotationalContraction
    ForPhysLib.Exhibits.RigidBody.inertia_mul_angularVelocity
    ForPhysLib.Exhibits.RigidBody.angularVelocity_mul_angularMomentum
    (ForPhysLib.Exhibits.RigidBody.bodyInertia M)
    (ForPhysLib.Exhibits.RigidBody.bodyOmega M t)

-- Frame safety: Proves that body-frame rotational contraction equals PhysLib's rotational kinetic energy for the motion's body-frame angular velocity.
example := ForPhysLib.Exhibits.RigidBody.rotationalContraction_eq_physlib
-- ANCHOR_END: framed_rotational_energy

-- ANCHOR: solid_sphere
-- Composition law: Proves that the 3D solid sphere's inertia tensor is (2/5) m R² times the identity matrix.
example := ForPhysLib.ClassicalMechanics.SolidSphereInertia.solidSphere_inertiaTensor
-- ANCHOR_END: solid_sphere

end HCP.L3_TheBodyOpens
