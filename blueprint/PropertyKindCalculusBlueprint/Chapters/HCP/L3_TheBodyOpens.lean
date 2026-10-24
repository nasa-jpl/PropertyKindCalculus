import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "HCP.L3_TheBodyOpens"

#doc (Manual) "L3 — The body opens up" =>
%%%
tag := "hcp-l3"
%%%

Body A of pair P now wobbles instead of sliding along the spring axis. Its centre of mass
is off that line of action, so the spring force misses the centre of mass, produces a
torque, and rotates the body. L3 opens body A into left and right halves, introduces a
body-fixed frame beside the lab frame, and keeps the identity rule from L1–L2: one name is
one system; records under that name are its states, configurations, or rival estimates,
while distinct names denote distinct systems.

_1. Open body A._ `HalfOf π b` adds nominal pair-and-body identity to the upstream
left/right `Half`. `OpenBody π b` records per-half mass and one position coordinate. The
existing `Assembles rigidBodyS massK` license produces the whole-body total and its
magnitude reads the two real fields. Upstream's union theorems state the corresponding
mass and inertia-tensor laws. Same-name records share bearers, while P and Q do not:

```anchor opened_body
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

theorem bodyMass_magnitude {π : PairId} {b : Body} (state : OpenBody π b) :
    (bodyMass state).magnitude = state.mass .left + state.mass .right := by
  rfl

example := ForPhysLib.Exhibits.Composition.union_mass

example := ForPhysLib.Exhibits.Composition.union_inertiaTensor

#guard_msgs in
example (earlier later : OpenBody .P .A) :
    IndividualQuantity
      (Composite.part (σ := rigidBodyS) (halfPart .P .A .left))
      massK ℝ :=
  IndividualQuantity.add DifferenceKind.ofScale
    (massOf later (halfPart .P .A .left))
    (-(massOf earlier (halfPart .P .A .left)))

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
```

The HCP total is the narrow restatement: upstream `union_mass` and
`union_inertiaTensor` are about PhysLib's `RigidBody`, not the nominal
`HalfOf .P .A` bearer.

_2. Centre of mass is a weighted mean._ Upstream supplies both the rigid-body union law
and the general weighted-mean machinery. HCP's `centerOfMassCarving` uses this state's
`OpenBody.mass` for its weights, and `centerOfMass_eq` gives the resulting formula. For
example, masses 3 and 5 at positions 0 and 10 give 25/4 (6.25), not the unit-weight
midpoint 5. HCP's position quantities use the same nominal half bearers as mass, but an
attempted sum has no `Assembles` license:

```anchor center_of_mass_mean
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
```

The physical content is
`(mA + mB) com = mA comA + mB comB`, not `com = comA + comB`.

_3. The degenerate whole._ PhysLib defines the massless body's centre of mass to be the
origin by convention. The license to build `centerOfMassCarving` is hypothesis `h`, that
the state's total mass is nonzero; a massless state cannot satisfy it, so it cannot build
the carving:

```anchor massless_center_of_mass
example := ForPhysLib.Exhibits.Composition.massless_centerOfMass

example := ForPhysLib.Exhibits.Composition.halvesByMass_total_ne_zero
```

_4. Angular velocity is intensive._ The two rigid halves share one angular velocity;
adding their measurements would double it. The upstream finding proves the intensive law
and refutes extensivity, while the HCP attempted assembly is rejected:

```anchor angular_velocity_intensive
example := ForPhysLib.Exhibits.Composition.omegaOfHalf_intensive

example := ForPhysLib.Exhibits.Composition.omegaOfHalf_not_extensive

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
```

_5. Upstream frames._ PhysLib's bare rotational-energy API accepts the lab-frame
`M.angularVelocity t` against the body-fixed inertia tensor. The term below type-checks,
but it is physically wrong:

```anchor bare_frame_mismatch
noncomputable example (M : RigidBodyMotion 3) (t : Time) : ℝ :=
  M.toRigidBody.rotationalKineticEnergy (M.angularVelocity t)
```

_6. PKC frames._ `rotationalContraction` retains the frame in the type. Lab-frame ω is
therefore refused, body-frame ω is accepted, and the bridge theorem equates the accepted
components with twice PhysLib's own rotational kinetic energy:

```anchor framed_rotational_energy
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

noncomputable example (M : RigidBodyMotion 3) (t : Time) :
    InFrame ForPhysLib.Exhibits.RigidBody.body .scalar
      ForPhysLib.Exhibits.RigidBody.kineticEnergyK ℝ :=
  ForPhysLib.Exhibits.RigidBody.rotationalContraction
    ForPhysLib.Exhibits.RigidBody.inertia_mul_angularVelocity
    ForPhysLib.Exhibits.RigidBody.angularVelocity_mul_angularMomentum
    (ForPhysLib.Exhibits.RigidBody.bodyInertia M)
    (ForPhysLib.Exhibits.RigidBody.bodyOmega M t)

example := ForPhysLib.Exhibits.RigidBody.rotationalContraction_eq_physlib
```

_7. Homogeneity returns as a special case._ For a nonzero-radius solid sphere, the proved
inertia tensor is `(2/5) m R²` times the identity matrix:

```anchor solid_sphere
example := ForPhysLib.ClassicalMechanics.SolidSphereInertia.solidSphere_inertiaTensor
```

PhysLib records this target as `informal_lemma` `CM-RB-sphereI`. The proof in
`ForPhysLib.ClassicalMechanics.SolidSphereInertia` is therefore a ready first upstream
contribution for the PhysLib contributor. L4 next revisits motion along one line seen by
one observer.
