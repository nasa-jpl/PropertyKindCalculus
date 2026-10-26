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

# Synopsis

## Purpose

Open body A of pair P into two rigid halves, with a body-fixed frame beside the lab frame. Mass assembles over the halves as a sum. The centre of mass is the mass-weighted mean of the halves' positions, which is meaningful only when the total mass is nonzero. Every half of a rigid body has the same angular velocity, so angular velocity is intensive and has no `Assembles` instance. Each frame-dependent quantity has its frame in its type (`InFrame`), so a body-frame rotational energy computed from a lab-frame angular velocity fails to type-check.

## PKC vocabulary in scope

New at this step:
- `WeightedCarving` (`parts`, `weight`, `mean`, `total_ne_zero`) — a carving with per-part weights whose mean requires nonzero total weight.
- `totalWeight`, `weightedSum` — the pieces of a weighted mean.
- `Decomposition.fold` — a value per part, combined over a decomposition.
- `InFrame` — components read in a stated frame.
- `union_mass`, `union_centerOfMass`, `union_inertiaTensor` — how mass, centre of mass and inertia combine over a union.
- `labOmega`, `bodyOmega`, `bodyInertia`, `rotationalContraction` — rigid-body quantities indexed by frame.

Carried from earlier steps: `Composite`, `Decomposition`, `Assembles`, `assemble`, `IndividualQuantity`, `DifferenceKind.ofScale`, `SortOfSystem`, `Sorted`, `Designated`, `displacementK`.

## Verifiable properties

- Body A's centre of mass is the mass-weighted mean of its halves' positions: halves of mass 3 and 5 at positions 0 and 10 give 25/4, not the midpoint 5 (theorem) `HCP.L3_TheBodyOpens#center_of_mass_mean`.
- PhysLib's `centerOfMass` of a body with zero mass is the origin, because 1/0 = 0 in Lean; body A's carving comes with a proof that its total mass is nonzero (theorem) `HCP.L3_TheBodyOpens#massless_center_of_mass`.
- Angular velocity is equal on both halves and is not a sum over them, and `assemble` of angular velocity over the halves fails: there is no `Assembles rigidBodyS angularVelocityK` instance (refused) `HCP.L3_TheBodyOpens#angular_velocity_intensive`.
- `rotationalContraction` of the body-frame inertia with the lab-frame ω fails with a type mismatch between `InFrame lab` and `InFrame body` (refused) `HCP.L3_TheBodyOpens#framed_rotational_energy`.
- With the body-frame ω, the kinded rotational energy equals PhysLib's rotational kinetic energy (theorem) `HCP.L3_TheBodyOpens#framed_rotational_energy`.
- A homogeneous solid sphere of mass m and radius R has moment of inertia (2/5) m R² (theorem) `HCP.L3_TheBodyOpens#solid_sphere`.

## Errors prevented

- Sum or midpoint instead of weighted mean: body A's centre of mass computed as the sum or the midpoint of its halves' positions (`HCP.L3_TheBodyOpens#center_of_mass_mean`).
- Degenerate whole: a centre of mass reported for a body with zero total mass, which PhysLib returns as the origin (`HCP.L3_TheBodyOpens#massless_center_of_mass`).
- Wrong frame: PhysLib accepts the lab-frame ω in the body-frame energy; with `InFrame`, it fails to type-check (`HCP.L3_TheBodyOpens#bare_frame_mismatch`, `HCP.L3_TheBodyOpens#framed_rotational_energy`).

# Lesson


Body A of pair P now wobbles instead of sliding along the spring axis. Its centre of mass
is off that line of action, so the spring force misses the centre of mass, produces a
torque, and rotates the body. L3 opens body A into left and right halves, introduces a
body-fixed frame beside the lab frame, and keeps the identity rule from L1–L2: one name is
one system; records under that name are its states, configurations, or rival estimates,
while distinct names denote distinct systems.

# Risks at this step

- *Wrong carving.* For body A of pair P, counting a half twice or leaving one out changes the whole mass; the pinned decomposition gives one slot to each half and proves the total at `HCP.L3_TheBodyOpens#opened_body`.
- *Weighted mean, not sum.* The centre of mass uses each half's mass and position, while both halves share the same angular velocity; the pinned checks are `HCP.L3_TheBodyOpens#center_of_mass_mean` and `HCP.L3_TheBodyOpens#angular_velocity_intensive`.
- *Degenerate whole and frame.* A massless body has no physical centre of mass, and lab-frame angular velocity is not the body-frame input to rotational energy; the checks are `HCP.L3_TheBodyOpens#massless_center_of_mass`, `HCP.L3_TheBodyOpens#bare_frame_mismatch`, and `HCP.L3_TheBodyOpens#framed_rotational_energy`.

*Further reading*
- `Exhibits/Composition`, findings 2 and 5.

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
```

The physical content is
`(mA + mB) com = mA comA + mB comB`, not `com = comA + comB`.

_3. The degenerate whole._ PhysLib defines the massless body's centre of mass to be the
origin by convention. The license to build `centerOfMassCarving` is hypothesis `h`, that
the state's total mass is nonzero; a massless state cannot satisfy it, so it cannot build
the carving:

```anchor massless_center_of_mass
-- Centre of mass: proves that a massless body's `centerOfMass` is the origin, because PhysLib computes (1 / mass) • … and Lean's 1 / 0 = 0.
example := ForPhysLib.Exhibits.Composition.massless_centerOfMass

-- Centre of mass: Proves that the two mass-weighted halves have total weight 2 ≠ 0, supplying the license for their weighted mean.
example := ForPhysLib.Exhibits.Composition.halvesByMass_total_ne_zero
```

_4. Angular velocity is intensive._ The two rigid halves share one angular velocity;
adding their measurements would double it. The upstream finding proves the intensive law
and refutes extensivity, while the HCP attempted assembly is rejected:

```anchor angular_velocity_intensive
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
```

_5. Upstream frames._ PhysLib's bare rotational-energy API accepts the lab-frame
`M.angularVelocity t` against the body-fixed inertia tensor. The term below type-checks,
but it is physically wrong:

```anchor bare_frame_mismatch
-- Frame safety: The bare ℝ example accepts rotational energy from M's body inertia and lab-frame ω; it erases frame and motion bearer, hiding the invalid mix.
noncomputable example (M : RigidBodyMotion 3) (t : Time) : ℝ :=
  M.toRigidBody.rotationalKineticEnergy (M.angularVelocity t)
```

_6. PKC frames._ `rotationalContraction` retains the frame in the type. Lab-frame ω is
therefore refused, body-frame ω is accepted, and the bridge theorem equates the accepted
components with twice PhysLib's own rotational kinetic energy:

```anchor framed_rotational_energy
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
```

_7. Homogeneity returns as a special case._ For a nonzero-radius solid sphere, the proved
inertia tensor is `(2/5) m R²` times the identity matrix:

```anchor solid_sphere
-- Inertia tensor: Proves that the 3D solid sphere's inertia tensor is (2/5) m R² times the identity matrix.
example := ForPhysLib.ClassicalMechanics.SolidSphereInertia.solidSphere_inertiaTensor
```

PhysLib records this target as `informal_lemma` `CM-RB-sphereI`. The proof in
`ForPhysLib.ClassicalMechanics.SolidSphereInertia` is therefore a ready first upstream
contribution for the PhysLib contributor. L4 next revisits motion along one line seen by
one observer.
