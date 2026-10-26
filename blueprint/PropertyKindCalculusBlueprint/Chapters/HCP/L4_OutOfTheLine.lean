import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "HCP.L4_OutOfTheLine"

#doc (Manual) "L4 — Out of the line" =>
%%%
tag := "hcp-l4"
%%%

# Synopsis

## Purpose

Move pair P into three-dimensional space, seen from two reference frames: the lab, and a cart moving at constant velocity relative to it. Positions, displacements and distances get distinct ISO 80000-3 kinds, so adding a position to a displacement fails to type-check. The A–B separation is an `IndividualQuantity` about the pair it belongs to, so pair P's separation cannot be used where pair Q's is expected. Each frame conversion accepts one kind of vector: `kGeometricTransport` converts displacements and `kBoostTransport` converts velocities, so passing a displacement to `kBoostTransport` fails to type-check.

## PKC vocabulary in scope

New at this step:
- `positionVector`, `displacement`, `distance`, `area` — ISO 80000-3 space kinds.
- `positionQ`, `displacementQ`, `distanceQ`, `lengthOf` — read PhysLib's `Space` values at their kinds.
- `KVector` — a frame vector with its physical kind stated.
- `kGeometricTransport`, `kBoostTransport` — frame conversions, each typed for one kind of vector.
- `velocityK`, `forceK`, `durationK` — kinds that share PhysLib's one vector type.
- `DifferenceKind` — a kind-level difference law.

Carried from earlier steps: `Quantity`, `IndividualQuantity`, `DifferenceKind.ofScale`, `SortOfSystem`, `Sorted`, `Designated`.

## Verifiable properties

- Adding a position to a displacement fails to type-check, and so does adding a distance to the length of a displacement: there is no `HAdd` instance for either pair of kinds (refused) `HCP.L4_OutOfTheLine#points_vectors_and_distances`.
- Pair P's A–B separation is an `IndividualQuantity` of kind distance about P, and pair Q's separation supplied where P's is expected fails with a type mismatch (refused) `HCP.L4_OutOfTheLine#whose_distance`.
- The distance between two points equals the length of the displacement between them (theorem) `HCP.L4_OutOfTheLine#distance_is_length`.
- `kBoostTransport` rejects a displacement with a type mismatch, and adding a velocity to a force fails to type-check (refused) `HCP.L4_OutOfTheLine#kinded_frames`.
- Converting P's displacement from frame F to frame G with `kGeometricTransport` gives the displacement that G computes from its own coordinates (theorem) `HCP.L4_OutOfTheLine#kinded_frames`.
- The displacement of the cart's origin between times t₁ and t₂ equals the elapsed time times the cart's velocity (theorem) `HCP.L4_OutOfTheLine#observer_motion`.

## Errors prevented

- Bearer erased: pair P's A–B separation used where pair Q's is meant (`HCP.L4_OutOfTheLine#whose_distance`).
- Observer left implicit: with PhysLib's single vector type, the geometric, boost and origin-shift conversions all accept the same vector; with kinded vectors, each conversion accepts only the kind it is correct for (`HCP.L4_OutOfTheLine#bare_frames`, `HCP.L4_OutOfTheLine#kinded_frames`).
- Point/vector confusion: a position added to a displacement, or a distance added to the length of a displacement (`HCP.L4_OutOfTheLine#points_vectors_and_distances`).

# Lesson


The wobble throws body A's centre of mass off the line, and a second observer on a
moving cart sees the pair differently. L4 moves the two centres of mass into `Space 3`,
distinguishes points from vectors and distances, and states the observer whose frame
supplies a vector's context. One name remains one system: records under it can be states
at different times, configurations, or rival estimates; comparing them is the point.
Distinct names are distinct systems. The lab F and cart G are explicit reference frames.

# Risks at this step

- *Bearer erased.* `distanceQ` cannot distinguish the A–B separation of pair P from that of pair Q; the typed cross-pair refusal is pinned at `HCP.L4_OutOfTheLine#whose_distance`.
- *Observer left implicit.* Bare vectors accept geometric, boost, and origin-shift transport even though only one law is right for each vector kind; `HCP.L4_OutOfTheLine#bare_frames` shows the wrong accepted forms and `HCP.L4_OutOfTheLine#kinded_frames` pins the role-specific refusals.

*Further reading*
- `Exhibits/ReferenceFrame`, MOTIVATION M7.

_1. Points, vectors, and distances._ `PairState3 π` stores this state's centre-of-mass
points. `BodyOf π` keeps a body's nominal pair identity, while `SeparationOf π` names
the pair's A–B separation. The upstream `positionQ`, `displacementQ`, and `distanceQ`
are applied to the state fields. Position plus displacement and distance plus the
length of that displacement are both pinned refusals:

```anchor pair_state_and_bearers
/--
One pair name is one system. Records under that name are its states, configurations, or
rival estimates; comparing them is the point. Distinct names are distinct systems.
-/
inductive PairId | P | Q
deriving DecidableEq, Repr

inductive Body | A | B
deriving DecidableEq, Repr

structure PairState3 (π : PairId) where
  com : Body → Space 3

structure BodyOf (π : PairId) where
  body : Body
deriving DecidableEq, Repr

structure SeparationOf (π : PairId) where
deriving DecidableEq, Repr

def bodyS : SortOfSystem := ⟨"body centre"⟩
def separationS : SortOfSystem := ⟨"pair separation"⟩

instance {π : PairId} : Sorted (BodyOf π) := ⟨fun _ => bodyS⟩

instance {π : PairId} : Designated (BodyOf π) where
  designation
    | ⟨.A⟩ => ⟨"body A"⟩
    | ⟨.B⟩ => ⟨"body B"⟩
  designation_inj {x y} h := by
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    cases x <;> cases y <;> first | rfl | exact absurd (System.mk.inj h) (by decide)

instance {π : PairId} : Sorted (SeparationOf π) := ⟨fun _ => separationS⟩

instance {π : PairId} : Designated (SeparationOf π) where
  designation _ := ⟨"A–B separation"⟩
  designation_inj {x y} _ := by cases x; cases y; rfl

def bodyPositionOf {π : PairId} (s : PairState3 π) (b : BodyOf π) :
    IndividualQuantity b ForPhysLib.Kinds.Space.positionVector (EuclideanSpace ℝ (Fin 3)) :=
  ⟨(ForPhysLib.Kinded.Space.positionQ (s.com b.body)).magnitude⟩

def pairDisplacementOf {π : PairId} (s : PairState3 π) :
    IndividualQuantity (⟨⟩ : SeparationOf π) ForPhysLib.Kinds.Space.displacement
      (EuclideanSpace ℝ (Fin 3)) :=
  ⟨(ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B)).magnitude⟩
```

```anchor points_vectors_and_distances
-- Point vs vector: Constructs body A's location as a bearer-free `Quantity positionVector`; its type records position kind, not pair P versus Q.
example (s : PairState3 .P) :
    Quantity ForPhysLib.Kinds.Space.positionVector (EuclideanSpace ℝ (Fin 3)) :=
  ForPhysLib.Kinded.Space.positionQ (s.com .A)

-- Point vs vector: Constructs pair P's A-to-B difference as a bearer-free `Quantity displacement`; its type cannot distinguish pair P from Q.
example (s : PairState3 .P) :
    Quantity ForPhysLib.Kinds.Space.displacement (EuclideanSpace ℝ (Fin 3)) :=
  ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B)

-- Point vs vector: Constructs pair P's scalar separation as a bearer-free `Quantity distance`; its type separates distance from displacement and length, not P from Q.
example (s : PairState3 .P) : Quantity ForPhysLib.Kinds.Space.distance ℝ :=
  ForPhysLib.Kinded.Space.distanceQ (s.com .A) (s.com .B)

-- Point vs vector: Refused: no HAdd instance combines positionVector and displacement; ordinary addition would conflate a point with its offset instead of translating it.
/--
error: failed to synthesize instance of type class
  HAdd (Quantity positionVector (EuclideanSpace ℝ (Fin 3))) (Quantity displacement (EuclideanSpace ℝ (Fin 3))) ?m.10

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (s : PairState3 .P) :=
  ForPhysLib.Kinded.Space.positionQ (s.com .A) +
    ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B)

-- Kind vs dimension: Refused: no HAdd instance combines distance and length, preventing a sum of distinct scalar kinds despite their shared length dimension.
/--
error: failed to synthesize instance of type class
  HAdd (Quantity distance ℝ) (Quantity length ℝ) ?m.12

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (s : PairState3 .P) :=
  ForPhysLib.Kinded.Space.distanceQ (s.com .A) (s.com .B) +
    ForPhysLib.Kinded.Space.lengthOf
      (ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B))
```

_2. Whose distance._ `distanceQ` returns a `Quantity` and so erases the HCP pair
bearer. `separationOf` puts that same distance on `SeparationOf π`. Distance is a
ratio-scale length species, so `DifferenceKind.ofScale` applies: two records under P
can express a change in separation, while Q's pair bearer does not unify with P's.

```anchor whose_distance
def separationOf {π : PairId} (s : PairState3 π) :
    IndividualQuantity (⟨⟩ : SeparationOf π) ForPhysLib.Kinds.Space.distance ℝ :=
  ⟨(ForPhysLib.Kinded.Space.distanceQ (s.com .A) (s.com .B)).magnitude⟩

/-- Bearer safety: Proves that pair P's indexed separation magnitude is the distance between body A's and body B's centres of mass. -/
lemma separationOf_magnitude {π : PairId} (s : PairState3 π) :
    (separationOf s).magnitude = dist (s.com .A) (s.com .B) := rfl

-- Distance is ratio-scale in ISO 80000-3, so its difference is licensed.
-- Composition law: Constructs a DifferenceKind for distance from its ratio scale, licensing a change between states of pair P.
example : DifferenceKind ForPhysLib.Kinds.Space.distance := DifferenceKind.ofScale

def separationChange (earlier later : PairState3 .P) :
    IndividualQuantity (⟨⟩ : SeparationOf .P) ForPhysLib.Kinds.Space.distance ℝ :=
  IndividualQuantity.add DifferenceKind.ofScale
    (separationOf later) (-(separationOf earlier))

/-- Same-name records: Proves that pair P's separation-change magnitude is later A–B distance minus earlier A–B distance. -/
lemma separationChange_magnitude (earlier later : PairState3 .P) :
    (separationChange earlier later).magnitude =
      dist (later.com .A) (later.com .B) - dist (earlier.com .A) (earlier.com .B) := by
  simp [separationChange, IndividualQuantity.add_magnitude,
    IndividualQuantity.neg_magnitude, separationOf]
  change dist (later.com .A) (later.com .B) +
      (-(dist (earlier.com .A) (earlier.com .B))) =
    dist (later.com .A) (later.com .B) - dist (earlier.com .A) (earlier.com .B)
  ring

-- Bearer safety: Refused: type mismatch between pair P's and pair Q's SeparationOf bearers; this prevents treating distinct pairs as one distance history.
/--
error: Application type mismatch: The argument
  qDistance
has type
  IndividualQuantity (@SeparationOf.mk PairId.Q) distance ℝ
but is expected to have type
  IndividualQuantity (@SeparationOf.mk PairId.P) distance ℝ
in the application
  IndividualQuantity.add ⋯ (separationOf p) qDistance
-/
#guard_msgs (whitespace := lax) in
example (p : PairState3 .P) (q : PairState3 .Q) :=
  let qDistance : IndividualQuantity (⟨⟩ : SeparationOf .Q)
      ForPhysLib.Kinds.Space.distance ℝ := separationOf q
  IndividualQuantity.add DifferenceKind.ofScale (separationOf p) qDistance
```

_3. Distance is displacement length._ These laws are applied to the state’s own A and B
centres. The magnitudes agree, but the kinds remain distinct; the triangle law is another
statement over the points carried by one `PairState3`.

```anchor distance_is_length
-- Point vs vector: Proves that pair P's A–B distance equals the length of its displacement; distance is the norm of the connecting vector.
example (s : PairState3 .P) :
    (ForPhysLib.Kinded.Space.distanceQ (s.com .A) (s.com .B)).magnitude =
      (ForPhysLib.Kinded.Space.lengthOf
        (ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B))).magnitude :=
  ForPhysLib.Kinded.Space.distanceQ_eq_lengthOf_displacementQ (s.com .A) (s.com .B)

-- Point vs vector: Proves that pair P's triangle inequality is distance(A,A) ≤ distance(A,B) + distance(B,A), a geometric law on its points.
example (s : PairState3 .P) :
    (ForPhysLib.Kinded.Space.distanceQ (s.com .A) (s.com .A)).magnitude ≤
      (ForPhysLib.Kinded.Space.distanceQ (s.com .A) (s.com .B)).magnitude +
        (ForPhysLib.Kinded.Space.distanceQ (s.com .B) (s.com .A)).magnitude :=
  ForPhysLib.Kinded.Space.distanceQ_triangle (s.com .A) (s.com .B) (s.com .A)
```

_4. Bare frames._ The vector fed to the three upstream laws is derived from this state's
two centres. All three transports accept it because `F.Vector` records a frame but not a
physical role. The displacement-plus-origin-velocity sum also elaborates. Both are
accepted but physically wrong when that vector is meant to be a displacement.

```anchor bare_frames
def barePairDisplacement {π : PairId} (s : PairState3 π)
    (F : ReferenceFrame 3) (t : Time) : F.Vector :=
  (ReferenceFrame.Vector.dispEquiv (frame := F) (F.timeEquiv.symm t)).symm
    (s.com .A -ᵥ s.com .B)

-- Frame safety: Bare vectors erase physical frame and kind, so all three transports accept pair P's A–B displacement; only geometric is correct, and kinded `kBoostTransport` refuses it.
example (s : PairState3 .P) (F G : ReferenceFrame 3) (t : Time)
    (u : EuclideanSpace ℝ (Fin 3)) :
    G.Vector × G.Vector × G.Vector :=
  let v := barePairDisplacement s F t
  (geometricTransport F G t v, boostTransport F G t u v, originShiftTransport F G t v)

-- Frame safety: Bare EuclideanSpace vectors accept adding pair P's displacement to cart velocity; the unindexed result cannot catch this physically invalid sum.
example (s : PairState3 .P) (cart : ReferenceFrame 3) (hCart : cart.IsInertial) :
    EuclideanSpace ℝ (Fin 3) :=
  (s.com .A -ᵥ s.com .B) + hCart.velocity
```

_5. Kinded frames._ Frame components must enter through the frame's own `dispEquiv`.
With `KVector`, the displacement goes through geometric transport, and an average
velocity computed from two same-pair centre states goes through the boost law. The
observer-independence theorem shows that geometric transport preserves the displacement.
The wrong boost on a displacement and a velocity-plus-force sum are pinned refusals.

```anchor kinded_frames
/- Frame components must enter through the frame's own `dispEquiv`. -/
def pairDisplacementInFrame {π : PairId} (F : ReferenceFrame 3) (t : Time)
    (s : PairState3 π) :
    KVector F ForPhysLib.Kinds.Space.displacement :=
  ⟨⟨(barePairDisplacement s F t).components⟩⟩

def averageVelocityOfA {π : PairId} (earlier later : PairState3 π)
    (elapsed : Quantity durationK ℝ) (h : elapsed.magnitude ≠ 0) :
    Quantity velocityK (EuclideanSpace ℝ (Fin 3)) :=
  ⟨(if hzero : elapsed.magnitude = 0 then False.elim (h hzero)
    else elapsed.magnitude⁻¹) • (later.com .A -ᵥ earlier.com .A)⟩

def averageVelocityInFrame {π : PairId} (F : ReferenceFrame 3) (t : Time)
    (earlier later : PairState3 π) (elapsed : Quantity durationK ℝ)
    (h : elapsed.magnitude ≠ 0) : KVector F velocityK :=
  ⟨⟨((ReferenceFrame.Vector.dispEquiv (frame := F) (F.timeEquiv.symm t)).symm
    (averageVelocityOfA earlier later elapsed h).magnitude).components⟩⟩

-- Frame safety: Constructs a bearer-free `KVector G displacement` for pair P via geometric transport; frame and kind remain indexed, but P and Q displacements share a type.
example (s : PairState3 .P) (F G : ReferenceFrame 3) (t : Time) :
    KVector G ForPhysLib.Kinds.Space.displacement :=
  kGeometricTransport F G t (pairDisplacementInFrame F t s)

/-- Frame safety: Proves that geometric transport of pair P's displacement from F to G yields its G representation, so displacement is observer-independent. -/
theorem pairDisplacement_observer_independent {π : PairId}
    (F G : ReferenceFrame 3) (t : Time) (s : PairState3 π) :
    kGeometricTransport F G t (pairDisplacementInFrame F t s) =
      pairDisplacementInFrame G t s := by
  have hη : (⟨(barePairDisplacement s F t).components⟩ : F.Vector) =
      barePairDisplacement s F t := rfl
  simp only [kGeometricTransport, pairDisplacementInFrame]
  rw [hη]
  simp [barePairDisplacement]

-- Frame safety: Constructs a bearer-free `KVector G velocityK` for body A's average velocity via boost transport; the type cannot distinguish pair P from Q.
example (earlier later : PairState3 .P) (elapsed : Quantity durationK ℝ)
    (h : elapsed.magnitude ≠ 0) (F G : ReferenceFrame 3) (t : Time)
    (u : Quantity velocityK (EuclideanSpace ℝ (Fin 3))) :
    KVector G velocityK :=
  kBoostTransport F G t u (averageVelocityInFrame F t earlier later elapsed h)

-- Frame safety: Refused: type mismatch between pair P's KVector displacement and the KVector velocity required by boost transport; displacement cannot be boosted as velocity.
/--
error: Application type mismatch: The argument
  pairDisplacementInFrame F t s
has type
  KVector F displacement
but is expected to have type
  KVector F velocityK
in the application
  kBoostTransport F G t u (pairDisplacementInFrame F t s)
-/
#guard_msgs (whitespace := lax) in
example (F G : ReferenceFrame 3) (t : Time)
    (u : Quantity velocityK (EuclideanSpace ℝ (Fin 3))) (s : PairState3 .P) :=
  kBoostTransport F G t u (pairDisplacementInFrame F t s)

-- Kind vs dimension: Refused: no HAdd instance combines frame-F velocity and force vectors, preventing addition of unlike physical kinds.
/--
error: failed to synthesize instance of type class
  HAdd (KVector F velocityK) (KVector F forceK) ?m.9

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (F : ReferenceFrame 3) (v : KVector F velocityK) (force : KVector F forceK) :=
  v + force
```

_6. The observer moves._ `origin_displacement_eq` states the cart frame's own origin
motion over elapsed time. The pair's state-derived displacement still cannot be added to
that frame's kinded velocity.

```anchor observer_motion
-- Frame safety: Proves that the inertial cart's origin-displacement magnitude equals elapsed time times cart-velocity magnitude; the law belongs to the cart frame.
example (cart : ReferenceFrame 3) (hCart : cart.IsInertial) (t₁ t₂ : Time) :
    (ForPhysLib.Kinded.Space.displacementQ (cart.origin t₂) (cart.origin t₁)).magnitude =
      (elapsedQ t₁ t₂).magnitude • (frameVelocityQ hCart).magnitude :=
  origin_displacement_eq cart hCart t₁ t₂

-- Kind vs dimension: Refused: no HAdd instance combines displacement and velocity quantities, preventing addition of unlike vector kinds.
/--
error: failed to synthesize instance of type class
  HAdd (Quantity displacement (EuclideanSpace ℝ (Fin 3))) (Quantity velocityK (EuclideanSpace ℝ (Fin 3))) ?m.13

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (s : PairState3 .P) (cart : ReferenceFrame 3) (hCart : cart.IsInertial) :=
  ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B) + frameVelocityQ hCart
```

_7. Adoption ladder._ The five Space stages go from Kinds, through Metrology,
Kinded and Operators, to Audits. Stage 3's operator-built area is computed from this
state's A–B displacement and a probe-point displacement; its magnitude law is accepted,
while area × area is refused. Stage 4 audits the boundary and anchors the API map.

```anchor adoption_ladder
def pairSpanArea {π : PairId} (s : PairState3 π) (p : Space 3) :
    Quantity ForPhysLib.Kinds.Space.area ℝ :=
  ForPhysLib.Operators.Space.spanArea
    (ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B))
    (ForPhysLib.Kinded.Space.displacementQ (s.com .A) p)

/-- Point vs vector: Proves that pair P's span-area magnitude from A–B and A–p displacements is the product of their norms. -/
lemma pairSpanArea_magnitude {π : PairId} (s : PairState3 π) (p : Space 3) :
    (pairSpanArea s p).magnitude =
      ‖(ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B)).magnitude‖ *
        ‖(ForPhysLib.Kinded.Space.displacementQ (s.com .A) p).magnitude‖ :=
  ForPhysLib.Operators.Space.spanArea_magnitude _ _

-- Point vs vector: Constructs a bearer-free `Quantity area` from pair P's A–B and A–p displacements; its type cannot distinguish areas from other pairs or points.
example (s : PairState3 .P) (p : Space 3) : Quantity ForPhysLib.Kinds.Space.area ℝ :=
  pairSpanArea s p

-- Point vs vector: Proves that pair P's span-area magnitude equals the product of its A–B and A–p displacement norms.
example (s : PairState3 .P) (p : Space 3) :
    (pairSpanArea s p).magnitude =
      ‖(ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B)).magnitude‖ *
        ‖(ForPhysLib.Kinded.Space.displacementQ (s.com .A) p).magnitude‖ :=
  pairSpanArea_magnitude s p

-- Kind vs dimension: Refused: no HMul instance licenses area times area, preventing an unregistered product of two area quantities.
/--
error: failed to synthesize instance of type class
  HMul (Quantity area ℝ) (Quantity area ℝ) ?m.9

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (s : PairState3 .P) (p : Space 3) := pairSpanArea s p * pairSpanArea s p
```

The Space adoption files, in order, are `ForPhysLib/Kinds/Space.lean`,
`ForPhysLib/Metrology/Space.lean`, `ForPhysLib/Kinded/Space.lean`,
`ForPhysLib/Operators/Space.lean`, and `ForPhysLib/Audits/Space.lean`. The final audit
stage is wired to `Space/API-map.md` by `Space.checked_by.yaml`.
