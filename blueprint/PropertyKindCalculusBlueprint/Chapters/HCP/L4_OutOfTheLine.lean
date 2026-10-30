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

/-
---
hcp: 5
id: hcp-l4
persona: "PhysLib contributor"
layer: PKC
pull: "The wobble throws body A's centre of mass off the line, and a second observer on a moving cart sees the pair differently. What must the model now say about where things are, and for whom?"
improvement: "Move the pair's centre-of-mass points into 3-D space, attach separation to its named pair, and make each observer's frame explicit."
concepts:
  - informal: "a pair state places body centres in 3-D"
    formal: "PairState3, BodyOf, and positionQ over the state's centre fields"
    where: "HCP.L4_OutOfTheLine#pair_state_and_bearers"
  - informal: "the A–B distance belongs to its pair and can change between states"
    formal: "separationOf, separationOf_magnitude, separationChange, and separationChange_magnitude"
    where: "HCP.L4_OutOfTheLine#whose_distance"
  - informal: "distance is the norm of displacement"
    formal: "distanceQ_eq_lengthOf_displacementQ and distanceQ_triangle over PairState3 points"
    where: "HCP.L4_OutOfTheLine#distance_is_length"
  - informal: "a vector's physical role and observer determine its transport"
    formal: "barePairDisplacement, kGeometricTransport, kBoostTransport, and origin_displacement_eq"
    where: "HCP.L4_OutOfTheLine#bare_frames; HCP.L4_OutOfTheLine#kinded_frames; HCP.L4_OutOfTheLine#observer_motion"
  - informal: "the Space adoption ladder reaches audited boundaries"
    formal: "pairSpanArea, pairSpanArea_magnitude, and the area-product refusal"
    where: "HCP.L4_OutOfTheLine#adoption_ladder"
artifacts: ['Lean lesson HCP.L4_OutOfTheLine', 'Blueprint chapter L4 — Out of the line']
tools: ['lake build HCP', 'python3 HCP/check-hcp.py']
exercises: 7
disclosure: ['distinguish points, vectors, and scalar distances', 'index pair separation by nominal identity', 'compare same-pair states', 'expose the role-blind bare frame API', 'kind frame transports by vector role', 'make observer motion part of frame context', 'recap Space stages 0–4']
owner: 'PKC methodology lead'
state:
  completed: []
---
-/

#doc (Manual) "L4 — Out of the line" =>
%%%
tag := "hcp-l4"
%%%

# Synopsis

## Purpose

Move pair P into three-dimensional space, seen from two reference frames: the lab, and a cart moving at constant velocity relative to it. Positions, displacements and distances get distinct ISO 80000-3 kinds, so adding a position to a displacement fails to type-check. The A–B separation is an `IndividualQuantity` about the pair it belongs to, so pair P's separation cannot be used where pair Q's is expected. Each frame conversion accepts one kind of vector: `kGeometricTransport` converts displacements and `kBoostTransport` converts velocities, so passing a displacement to `kBoostTransport` fails to type-check.

## PKC vocabulary in scope

New at this step:
- `positionVector`, `distance`, `area` — ISO 80000-3 space kinds (with `displacement`, carried from L2: the spring extension is the same kind).
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

# Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean and
PhysLib and trust `Dimension` and `WithDim`; L0–L3 have established kinds, bearers,
composition, and body- and lab-frame angular velocity.

# Pull

The wobble throws body A's centre of mass off the line, and a second observer on a moving cart sees the pair differently. What must the model now say about where things are, and for whom? L4 moves the two centres of mass into `Space 3`, distinguishes points from vectors and distances, and states the observer whose frame supplies a vector's context. One name is one system: records under it are states at different times, configurations, or rival estimates; comparing them is the point. Distinct names are distinct systems. Pair P's separation has one bearer across its states, while pair Q has a different bearer. The lab frame F and cart frame G are explicit observers.

# Risks at this step

- *Bearer erased.* `distanceQ` cannot distinguish the A–B separation of pair P from that of pair Q; the typed cross-pair refusal is pinned at `HCP.L4_OutOfTheLine#whose_distance`.
- *Observer left implicit.* Bare vectors accept geometric, boost, and origin-shift transport even though only one law is right for each vector kind; `HCP.L4_OutOfTheLine#bare_frames` shows the wrong accepted forms and `HCP.L4_OutOfTheLine#kinded_frames` pins the role-specific refusals.

*Further reading*
- `Exhibits/ReferenceFrame`, MOTIVATION M7.

# Small rigorous improvement

:::table +header
*
  * Question
  * Context change
  * Attribute change
  * Risk shown
  * PhysLib stage
*
  * The wobble throws body A's centre of mass off the line, and a second observer on a moving cart sees the pair differently. What must the model now say about where things are, and for whom?
  * The pair's centres become points in `Space 3`; lab F and cart G are named frames.
  * Position vector, displacement, pair distance, and velocity per frame.
  * Pair P's distance can be confused with pair Q's, and bare frame vectors accept transport laws that are wrong for the vector's role.
  * Space Stages 0–4.
:::

The remaining one-dimensional, one-observer assumption is gone. The no-dissipation
assumption remains for L5.

# Learning path

:::table +header
*
  * #
  * Do
  * Checked by `HCP.L4_OutOfTheLine` anchor
  * Concept disclosed
*
  * 1
  * Put the two centres in a `PairState3`; read position, displacement, and distance, then try the two kind collisions.
  * `points_vectors_and_distances`
  * Position and displacement are distinct vector kinds; distance and the length of displacement are distinct scalar kinds, even where magnitudes agree. HCP's body and separation bearers retain nominal identity.
*
  * 2
  * Attach the distance to the named pair, compare two states, and mix P with Q.
  * `whose_distance`
  * `distance` admits `DifferenceKind.ofScale`; same-name states have a typed change whose magnitude reads their own centres, while Q's separation cannot be added to P's.
*
  * 3
  * Relate distance to displacement length and apply the triangle inequality to state points.
  * `distance_is_length`
  * `distanceQ_eq_lengthOf_displacementQ` and `distanceQ_triangle` operate directly on the pair state's centres.
*
  * 4
  * Feed one state-derived bare frame vector to all three upstream transports and add the cart's origin velocity.
  * `bare_frames`
  * Both terms compile, but are physically wrong when the vector's role is displacement: bare `F.Vector` cannot select a transport law or distinguish displacement from velocity.
*
  * 5
  * Use `KVector` for displacement and velocity; try the wrong boost and velocity-plus-force.
  * `kinded_frames`
  * Frame components enter through each frame's own `dispEquiv`; the observer-independence theorem verifies geometric transport. Boost-on-displacement and velocity-plus-force are pinned refusals. Average velocity is computed from two same-pair states and an elapsed duration.
*
  * 6
  * State the cart-origin displacement law and try adding its frame velocity to the pair displacement.
  * `observer_motion`
  * `origin_displacement_eq` makes observer motion an attribute of the cart frame; the kinded displacement-plus-velocity sum is refused.
*
  * 7
  * Map Space Stages 0–4 and exercise Stage 3's operator table.
  * `adoption_ladder`
  * `spanArea` and its magnitude law are accepted on a displacement from the state and a probe point; area × area is refused. Stage 4's boundary and API-map audits are the final rung.
:::

Worksheet: `HCP/Worksheets/L4_OutOfTheLine.lean` · Solution: `HCP/L4_OutOfTheLine.lean`

# Lesson

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

## Space adoption ladder

:::table +header
*
  * Stage
  * File
  * What it contributes
*
  * 0
  * `ForPhysLib/Kinds/Space.lean`
  * Kind vocabulary for length, distance, position vector, displacement, and area.
*
  * 1
  * `ForPhysLib/Metrology/Space.lean`
  * Dimension pairings and the kind algebra.
*
  * 2
  * `ForPhysLib/Kinded/Space.lean`
  * `positionQ`, `displacementQ`, `distanceQ`, and `lengthOf`.
*
  * 3
  * `ForPhysLib/Operators/Space.lean`
  * The curated operator table: `spanArea` is accepted, area × area is not.
*
  * 4
  * `ForPhysLib/Audits/Space.lean` and `Space.checked_by.yaml`
  * Boundary and API-map audits under build checks.
:::

The Stage-3 accepted form is
`spanArea v w : Quantity area ℝ`, with magnitude
`‖v.magnitude‖ * ‖w.magnitude‖`; the product of two areas has no registration. Stage 4
audits the authored boundary and ties the API map to its Lean declarations.

# AI assistance contract

- Keep L4 independent: define local `PairId | P | Q` and `Body | A | B`.
- Preserve nominal identity: one name is one system; records under it are states,
  configurations, or rival estimates; distinct names are distinct systems.
- Use the exact `PairState3.com` fields for all accepted position, displacement,
  distance, velocity, and area forms.
- Keep the `distance` bearer pair-indexed in HCP; do not alter ForPhysLib's `distanceQ`.
- Reuse the Space and ReferenceFrame APIs, and pin each requested kind refusal.
- Label the accepted unkinded frame examples wrong; they do not encode physical role.
- Recap, rather than rewrite, Space Stages 0–4 and point to Stage 4 audits.
- Leave the no-dissipation assumption for L5.

# Questions to ask the model so far

:::table +header
*
  * Question
  * Check
  * What the verdict means
*
  * Where is body A in this state?
  * `points_vectors_and_distances`
  * `positionQ` reads the state's `com .A` point from the conventional origin, and `BodyOf π` retains the body's nominal pair identity.
*
  * Can position be added to displacement?
  * `points_vectors_and_distances`
  * No; the Space kind layer refuses the distinct vector roles.
*
  * Is distance interchangeable with displacement length?
  * `points_vectors_and_distances`, `distance_is_length`
  * No; their scalar magnitudes are related by a theorem, not kind identity.
*
  * Whose separation is this?
  * `whose_distance`
  * `SeparationOf π` retains the pair name erased by the upstream `distanceQ`.
*
  * Can the separation change between P states?
  * `whose_distance`
  * Yes; distance is ratio-scale and the difference magnitude is the later distance minus the earlier one, computed from each state's centres.
*
  * Can Q's distance be mixed with P's?
  * `whose_distance`
  * No; distinct pair identities yield distinct separation bearers.
*
  * Which frame law applies to a displacement?
  * `bare_frames`, `kinded_frames`
  * Bare `F.Vector` accepts all three; `KVector` allows geometric transport, proves observer independence, and refuses the boost law.
*
  * Where does the observer's velocity live?
  * `observer_motion`
  * On the cart frame context, and not as a summand of the pair displacement.
*
  * What does the adoption ladder contribute?
  * `adoption_ladder`
  * Stage 3 curates operators; Stage 4 audits the Space boundary and API map.
:::

# System-context card

:::table +header
*
  * Scope
  * System or component
  * Sort / status
  * L4 assumptions and attributes
*
  * System
  * Coupled pair P or Q
  * Nominal `PairId`
  * One name denotes one system; records under it can be different states, configurations, or rival estimates. P and Q are distinct systems.
*
  * State
  * Pair state
  * `PairState3 π`
  * Stores the centre-of-mass point of each body in `Space 3`.
*
  * Part
  * Body A or B
  * `BodyOf π`
  * Its position vector is read from the point in this state.
*
  * Attribute
  * A–B separation
  * `SeparationOf π`
  * `distance` in ℝ; its change is comparable between states of one pair.
*
  * Attribute
  * Pair displacement
  * `SeparationOf π` bearer
  * A vector from body B's centre to body A's centre, kind `displacement`.
*
  * Observer
  * Lab F or cart G
  * `ReferenceFrame 3`
  * The frame is part of the context; the cart's origin velocity and motion law are explicit.
*
  * Deferred assumption
  * No dissipation
  * L5
  * Not changed by this spatial and observer refinement.
:::
