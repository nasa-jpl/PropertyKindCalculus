/-
# L4 — Out of the line

Solution for the worksheet HCP/Worksheets/L4_OutOfTheLine.lean.

Seven build-checked probes of three-dimensional positions, distances, and reference frames.
-/

module

public import ForPhysLib.Kinded.Space
public import ForPhysLib.Operators.Space
public import ForPhysLib.Exhibits.ReferenceFrame.Findings
public import PropertyKindCalculus

@[expose] public section

open PropertyKindCalculus ForPhysLib.Kinds.Space ForPhysLib.Kinded.Space
open ForPhysLib.Exhibits.ReferenceFrame ClassicalMechanics
open scoped PropertyKindCalculus.OperatorTable

noncomputable section

-- ANCHOR: pair_state_and_bearers
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
-- ANCHOR_END: pair_state_and_bearers

-- ANCHOR: points_vectors_and_distances
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
-- ANCHOR_END: points_vectors_and_distances

-- ANCHOR: whose_distance
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
-- ANCHOR_END: whose_distance

-- ANCHOR: distance_is_length
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
-- ANCHOR_END: distance_is_length

-- ANCHOR: bare_frames
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
-- ANCHOR_END: bare_frames

-- ANCHOR: kinded_frames
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
-- ANCHOR_END: kinded_frames

-- ANCHOR: observer_motion
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
-- ANCHOR_END: observer_motion

-- ANCHOR: adoption_ladder
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
-- ANCHOR_END: adoption_ladder

end
