/-
# L4 — Out of the line

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
example (s : PairState3 .P) :
    Quantity ForPhysLib.Kinds.Space.positionVector (EuclideanSpace ℝ (Fin 3)) :=
  ForPhysLib.Kinded.Space.positionQ (s.com .A)

example (s : PairState3 .P) :
    Quantity ForPhysLib.Kinds.Space.displacement (EuclideanSpace ℝ (Fin 3)) :=
  ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B)

example (s : PairState3 .P) : Quantity ForPhysLib.Kinds.Space.distance ℝ :=
  ForPhysLib.Kinded.Space.distanceQ (s.com .A) (s.com .B)

/--
error: failed to synthesize instance of type class
  HAdd (Quantity positionVector (EuclideanSpace ℝ (Fin 3))) (Quantity displacement (EuclideanSpace ℝ (Fin 3))) ?m.10

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (s : PairState3 .P) :=
  ForPhysLib.Kinded.Space.positionQ (s.com .A) +
    ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B)

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

lemma separationOf_magnitude {π : PairId} (s : PairState3 π) :
    (separationOf s).magnitude = dist (s.com .A) (s.com .B) := rfl

-- Distance is ratio-scale in ISO 80000-3, so its difference is licensed.
example : DifferenceKind ForPhysLib.Kinds.Space.distance := DifferenceKind.ofScale

def separationChange (earlier later : PairState3 .P) :
    IndividualQuantity (⟨⟩ : SeparationOf .P) ForPhysLib.Kinds.Space.distance ℝ :=
  IndividualQuantity.add DifferenceKind.ofScale
    (separationOf later) (-(separationOf earlier))

lemma separationChange_magnitude (earlier later : PairState3 .P) :
    (separationChange earlier later).magnitude =
      dist (later.com .A) (later.com .B) - dist (earlier.com .A) (earlier.com .B) := by
  simp [separationChange, IndividualQuantity.add_magnitude,
    IndividualQuantity.neg_magnitude, separationOf]
  change dist (later.com .A) (later.com .B) +
      (-(dist (earlier.com .A) (earlier.com .B))) =
    dist (later.com .A) (later.com .B) - dist (earlier.com .A) (earlier.com .B)
  ring

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
example (s : PairState3 .P) :
    (ForPhysLib.Kinded.Space.distanceQ (s.com .A) (s.com .B)).magnitude =
      (ForPhysLib.Kinded.Space.lengthOf
        (ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B))).magnitude :=
  ForPhysLib.Kinded.Space.distanceQ_eq_lengthOf_displacementQ (s.com .A) (s.com .B)

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

example (s : PairState3 .P) (F G : ReferenceFrame 3) (t : Time)
    (u : EuclideanSpace ℝ (Fin 3)) :
    G.Vector × G.Vector × G.Vector :=
  let v := barePairDisplacement s F t
  (geometricTransport F G t v, boostTransport F G t u v, originShiftTransport F G t v)

example (s : PairState3 .P) (cart : ReferenceFrame 3) (hCart : cart.IsInertial) :
    EuclideanSpace ℝ (Fin 3) :=
  (s.com .A -ᵥ s.com .B) + hCart.velocity
-- ANCHOR_END: bare_frames

-- ANCHOR: kinded_frames
def pairDisplacementInFrame {π : PairId} (F : ReferenceFrame 3) (s : PairState3 π) :
    KVector F ForPhysLib.Kinds.Space.displacement :=
  ⟨⟨fun i =>
    (ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B)).magnitude i⟩⟩

def averageVelocityOfA {π : PairId} (earlier later : PairState3 π)
    (elapsed : Quantity durationK ℝ) (h : elapsed.magnitude ≠ 0) :
    Quantity velocityK (EuclideanSpace ℝ (Fin 3)) :=
  ⟨(if hzero : elapsed.magnitude = 0 then False.elim (h hzero)
    else elapsed.magnitude⁻¹) • (later.com .A -ᵥ earlier.com .A)⟩

def averageVelocityInFrame {π : PairId} (F : ReferenceFrame 3)
    (earlier later : PairState3 π) (elapsed : Quantity durationK ℝ)
    (h : elapsed.magnitude ≠ 0) : KVector F velocityK :=
  ⟨⟨fun i => (averageVelocityOfA earlier later elapsed h).magnitude i⟩⟩

example (s : PairState3 .P) (F G : ReferenceFrame 3) (t : Time) :
    KVector G ForPhysLib.Kinds.Space.displacement :=
  kGeometricTransport F G t (pairDisplacementInFrame F s)

example (earlier later : PairState3 .P) (elapsed : Quantity durationK ℝ)
    (h : elapsed.magnitude ≠ 0) (F G : ReferenceFrame 3) (t : Time)
    (u : Quantity velocityK (EuclideanSpace ℝ (Fin 3))) :
    KVector G velocityK :=
  kBoostTransport F G t u (averageVelocityInFrame F earlier later elapsed h)

/--
error: Application type mismatch: The argument
  pairDisplacementInFrame F s
has type
  KVector F displacement
but is expected to have type
  KVector F velocityK
in the application
  kBoostTransport F G t u (pairDisplacementInFrame F s)
-/
#guard_msgs (whitespace := lax) in
example (F G : ReferenceFrame 3) (t : Time)
    (u : Quantity velocityK (EuclideanSpace ℝ (Fin 3))) (s : PairState3 .P) :=
  kBoostTransport F G t u (pairDisplacementInFrame F s)

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
example (cart : ReferenceFrame 3) (hCart : cart.IsInertial) (t₁ t₂ : Time) :
    (ForPhysLib.Kinded.Space.displacementQ (cart.origin t₂) (cart.origin t₁)).magnitude =
      (elapsedQ t₁ t₂).magnitude • (frameVelocityQ hCart).magnitude :=
  origin_displacement_eq cart hCart t₁ t₂

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

lemma pairSpanArea_magnitude {π : PairId} (s : PairState3 π) (p : Space 3) :
    (pairSpanArea s p).magnitude =
      ‖(ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B)).magnitude‖ *
        ‖(ForPhysLib.Kinded.Space.displacementQ (s.com .A) p).magnitude‖ :=
  ForPhysLib.Operators.Space.spanArea_magnitude _ _

example (s : PairState3 .P) (p : Space 3) : Quantity ForPhysLib.Kinds.Space.area ℝ :=
  pairSpanArea s p

example (s : PairState3 .P) (p : Space 3) :
    (pairSpanArea s p).magnitude =
      ‖(ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B)).magnitude‖ *
        ‖(ForPhysLib.Kinded.Space.displacementQ (s.com .A) p).magnitude‖ :=
  pairSpanArea_magnitude s p

/--
error: failed to synthesize instance of type class
  HMul (Quantity area ℝ) (Quantity area ℝ) ?m.9

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (s : PairState3 .P) (p : Space 3) := pairSpanArea s p * pairSpanArea s p
-- ANCHOR_END: adoption_ladder

end
