/-
# L4 — Out of the line

Seven build-checked probes of three-dimensional positions, distances, and reference frames.

Edit this worksheet in place, build with `lake build HCP.Worksheets.L4_OutOfTheLine`,
and compare with the solution at `HCP/L4_OutOfTheLine.lean`.
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

namespace HCP.Worksheets.L4_OutOfTheLine

-- EXERCISE: pair_state_and_bearers
-- GIVEN:
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

-- TODO: attach the position and displacement values to their nominal bearers.
def bodyPositionOf {π : PairId} (s : PairState3 π) (b : BodyOf π) :
    IndividualQuantity b ForPhysLib.Kinds.Space.positionVector (EuclideanSpace ℝ (Fin 3)) := by
  sorry

def pairDisplacementOf {π : PairId} (s : PairState3 π) :
    IndividualQuantity (⟨⟩ : SeparationOf π) ForPhysLib.Kinds.Space.displacement
      (EuclideanSpace ℝ (Fin 3)) := by
  sorry
-- EXERCISE_END: pair_state_and_bearers

-- EXERCISE: points_vectors_and_distances
-- TODO: construct the well-kinded position, displacement, and distance values.
example (s : PairState3 .P) :
    Quantity ForPhysLib.Kinds.Space.positionVector (EuclideanSpace ℝ (Fin 3)) := by
  sorry

example (s : PairState3 .P) :
    Quantity ForPhysLib.Kinds.Space.displacement (EuclideanSpace ℝ (Fin 3)) := by
  sorry

example (s : PairState3 .P) : Quantity ForPhysLib.Kinds.Space.distance ℝ := by
  sorry

-- TODO: uncomment each expression and explain why the vector kinds cannot be added.
-- example (s : PairState3 .P) :=
--   ForPhysLib.Kinded.Space.positionQ (s.com .A) +
--     ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B)
-- example (s : PairState3 .P) :=
--   ForPhysLib.Kinded.Space.distanceQ (s.com .A) (s.com .B) +
--     ForPhysLib.Kinded.Space.lengthOf
--       (ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B))
-- EXERCISE_END: points_vectors_and_distances

-- EXERCISE: whose_distance
-- TODO: index distance by the pair, then prove the magnitude and change equations.
def separationOf {π : PairId} (s : PairState3 π) :
    IndividualQuantity (⟨⟩ : SeparationOf π) ForPhysLib.Kinds.Space.distance ℝ := by
  sorry

lemma separationOf_magnitude {π : PairId} (s : PairState3 π) :
    (separationOf s).magnitude = dist (s.com .A) (s.com .B) := by
  sorry

example : DifferenceKind ForPhysLib.Kinds.Space.distance := by
  sorry

def separationChange (earlier later : PairState3 .P) :
    IndividualQuantity (⟨⟩ : SeparationOf .P) ForPhysLib.Kinds.Space.distance ℝ := by
  sorry

lemma separationChange_magnitude (earlier later : PairState3 .P) :
    (separationChange earlier later).magnitude =
      dist (later.com .A) (later.com .B) - dist (earlier.com .A) (earlier.com .B) := by
  sorry

-- TODO: uncomment the cross-pair addition and explain the bearer mismatch.
-- example (p : PairState3 .P) (q : PairState3 .Q) :=
--   let qDistance : IndividualQuantity (⟨⟩ : SeparationOf .Q)
--       ForPhysLib.Kinds.Space.distance ℝ := separationOf q
--   IndividualQuantity.add DifferenceKind.ofScale (separationOf p) qDistance
-- EXERCISE_END: whose_distance

-- EXERCISE: distance_is_length
-- TODO: apply the distance-as-length theorem and the triangle inequality.
example (s : PairState3 .P) :
    (ForPhysLib.Kinded.Space.distanceQ (s.com .A) (s.com .B)).magnitude =
      (ForPhysLib.Kinded.Space.lengthOf
        (ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B))).magnitude := by
  sorry

example (s : PairState3 .P) :
    (ForPhysLib.Kinded.Space.distanceQ (s.com .A) (s.com .A)).magnitude ≤
      (ForPhysLib.Kinded.Space.distanceQ (s.com .A) (s.com .B)).magnitude +
        (ForPhysLib.Kinded.Space.distanceQ (s.com .B) (s.com .A)).magnitude := by
  sorry
-- EXERCISE_END: distance_is_length

-- EXERCISE: bare_frames
-- TODO: build the bare frame conversion and explain what the vector type leaves unspecified.
def barePairDisplacement {π : PairId} (s : PairState3 π)
    (F : ReferenceFrame 3) (t : Time) : F.Vector := by
  sorry

example (s : PairState3 .P) (F G : ReferenceFrame 3) (t : Time)
    (u : EuclideanSpace ℝ (Fin 3)) :
    G.Vector × G.Vector × G.Vector := by
  sorry

-- TODO: explain why an unframed vector can combine with the cart velocity.
example (s : PairState3 .P) (cart : ReferenceFrame 3) (hCart : cart.IsInertial) :
    EuclideanSpace ℝ (Fin 3) :=
  (s.com .A -ᵥ s.com .B) + hCart.velocity
-- EXERCISE_END: bare_frames

-- EXERCISE: kinded_frames
-- TODO: carry the frame and vector kind through displacement and velocity conversions.
def pairDisplacementInFrame {π : PairId} (F : ReferenceFrame 3) (t : Time)
    (s : PairState3 π) :
    KVector F ForPhysLib.Kinds.Space.displacement := by
  sorry

def averageVelocityOfA {π : PairId} (earlier later : PairState3 π)
    (elapsed : Quantity durationK ℝ) (h : elapsed.magnitude ≠ 0) :
    Quantity velocityK (EuclideanSpace ℝ (Fin 3)) := by
  sorry

def averageVelocityInFrame {π : PairId} (F : ReferenceFrame 3) (t : Time)
    (earlier later : PairState3 π) (elapsed : Quantity durationK ℝ)
    (h : elapsed.magnitude ≠ 0) : KVector F velocityK := by
  sorry

example (s : PairState3 .P) (F G : ReferenceFrame 3) (t : Time) :
    KVector G ForPhysLib.Kinds.Space.displacement := by
  sorry

theorem pairDisplacement_observer_independent {π : PairId}
    (F G : ReferenceFrame 3) (t : Time) (s : PairState3 π) :
    kGeometricTransport F G t (pairDisplacementInFrame F t s) =
      pairDisplacementInFrame G t s := by
  sorry

example (earlier later : PairState3 .P) (elapsed : Quantity durationK ℝ)
    (h : elapsed.magnitude ≠ 0) (F G : ReferenceFrame 3) (t : Time)
    (u : Quantity velocityK (EuclideanSpace ℝ (Fin 3))) :
    KVector G velocityK := by
  sorry

-- TODO: uncomment each expression and describe the kind mismatch.
-- example (F G : ReferenceFrame 3) (t : Time)
--     (u : Quantity velocityK (EuclideanSpace ℝ (Fin 3))) (s : PairState3 .P) :=
--   kBoostTransport F G t u (pairDisplacementInFrame F t s)
-- example (F : ReferenceFrame 3) (v : KVector F velocityK) (force : KVector F forceK) :=
--   v + force
-- EXERCISE_END: kinded_frames

-- EXERCISE: observer_motion
-- TODO: apply the origin-displacement theorem and inspect the rejected mixed-kind sum.
example (cart : ReferenceFrame 3) (hCart : cart.IsInertial) (t₁ t₂ : Time) :
    (ForPhysLib.Kinded.Space.displacementQ (cart.origin t₂) (cart.origin t₁)).magnitude =
      (elapsedQ t₁ t₂).magnitude • (frameVelocityQ hCart).magnitude := by
  sorry

-- TODO: uncomment the expression that adds displacement and velocity.
-- example (s : PairState3 .P) (cart : ReferenceFrame 3) (hCart : cart.IsInertial) :=
--   ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B) + frameVelocityQ hCart
-- EXERCISE_END: observer_motion

-- EXERCISE: adoption_ladder
-- TODO: construct the span area, prove its magnitude, and explain why area cannot multiply itself.
def pairSpanArea {π : PairId} (s : PairState3 π) (p : Space 3) :
    Quantity ForPhysLib.Kinds.Space.area ℝ := by
  sorry

lemma pairSpanArea_magnitude {π : PairId} (s : PairState3 π) (p : Space 3) :
    (pairSpanArea s p).magnitude =
      ‖(ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B)).magnitude‖ *
        ‖(ForPhysLib.Kinded.Space.displacementQ (s.com .A) p).magnitude‖ := by
  sorry

example (s : PairState3 .P) (p : Space 3) :
    Quantity ForPhysLib.Kinds.Space.area ℝ := by
  sorry

example (s : PairState3 .P) (p : Space 3) :
    (pairSpanArea s p).magnitude =
      ‖(ForPhysLib.Kinded.Space.displacementQ (s.com .A) (s.com .B)).magnitude‖ *
        ‖(ForPhysLib.Kinded.Space.displacementQ (s.com .A) p).magnitude‖ := by
  sorry

-- TODO: uncomment the repeated-area product and read the kind error.
-- example (s : PairState3 .P) (p : Space 3) := pairSpanArea s p * pairSpanArea s p
-- EXERCISE_END: adoption_ladder

end HCP.Worksheets.L4_OutOfTheLine

end
