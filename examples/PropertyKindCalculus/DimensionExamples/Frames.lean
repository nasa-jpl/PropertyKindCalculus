/-
# Worked examples — frames and variance (R20)

ISO 80000-2 §18 says two things about a vector quantity. The first is numerical — a numerical
vector times one scalar unit — and is R11, worked in
`PropertyKindCalculus.Examples.MiniVectorQuantity`. The second is the one this module works:
the quantity is independent of the choice of coordinate system while its components are not.

The scenario is a planar rover reading its velocity in two frames — the lab frame it was
surveyed in, and a frame turned a quarter turn from it. Four checked facts, in the order that
makes the requirement rather than a slogan:

  1. The quarter turn **is** orthonormal, so the invariance results apply to it — the
     hypothesis is discharged, not assumed.
  2. The **kinetic-energy contraction is invariant**: `v · v` read in the turned frame equals
     `v · v` read in the lab frame. This is the sense in which the choice of coordinates does
     not change the physics.
  3. A **component is not invariant**, exhibited with the vector that shows it. Without this
     the previous fact reads as "nothing changes", which is false and is exactly the
     over-reading a per-component discipline invites.
  4. A **scalar reading needs no hypothesis at all** — it is invariant definitionally, no
     matrix consulted. The contrast is the point: the vector's invariance is a theorem *with*
     an orthonormality hypothesis, and the scalar's is not a theorem.

Over `ℝ`, because the invariance laws need ring reasoning; the frame and variance indices
themselves are Mathlib-free (`Frame`) and run at `Float`.
-/

module

public import PropertyKindCalculus.FrameReal

@[expose] public section Blanket

namespace PropertyKindCalculus.DimensionExamples.Frames

open PropertyKindCalculus

/-! ## Two frames and one kind -/

/-- The frame the rover was surveyed in. -/
def lab : Frame := { id := "lab" }

/-- A frame turned a quarter turn from the lab frame. -/
def turned : Frame := { id := "turned" }

/-- Velocity — one kind, whichever frame its components are read in. -/
def velocity : KindOfProperty := { id := "velocity", scale := .ratio }

/-- The kind a velocity contracted with a velocity lands at: a specific energy, the `v·v` of
`½ m (v·v)` with the mass not yet applied. -/
def specificEnergy : KindOfProperty := { id := "specific energy", scale := .ratio }

/-- The contraction law: velocity × velocity is a specific energy. -/
theorem hContract : ProductKind velocity velocity specificEnergy := .ofRatio _ _ _

/-- The rover's velocity, read in the lab frame: two components, one quantity. -/
noncomputable def v : InFrame lab .vector velocity (Fin 2 → ℝ) := ⟨⟨![2, 1]⟩⟩

/-! ## (1) The change of frame is orthonormal — the hypothesis, discharged -/

/-- The quarter turn between the two frames. -/
noncomputable def turn : FrameChange 2 ℝ lab turned := quarterTurn lab turned

/-- It is orthonormal, so the invariance results below apply to it. -/
theorem turn_isOrthonormal : turn.IsOrthonormal := quarterTurn_isOrthonormal lab turned

/-! ## (2) The contraction is invariant — what the model actually asserts -/

/-- **`v · v` does not move.** The specific energy read in the turned frame is the specific
energy read in the lab frame — the same number, from different components. -/
theorem contraction_invariant :
    (InFrame.dot hContract (InFrame.toFrameVector turn v) (InFrame.toFrameVector turn v)).components
      = (InFrame.dot hContract v v).components :=
  dot_toFrameVector turn_isOrthonormal hContract v v

/-- The squared-magnitude form, which is the shape a kinetic energy actually takes. -/
example :
    (InFrame.normSq hContract (InFrame.toFrameVector turn v)).components
      = (InFrame.normSq hContract v).components :=
  normSq_toFrameVector turn_isOrthonormal hContract v

/-! ## (3) A component *is* not invariant — the over-reading, refused -/

/-- **A component moves.** Some velocity read in the lab frame has a first component the
turned frame does not agree with. One quantity, two frames — not two quantities — which is
why a per-component discipline cannot be a metrological guarantee. -/
theorem component_moves :
    ∃ x : InFrame lab .vector velocity (Fin 2 → ℝ),
      (InFrame.toFrameVector turn x).components 0 ≠ x.components 0 :=
  component_not_invariant lab turned velocity

/-! ## (4) A scalar reading is invariant with nothing assumed -/

/-- **No hypothesis, no proof.** A scalar-variance quantity has no basis index for the
transition matrix to act on, so its reading is unchanged definitionally — orthonormality is
never consulted. That is the contrast that makes (2) informative. -/
example (m : InFrame lab .scalar velocity ℝ) :
    (InFrame.toFrameScalar (g := turned) m).components = m.components :=
  toFrameScalar_components' m

end PropertyKindCalculus.DimensionExamples.Frames

end Blanket
