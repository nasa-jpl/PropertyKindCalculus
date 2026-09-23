/-
# Validation probes — frames and variance (R20)

Inhabitation and axiom-profile probes for the structural half of value representation: the
frame index, the variance index, and what survives a change of frame.

**The non-vacuity boundary here is the rotation.** `dot_toFrameVector` is easy to satisfy
*vacuously* with the identity change of frame, which is orthonormal and moves nothing — the
theorem would then be exercised on a case where both sides are the same expression. The
witness below is therefore a rotation that genuinely mixes: the Pythagorean turn
`cos θ = 3/5`, `sin θ = 4/5` applied to `v = (3, 4)` gives `(−7/5, 24/5)`, so **both**
components change, and `#guard`-style equalities on them are `norm_num`-decidable because
every entry is rational. The invariance is then applied where the components have actually
moved, and `component_not_invariant`'s companion probe shows the same rotation changing a
component — the two together are the requirement.

The other boundary is the scalar gate. `Quantity.mul` at a numerical-array carrier is the
error R20 exists downstream of (a Hadamard product signed as a product of kinds), and the
probe for it is a `#check_failure`: the absence of `ScalarCarrier (Fin 2 → ℝ)` is what makes
the ill-formed term fail to elaborate, so a regression that added such an instance would
show up here rather than as a wrong answer somewhere else.
-/

module

public import PropertyKindCalculus.FrameReal
meta import PropertyKindCalculus.FrameReal
-- Private scope only: the checks below reduce through bodies sealed in the core
-- library; `import all` gives this file the reduction without exposing them.
import all PropertyKindCalculus.Frame

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Tests.Frames

open PropertyKindCalculus

/-- Velocity, a ratio kind. -/
def velK : KindOfProperty := { id := "velocity", scale := .ratio }
/-- Speed squared, the kind a velocity contracted with itself lands at. -/
def speedSqK : KindOfProperty := { id := "speed squared", scale := .ratio }
theorem vv : ProductKind velK velK speedSqK := ProductKind.ofRatio _ _ _

/-- The laboratory frame. -/
def lab : Frame := { id := "laboratory" }
/-- A frame rotated relative to it. -/
def rot : Frame := { id := "rotated" }

/-- The Pythagorean rotation `[[3/5, −4/5], [4/5, 3/5]]` — orthonormal, rational, and *not*
the identity, which is what makes the probes below non-vacuous. -/
noncomputable def turn : FrameChange 2 ℝ lab rot :=
  ⟨fun i j => if i = 0 then (if j = 0 then 3/5 else -(4/5))
              else (if j = 0 then 4/5 else 3/5)⟩

theorem turn_isOrthonormal : turn.IsOrthonormal := by
  rw [isOrthonormal_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [turn, Fin.sum_univ_succ] <;> norm_num

/-- A velocity `(3, 4)`, read in the laboratory frame. -/
noncomputable def vLab : InFrame lab .vector velK (Fin 2 → ℝ) :=
  ⟨⟨fun i => if i = 0 then 3 else 4⟩⟩

/-- The same velocity read in the rotated frame. -/
noncomputable def vRot : InFrame rot .vector velK (Fin 2 → ℝ) :=
  InFrame.toFrameVector turn vLab

/-! ## The rotation genuinely moves both components

Without these two facts the invariance probe below would be vacuous. -/

theorem vRot_zero : vRot.components 0 = -(7/5) := by
  simp [vRot, vLab, InFrame.toFrameVector, FrameChange.mulVec, InFrame.components, turn, sumFin]
  norm_num

theorem vRot_one : vRot.components 1 = 24/5 := by
  simp [vRot, vLab, InFrame.toFrameVector, FrameChange.mulVec, InFrame.components, turn, sumFin]
  norm_num

/-! ## R20 — inhabitation

The capstone applied to a concrete non-identity orthonormal change: the contraction agrees
across frames even though neither component does. -/

theorem r20_dot_invariant :
    (InFrame.dot vv vRot vRot).components = (InFrame.dot vv vLab vLab).components :=
  dot_toFrameVector turn_isOrthonormal vv vLab vLab

/-- And the shared value is `3² + 4² = 25`, so the equality above is between two computations
that both had to happen rather than between two copies of one expression. -/
theorem r20_dot_value : (InFrame.dot vv vLab vLab).components = 25 := by
  simp [InFrame.dot, InFrame.components, vLab]
  norm_num

/-- The other half, on the same witness: a component is not invariant. -/
theorem r20_component_moves : vRot.components 0 ≠ vLab.components 0 := by
  rw [vRot_zero]
  simp [vLab, InFrame.components]
  norm_num

/-! ## R20 — the frame index does its job

Two readings of one quantity in two frames have different types, so their sum is not a wrong
answer but a non-expression. Likewise the variance index: the vector law does not apply to a
scalar reading. -/

#check_failure (InFrame.add (DifferenceKind.ofScale) vLab vRot)
#check_failure (fun (m : InFrame lab .scalar velK ℝ) => InFrame.toFrameVector turn m)

/-! ## R20 — the scalar gate

`Quantity.mul` at a numerical-array carrier would sign the componentwise product as a product
of kinds. The absence of `ScalarCarrier (Fin 2 → ℝ)` is what refuses it. -/

#check_failure (fun (x y : Quantity velK (Fin 2 → ℝ)) => Quantity.mul vv x y)

/-- And the gate is not a blanket refusal — the scalar carriers still multiply. -/
noncomputable example (x y : Quantity velK ℝ) : Quantity speedSqK ℝ := Quantity.mul vv x y

/-! ## Axiom profiles

A proof silently relocated behind a `sorry` emits no warning on its caller; only the axiom set
reveals it. -/

/-- info: 'PropertyKindCalculus.dot_toFrameVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dot_toFrameVector

/-- info: 'PropertyKindCalculus.normSq_toFrameVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms normSq_toFrameVector

/-- info: 'PropertyKindCalculus.toFrameVector_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms toFrameVector_id

/-- info: 'PropertyKindCalculus.toFrameVector_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms toFrameVector_comp

/-- info: 'PropertyKindCalculus.component_not_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms component_not_invariant

/-- info: 'PropertyKindCalculus.sumFin_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sumFin_eq_sum

end PropertyKindCalculus.Tests.Frames

end -- pkc-blanket-expose
end -- pkc-blanket
