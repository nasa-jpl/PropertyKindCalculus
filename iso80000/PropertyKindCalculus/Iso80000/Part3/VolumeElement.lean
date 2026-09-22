/-
# ISO 80000-3 item 3-4 (volume) — the volume element, formalized analytically

The *Remarks* field of the volume item gives the **volume element** of a region in
terms of its (Gaussian) coordinates and the determinant `g` of the metric tensor
(ISO 80000-2). This module captures that content analytically — as real
differential-geometric objects with proved properties — and ties them back to the
catalogued volume quantity-kind `Part3.volume`. It is the three-dimensional analogue
of `Part3.AreaElement` (the surface element of item 3-3): the same Gram-determinant
construction, raised from a `2 × 2` to a `3 × 3` metric tensor.

No normative text or formula from the licensed standard is reproduced; the relation
is restated in this work's own formalism, on Mathlib's Gram-matrix and
change-of-variables machinery.

## What is formalized

  * `metricTensor t` — the **metric tensor** of a 3-parameter region: the `3 × 3`
    Gram matrix `⟪tᵢ, tⱼ⟫` of the three tangent vectors `t 0, t 1, t 2`.
  * `metricDet t` — `g`, its **determinant**.
  * `volumeElement t = √g` — the **volume element** density.
  * `regionVolume t s = ∭_s √g du dv dw` — the **volume** as its integral.

## What is proved

  * the metric tensor is symmetric and positive-semidefinite, so `g ≥ 0`;
  * `(dV)² = g`;
  * `dV > 0` exactly when the tangent frame is non-degenerate (a regular point);
  * the **correctness anchor** `volumeElement_eq_abs_det`: for a flat region the
    element equals `|det A|` (the change-of-variables volume density), so the formula
    computes the *actual* Euclidean volume;
  * `regionVolume_const`: a uniformly-parametrized region has volume `= element ×
    (volume of the parameter region)`.
-/

module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import PropertyKindCalculus.Iso80000.Part3

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Iso80000.Part3.VolumeElement

open Matrix MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The metric tensor, its determinant, and the volume element -/

/-- The **metric tensor** of a 3-parameter region at a point, given the three
tangent vectors `t 0, t 1, t 2`: the `3 × 3` Gram matrix `⟪tᵢ, tⱼ⟫`. -/
def metricTensor (t : Fin 3 → E) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.gram ℝ t

/-- `g` — the **determinant of the metric tensor**. -/
def metricDet (t : Fin 3 → E) : ℝ := (metricTensor t).det

/-- The **volume element** `dV = √g`: the volume-element density at the point. The
square root is what makes a flat region recover its Euclidean volume
(`volumeElement_eq_abs_det`). -/
noncomputable def volumeElement (t : Fin 3 → E) : ℝ := Real.sqrt (metricDet t)

/-! ## Properties of the metric tensor -/

/-- The metric tensor is **symmetric**. -/
theorem metricTensor_isHermitian (t : Fin 3 → E) : (metricTensor t).IsHermitian :=
  Matrix.isHermitian_gram ℝ t

/-- `g ≥ 0` — the determinant of the metric tensor is non-negative (a Gram matrix is
positive-semidefinite). -/
theorem metricDet_nonneg (t : Fin 3 → E) : 0 ≤ metricDet t :=
  (Matrix.posSemidef_gram ℝ t).det_nonneg

/-- The volume element is non-negative. -/
theorem volumeElement_nonneg (t : Fin 3 → E) : 0 ≤ volumeElement t := Real.sqrt_nonneg _

/-- `(dV)² = g` — the volume element squares back to the determinant of the metric
tensor: the `√` in `dV = √g` is faithful. -/
theorem volumeElement_sq (t : Fin 3 → E) : volumeElement t ^ 2 = metricDet t :=
  Real.sq_sqrt (metricDet_nonneg t)

/-- **Regularity.** The volume element is strictly positive exactly when the three
tangent vectors are linearly independent — a non-degenerate (regular) point of the
parametrization. A vanishing element marks a degenerate parametrization. -/
theorem volumeElement_pos_iff (t : Fin 3 → E) :
    0 < volumeElement t ↔ LinearIndependent ℝ t := by
  rw [volumeElement, Real.sqrt_pos]
  unfold metricDet metricTensor
  constructor
  · intro h
    exact det_gram_ne_zero_iff_linearIndependent.mp (ne_of_gt h)
  · intro h
    exact lt_of_le_of_ne (Matrix.posSemidef_gram ℝ t).det_nonneg
      (Ne.symm (det_gram_ne_zero_iff_linearIndependent.mpr h))

/-! ## Correctness anchor: a flat region recovers its Euclidean volume -/

/-- In Euclidean 3-space, `g` equals the square of the parametrization Jacobian's
determinant: `g = (det A)²`, where `A` is the matrix whose columns are the tangent
vectors. -/
theorem metricDet_eq_det_sq (t : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    metricDet t = (Matrix.of fun i j => t j i).det ^ 2 := by
  have hb := Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin 3) ℝ) t
  simp only [EuclideanSpace.basisFun_repr] at hb
  rw [metricDet, metricTensor, hb, Matrix.det_mul, Matrix.det_conjTranspose,
    star_trivial, sq]

/-- **The element is the change-of-variables volume density.** For a flat region the
volume element equals `|det A|` — so `dV = |det A| du dv dw` integrates to the
*actual* Euclidean volume, confirming the `√g` reading. -/
theorem volumeElement_eq_abs_det (t : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    volumeElement t = |(Matrix.of fun i j => t j i).det| := by
  rw [volumeElement, metricDet_eq_det_sq, Real.sqrt_sq_eq_abs]

/-! ## Volume as the integral of the volume element -/

/-- The **volume of a parametrized region** (ISO 80000-3, 3-4: `V = ∭ √g du dv dw`):
the integral of the volume element over the parameter region `s ⊆ ℝ³`, where `t x` is
the tangent frame at the parameter point `x`. -/
noncomputable def regionVolume (t : ℝ × ℝ × ℝ → Fin 3 → E) (s : Set (ℝ × ℝ × ℝ)) : ℝ :=
  ∫ x in s, volumeElement (t x)

/-- A uniformly-parametrized (constant-frame) region has volume `= volume element ×
volume of the parameter region` — the integral of a constant element. -/
theorem regionVolume_const (t : Fin 3 → E) (s : Set (ℝ × ℝ × ℝ)) :
    regionVolume (fun _ => t) s = (MeasureTheory.volume s).toReal • volumeElement t := by
  rw [regionVolume, setIntegral_const, MeasureTheory.measureReal_def]

/-! ## Connection to the catalogued volume quantity-kind (item 3-4)

`regionVolume` produces magnitudes of the catalogued quantity-kind `Part3.volume`
(dimension `L³`, by `Part3.volume_dim_length`), measured in `Part3.cubicMetre`. The
analytic element above is the *defining relation* behind that kind. -/

/-- The catalogued volume quantity-kind whose magnitudes `regionVolume` computes. -/
abbrev kind : DimensionedKind := Part3.volume

end PropertyKindCalculus.Iso80000.Part3.VolumeElement

end -- pkc-blanket-expose
end -- pkc-blanket
