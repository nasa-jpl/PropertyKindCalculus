/-
# ISO 80000-3 item 3-2.1 (area) — the surface element, formalized analytically

The *Remarks* field of the area item gives the **surface element** of a surface in
terms of its Gaussian coordinates `(u, v)` and the determinant `g` of the metric
tensor (ISO 80000-2) at the point. This module captures that mathematical content
analytically — not as prose, and not merely as a dimensional annotation, but as real
differential-geometric objects with proved properties — and ties them back to the
catalogued area quantity-kind `Part3.area`.

No normative text or formula from the licensed standard is reproduced; the relation
is restated in this work's own formalism, built on Mathlib's Gram-matrix and
change-of-variables machinery.

## What is formalized

  * `firstFundamentalForm t` — the **metric tensor** at a point: the `2 × 2` Gram
    matrix `⟪tᵢ, tⱼ⟫` of the two tangent vectors `t 0 = ∂r/∂u`, `t 1 = ∂r/∂v` (its
    entries are the classical `E, F, G`).
  * `metricDet t` — `g`, the **determinant** of the metric tensor (`= E·G − F²`).
  * `areaElement t = √g` — the **surface element** density.
  * `surfaceArea t s = ∬_s √g du dv` — the **area** as the integral of the element.

## What is proved

  * the metric tensor is symmetric and positive-semidefinite, so `g ≥ 0`;
  * `(dA)² = g` — the element squares back to the determinant of the metric tensor;
  * `dA > 0` exactly when the tangent frame is non-degenerate (a *regular* point);
  * the **correctness anchor** `areaElement_eq_abs_det`: for a flat patch the element
    equals `|det A|` (the change-of-variables area density), so the formula computes
    the *actual* area;
  * `surfaceArea_const`: a uniformly-parametrized patch has area `= element × (area of
    the parameter region)`.

A note on `√`: the standard writes the element with the determinant `g`; the
area-consistent Riemannian element is `√g` (only then does a flat patch recover its
Euclidean area, `areaElement_eq_abs_det`). Formalization forces this convention into
the open — exactly the kind of implicit reading a prose remark leaves unstated.
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

namespace PropertyKindCalculus.Iso80000.Part3.AreaElement

open Matrix MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The metric tensor, its determinant, and the surface element -/

/-- The **first fundamental form** (the *metric tensor* of ISO 80000-2) of a surface
at a point, given the two tangent vectors `t 0 = ∂r/∂u`, `t 1 = ∂r/∂v`: the `2 × 2`
Gram matrix `⟪tᵢ, tⱼ⟫`. Its entries are the classical coefficients `E = ⟪t₀,t₀⟫`,
`F = ⟪t₀,t₁⟫`, `G = ⟪t₁,t₁⟫`. -/
def firstFundamentalForm (t : Fin 2 → E) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.gram ℝ t

/-- `g` — the **determinant of the metric tensor** (`= E·G − F²`). -/
def metricDet (t : Fin 2 → E) : ℝ := (firstFundamentalForm t).det

/-- The **surface element** `dA = √g`: the area-element density at the point. The
square root is what makes a flat patch recover its Euclidean area
(`areaElement_eq_abs_det`). -/
noncomputable def areaElement (t : Fin 2 → E) : ℝ := Real.sqrt (metricDet t)

/-! ## Properties of the metric tensor -/

/-- The metric tensor is **symmetric** (`F = ⟪t₀,t₁⟫ = ⟪t₁,t₀⟫`). -/
theorem firstFundamentalForm_isHermitian (t : Fin 2 → E) :
    (firstFundamentalForm t).IsHermitian :=
  Matrix.isHermitian_gram ℝ t

/-- `g ≥ 0` — the determinant of the metric tensor is non-negative, because the metric
tensor is positive-semidefinite (a Gram matrix). -/
theorem metricDet_nonneg (t : Fin 2 → E) : 0 ≤ metricDet t :=
  (Matrix.posSemidef_gram ℝ t).det_nonneg

/-- The surface element is non-negative. -/
theorem areaElement_nonneg (t : Fin 2 → E) : 0 ≤ areaElement t := Real.sqrt_nonneg _

/-- `(dA)² = g` — the surface element squares back to the determinant of the metric
tensor: the `√` in `dA = √g` is faithful. -/
theorem areaElement_sq (t : Fin 2 → E) : areaElement t ^ 2 = metricDet t :=
  Real.sq_sqrt (metricDet_nonneg t)

/-- **Regularity.** The surface element is strictly positive exactly when the two
tangent vectors are linearly independent — i.e. at a non-degenerate (regular) point of
the parametrization. A vanishing element marks a degenerate parametrization. -/
theorem areaElement_pos_iff (t : Fin 2 → E) :
    0 < areaElement t ↔ LinearIndependent ℝ t := by
  rw [areaElement, Real.sqrt_pos]
  unfold metricDet firstFundamentalForm
  constructor
  · intro h
    exact det_gram_ne_zero_iff_linearIndependent.mp (ne_of_gt h)
  · intro h
    exact lt_of_le_of_ne (Matrix.posSemidef_gram ℝ t).det_nonneg
      (Ne.symm (det_gram_ne_zero_iff_linearIndependent.mpr h))

/-! ## Correctness anchor: a flat patch recovers its Euclidean area -/

/-- In the plane (a surface lying in `ℝ²`), `g` equals the square of the
parametrization Jacobian's determinant: `g = (det A)²`, where `A` is the matrix whose
columns are the tangent vectors. -/
theorem metricDet_eq_det_sq (t : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    metricDet t = (Matrix.of fun i j => t j i).det ^ 2 := by
  have hb := Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin 2) ℝ) t
  simp only [EuclideanSpace.basisFun_repr] at hb
  rw [metricDet, firstFundamentalForm, hb, Matrix.det_mul, Matrix.det_conjTranspose,
    star_trivial, sq]

/-- **The element is the change-of-variables area density.** For a flat patch the
surface element equals `|det A|` — so `dA = |det A| du dv` integrates to the *actual*
area, confirming the `√g` reading against the Euclidean area it must reproduce. -/
theorem areaElement_eq_abs_det (t : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    areaElement t = |(Matrix.of fun i j => t j i).det| := by
  rw [areaElement, metricDet_eq_det_sq, Real.sqrt_sq_eq_abs]

/-! ## Area as the integral of the surface element -/

/-- The **area of a parametrized surface patch** (ISO 80000-3, 3-2.1: `A = ∬ √g du dv`):
the integral of the surface element over the parameter region `s ⊆ ℝ²`, where `t x` is
the tangent frame `(∂r/∂u, ∂r/∂v)` at the parameter point `x`. -/
noncomputable def surfaceArea (t : ℝ × ℝ → Fin 2 → E) (s : Set (ℝ × ℝ)) : ℝ :=
  ∫ x in s, areaElement (t x)

/-- A uniformly-parametrized (constant-frame) patch has area `= surface element × area
of the parameter region` — the integral of a constant element. (`MeasureTheory.volume`
is named in full because `Part3.volume` is the catalogued volume kind in scope here.) -/
theorem surfaceArea_const (t : Fin 2 → E) (s : Set (ℝ × ℝ)) :
    surfaceArea (fun _ => t) s = (MeasureTheory.volume s).toReal • areaElement t := by
  rw [surfaceArea, setIntegral_const, MeasureTheory.measureReal_def]

/-! ## Connection to the catalogued area quantity-kind (item 3-2.1)

`surfaceArea` produces magnitudes of the catalogued quantity-kind `Part3.area`
(dimension `L²`, by `Part3.area_dim_length`), measured in `Part3.squareMetre`. The
analytic element above is the *defining relation* behind that kind: every concrete
surface area is a value of this one kind, and `area.dim.length = 2` is the kind-level
invariant every such value carries — the link this module makes explicit between the
remark's mathematics and the catalogued kind. -/

/-- The catalogued area quantity-kind whose magnitudes `surfaceArea` computes. -/
abbrev kind : DimensionedKind := Part3.area

end PropertyKindCalculus.Iso80000.Part3.AreaElement

end -- pkc-blanket-expose
end -- pkc-blanket
