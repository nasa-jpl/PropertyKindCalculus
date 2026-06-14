/-
# Worked examples — ISO 80000-3 (Space and time)

Part-3 examples, mirroring the `Iso80000` library's own `Iso80000/Part3` layout:

1. the dimensional algebra and unit facts of the Part-3 seed (length is `L`, area is
   `L²`, speed is `L·T⁻¹`; the metre well-formed; commensurability "of the same kind");
2. **ISO 80000-2 §18** — a *vector* quantity (displacement, item 3-1.11) as a numerical
   array × **one scalar unit**, with the additivity laws transferring to the vector
   carrier by the *same* parametric proof used for scalars (the R10 reading of §18);
3. from item 3-2.1's surface-element remark to quantity **classification** and
   **metrological consistency** at the quantity level;
4. **verified classification (R12)** — area certificates.

Series-wide catalogue examples are in the sibling
`PropertyKindCalculus.DimensionExamples.Iso80000.References`.
-/

import PropertyKindCalculus.Iso80000
import PropertyKindCalculus.Iso80000.Part3.AreaElement
import PropertyKindCalculus.Iso80000.Part3.AreaClassification
import PropertyKindCalculus.QuantityReal
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

namespace PropertyKindCalculus.Examples.Iso80000.Part3

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open PropertyKindCalculus.Iso80000.Part3
open PropertyKindCalculus.Iso80000.Part3.AreaElement
open PropertyKindCalculus.Iso80000.Part3.AreaClassification

/-! ## (1) ISO 80000-3 — Space and time (the seed) -/

-- the dimensional algebra is a checked computation, not an annotation
example : length.dim = Dim.length := length_dim
example : area.dim.length = 2 := area_dim_length
example : speed.dim = Dim.length / Dim.time := speed_dim

-- each kind carries its exact item citation as data
#guard lengthCK.item == "3-1.1"
#guard lengthCK.cite == "ISO 80000-3, Second edition, 2019-10 item 3-1.1"
#guard speedCK.item == "3-10.2"

-- the metre is a well-formed unit; commensurability is "of the same kind"
example : metre.WellFormed := metre_wellFormed
example : metre.Commensurable centimetre := metre_centimetre_commensurable
example : ¬ metre.Commensurable second := metre_second_not_commensurable

/-! ## (2) ISO 80000-2 §18 — a vector quantity as numerical array × scalar unit

A displacement (ISO 80000-3 item 3-1.11). §18's own example is a force,
`(Fₓ, F_y, F_z) = (−31.5, 43.2, 17.0) N` — one unit `N` for the whole vector. -/

/-- The displacement as a single kind-`displacement` quantity whose magnitude is a
*numerical* 3-vector — not three separate `(number × unit)` coordinate values. -/
noncomputable def d : Quantity displacement.kind (Fin 3 → ℝ) := ⟨![3.0, 4.0, 0.0]⟩

/-- The unit of a vector quantity is a single **scalar** of its kind (one metre for
the whole vector), and it is well-formed. -/
def displacementMetre : MetrologicalUnit := displacement.kind.unit "m"
example : displacementMetre.WellFormed := KindOfProperty.rational_bears_unit rfl

-- the additivity laws hold over the vector carrier `Fin 3 → ℝ` by the SAME
-- parametric proof used for scalars (adding displacements is componentwise)
example (x y : Quantity displacement.kind (Fin 3 → ℝ)) :
    Quantity.add x y = Quantity.add y x :=
  Quantity.add_comm x y

example (x y z : Quantity displacement.kind (Fin 3 → ℝ)) :
    Quantity.add x y = Quantity.add y x
      ∧ Quantity.add (Quantity.add x y) z = Quantity.add x (Quantity.add y z)
      ∧ Quantity.add Quantity.zero x = x ∧ Quantity.add x Quantity.zero = x :=
  Quantity.laws_parametric x y z

/-- An `Int`-valued displacement, for an executable witness: componentwise addition
computes (the middle component `5 + 5 = 10`). -/
def vInt : Quantity displacement.kind (Fin 3 → Int) := ⟨![4, 5, 6]⟩
#guard (Quantity.add vInt vInt).magnitude 1 == 10

/-! ## (3) From a remark's mathematics to quantity classification and consistency

ISO 80000-3 item 3-2.1 defines area through a surface element `dA = √g du dv`
(formalized in `Part3.AreaElement`). Formalizing that *defining relation*, rather than
leaving it as prose, does two things for the quantity-kind `area`:

* **it anchors the kind** — the geometry's output is, by construction, a magnitude of
  `area`; every surface area is one value of this *one* kind; and
* **it makes the kind a classifier with teeth** — because `area` carries the dimension
  `L²` and a scalar unit of its own, the type system refuses to combine an area with a
  length, or to measure it in metres. Consistency is checked at the *quantity* level,
  by the kind, not by convention or by a runtime guard.

This is what "the quantity-kind level formalization verifies metrological consistency
at the quantity level" means concretely. -/

-- (a) The formalized remark, as checked facts: the surface element squares back to the
-- determinant of the metric tensor, and for a flat patch it equals `|det A|` — the
-- change-of-variables area density, so the formula computes the *actual* area.
example (t : Fin 2 → EuclideanSpace ℝ (Fin 2)) : areaElement t ^ 2 = metricDet t :=
  areaElement_sq t
example (t : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    areaElement t = |(Matrix.of fun i j => t j i).det| :=
  areaElement_eq_abs_det t

-- (b) CLASSIFICATION: the output of the geometric formula is a value of the *one* area
-- kind — a surface area, classified by `area`, carried in `ℝ`.
noncomputable def surfaceAreaQuantity (t : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    Quantity area.kind ℝ := ⟨areaElement t⟩

-- (c) The kind classifies every such value as `L²` — the dimensional invariant it carries.
example : area.dim.length = 2 := area_dim_length

-- (d) METROLOGICAL CONSISTENCY at the quantity level.
-- Two areas (same kind) combine — `Quantity.add` is defined on the area carrier …
example (t u : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    Quantity.add (surfaceAreaQuantity t) (surfaceAreaQuantity u)
      = Quantity.add (surfaceAreaQuantity u) (surfaceAreaQuantity t) :=
  Quantity.add_comm _ _

-- … but an area is NOT a length: the kinds differ, so `Quantity area.kind ℝ` and
-- `Quantity length.kind ℝ` are *different types*. Writing
-- `Quantity.add (surfaceAreaQuantity t) (lengthQuantity)` does not typecheck — the
-- conflation a dimensionless numeric model would silently allow is rejected here.
example : area.kind ≠ length.kind := by unfold area length; decide

-- And an area is not measurable in metres: the square metre and the metre are not
-- commensurable — a type-level fact, not a runtime check.
example : ¬ squareMetre.Commensurable metre := by
  unfold MetrologicalUnit.Commensurable squareMetre metre area length KindOfProperty.unit
  decide

-- The SI unit of these areas is the square metre, a well-formed unit of `area`.
example : squareMetre.WellFormed := KindOfProperty.rational_bears_unit rfl

-- The integral form: a uniformly-parametrized patch's area is the surface element
-- times the area of its parameter region (ISO 80000-3, 3-2.1: `A = ∬ √g du dv`).
example (t : Fin 2 → EuclideanSpace ℝ (Fin 2)) (s : Set (ℝ × ℝ)) :
    surfaceArea (fun _ => t) s = (MeasureTheory.volume s).toReal • areaElement t :=
  surfaceArea_const t s

/-! ## (4) Verified classification (R12): area certificates

A quantity is classified under a kind by a *certificate* that it satisfies the kind's
defining relation, not by a bare tag. -/

-- a rectangle's area = width × height, verified-classified as an area BY CONSTRUCTION
noncomputable def rect : Quantity area.kind ℝ := rectangleArea ⟨3⟩ ⟨4⟩

-- the product certificate holds by construction, and the magnitude is 3 × 4 = 12
example : rect.IsProduct area_is_length_times_length ⟨3⟩ ⟨4⟩ := rfl
example : rect.magnitude = 12 := by
  show (3 : ℝ) * 4 = 12
  norm_num

-- PROPERTY TRANSPORT: every certified surface area is ≥ 0 — a property of area's
-- defining relation, instantiated at the quantity level via the certificate
example (q : Quantity area.kind ℝ)
    (t : ℝ × ℝ → Fin 2 → EuclideanSpace ℝ (Fin 2)) (s : Set (ℝ × ℝ))
    (hs : MeasurableSet s) (h : IsSurfaceArea q t s) : 0 ≤ q.magnitude :=
  certified_surfaceArea_nonneg hs h

end PropertyKindCalculus.Examples.Iso80000.Part3
