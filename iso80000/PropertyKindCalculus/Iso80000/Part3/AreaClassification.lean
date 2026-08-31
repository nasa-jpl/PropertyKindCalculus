/-
# Verified classification of areas (an R12 instance)

This module classifies a `Quantity Part3.area.kind ℝ` *with a certificate*, tying the
classification to area's defining relation — the formalized ISO 80000-3 item 3-2.1
*Remark* (`AreaElement`). It realizes R12 (verified instantiation) in the
Mathlib-backed layer, where the analytic relation lives.

Two certificate forms, both for the one area kind:

  * `IsSurfaceArea` — the general (Level-2, integral) certificate: the magnitude is the
    surface integral `∬ √g du dv` of an actual surface. A property of the defining
    relation (the element is `≥ 0`) **transports** to *every* certified area
    (`certified_surfaceArea_nonneg`) — a kind-level fact instantiated at the quantity
    level.
  * `rectangleArea` — the closed-form (product) certificate: a rectangle's area is
    `width × height`, a verified-by-construction `ProductKind` instance (area = length ×
    length). Both forms are areas — same kind, same `L²` dimension
    (`Part3.area_dim_length`); the integral certificate is the more general one.
-/

import PropertyKindCalculus.Quantity
import PropertyKindCalculus.QuantityClassification
import PropertyKindCalculus.Iso80000.Part3.AreaElement
import PropertyKindCalculus.QuantityReal

namespace PropertyKindCalculus.Iso80000.Part3.AreaClassification

open PropertyKindCalculus MeasureTheory
open PropertyKindCalculus.Iso80000.Part3
open PropertyKindCalculus.Iso80000.Part3.AreaElement

/-! ## The integral certificate: an area is the area of a surface -/

/-- **Certificate (Level-2, integral).** `q : Quantity area.kind ℝ` *is a surface area*
iff its magnitude is the area of an actual surface — the parametrization `t` over the
region `s`, via area's defining relation `∬ √g du dv`. A proof of this certifies `q`'s
classification as an area, rather than asserting it. -/
def IsSurfaceArea (q : Quantity area.kind ℝ)
    (t : ℝ × ℝ → Fin 2 → EuclideanSpace ℝ (Fin 2)) (s : Set (ℝ × ℝ)) : Prop :=
  q.magnitude = surfaceArea t s

/-- The surface area is non-negative — the area element is `≥ 0` everywhere, integrated
over the region. -/
theorem surfaceArea_nonneg
    (t : ℝ × ℝ → Fin 2 → EuclideanSpace ℝ (Fin 2)) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) : 0 ≤ surfaceArea t s := by
  rw [surfaceArea]
  exact setIntegral_nonneg hs (fun x _ => areaElement_nonneg (t x))

/-- **Property transport (R12).** *Every* certified surface area is non-negative — a
property of area's defining relation, instantiated at the quantity level via the
certificate. -/
theorem certified_surfaceArea_nonneg {q : Quantity area.kind ℝ}
    {t : ℝ × ℝ → Fin 2 → EuclideanSpace ℝ (Fin 2)} {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (h : IsSurfaceArea q t s) : 0 ≤ q.magnitude := by
  rw [IsSurfaceArea] at h
  rw [h]
  exact surfaceArea_nonneg t hs

/-! ## The product certificate: a rectangle's area is width × height -/

/-- **area = length × length**, as a product kind-law (the Level-1 scale precondition;
the dimensional `L²` is `Part3.area_dim_length`). -/
theorem area_is_length_times_length :
    ProductKind length.kind length.kind area.kind := ⟨rfl, rfl, rfl⟩

/-- A rectangle's area, verified-classified as an area **by construction** from its two
side lengths (`width × height`). -/
def rectangleArea (w h : Quantity length.kind ℝ) : Quantity area.kind ℝ :=
  Quantity.mul area_is_length_times_length w h

/-- The rectangle-area certificate holds by construction. -/
theorem rectangleArea_isProduct (w h : Quantity length.kind ℝ) :
    (rectangleArea w h).IsProduct area_is_length_times_length w h := rfl

end PropertyKindCalculus.Iso80000.Part3.AreaClassification
