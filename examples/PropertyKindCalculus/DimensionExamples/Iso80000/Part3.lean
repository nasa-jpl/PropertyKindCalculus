/-
# Worked examples — ISO 80000-3 (Space and time)

Part-3 examples, mirroring the `Iso80000` library's own `Iso80000/Part3` layout:

1. the dimensional algebra and unit facts (length is `L`, area is `L²`, speed is
   `L·T⁻¹`; the metre well-formed; commensurability "of the same kind");
2. **ISO 80000-2 §18** — a *vector* quantity (displacement, item 3-1.11) as a numerical
   array × **one scalar unit**, with the additivity laws transferring to the vector
   carrier by the *same* parametric proof used for scalars (the R10 reading of §18);
3. from item 3-3's surface-element remark to quantity **classification** and
   **metrological consistency** at the quantity level;
4. **verified classification (R12)** — area certificates;
5. **the length family as a specialization lattice (R2)** — width, distance, … as
   length species individuated **by measurement principle**, comparable yet distinct;
6. **dimension collisions** — same dimension, distinct kind (plane vs solid angle,
   frequency vs angular frequency, velocity vs speed), and the units they keep apart;
7. **the volume-element remark** (item 3-4) and the **algebraic remarks** (item 3-2,
   3-5, 3-10.2, 3-17.1, 3-20) as kind-laws;
8. **catalogue coverage** — all 42 items carry their source as data.

Series-wide catalogue examples are in the sibling
`PropertyKindCalculus.DimensionExamples.Iso80000.References`.
-/

import PropertyKindCalculus.Iso80000
import PropertyKindCalculus.Iso80000.Part3.AreaElement
import PropertyKindCalculus.Iso80000.Part3.AreaClassification
import PropertyKindCalculus.Iso80000.Part3.VolumeElement
import PropertyKindCalculus.Iso80000.Part3.DefiningRelations
import PropertyKindCalculus.QuantityReal
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

namespace PropertyKindCalculus.Examples.Iso80000.Part3

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open PropertyKindCalculus.Iso80000.Part3
open PropertyKindCalculus.Iso80000.Part3.AreaElement
open PropertyKindCalculus.Iso80000.Part3.AreaClassification
open PropertyKindCalculus.Iso80000.Part3.VolumeElement
open PropertyKindCalculus.Iso80000.Part3.DefiningRelations

-- displacement and area are ratio-scale, hence `DifferenceKind`s — the comparability
-- witness `Quantity.add` requires, threaded explicitly into the additivity examples.
private theorem hDisp : DifferenceKind displacement.kind := .ofScale
private theorem hArea : DifferenceKind area.kind := .ofScale

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
    Quantity.add hDisp x y = Quantity.add hDisp y x :=
  Quantity.add_comm hDisp x y

example (x y z : Quantity displacement.kind (Fin 3 → ℝ)) :
    Quantity.add hDisp x y = Quantity.add hDisp y x
      ∧ Quantity.add hDisp (Quantity.add hDisp x y) z
          = Quantity.add hDisp x (Quantity.add hDisp y z)
      ∧ Quantity.add hDisp Quantity.zero x = x ∧ Quantity.add hDisp x Quantity.zero = x :=
  Quantity.laws_parametric hDisp x y z

/-- An `Int`-valued displacement, for an executable witness: componentwise addition
computes (the middle component `5 + 5 = 10`). -/
def vInt : Quantity displacement.kind (Fin 3 → Int) := ⟨![4, 5, 6]⟩
#guard (Quantity.add hDisp vInt vInt).magnitude 1 == 10

/-! ## (3) From a remark's mathematics to quantity classification and consistency

ISO 80000-3 item 3-3 defines area through a surface element `dA = √g du dv`
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
    Quantity.add hArea (surfaceAreaQuantity t) (surfaceAreaQuantity u)
      = Quantity.add hArea (surfaceAreaQuantity u) (surfaceAreaQuantity t) :=
  Quantity.add_comm hArea _ _

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
-- times the area of its parameter region (ISO 80000-3, 3-3: `A = ∬ √g du dv`).
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

/-! ## (5) The length family: a specialization lattice individuated by measurement
principle (requirement R2, on the real standard)

ISO 80000-3 lists width (3-1.2), distance (3-1.8), radius (3-1.6), … as separate
length items, all of dimension `L`, distinguished in the standard only by prose. Here
each is a *species* of the general length kind (3-1.1), individuated **not by fiat but
by an explicit measurement (examination) principle**. -/

-- (a) a radius specializes length — transitively (radius ⊑ diameter ⊑ width ⊑ length),
--     so specialization is a genuine preorder, a lattice not just direct edges.
example : Specializes Edge radius.kind length.kind := radius_specializes_length

-- (b) DISTINCTION NOT BY FIAT: width and distance are distinct kinds *because they are
--     examined by different principles* (transverse extent vs shortest path) — the
--     user-facing point, proved via `distinct_of_examPrinciple`, not by `id` strings.
example : width.kind ≠ distance.kind := width_ne_distance

-- the link from the kind back to its measurement principle is checked, too.
example : width.kind.examinedBy LengthPrinciple.transverse := width_examinedBy

-- (c) COMPARABILITY PRESERVED: though distinct, width and distance remain mutually
--     comparable — they share the super-kind length, so combining them is possible
--     only via an explicit up-cast, never silently.
example : MutuallyComparable Edge width.kind distance.kind := width_distance_comparable

-- (d) and the dimension cannot tell them apart: same dimension `L`, distinct kinds.
example : width.dim = distance.dim := rfl

/-! ## (6) Dimension collisions: same dimension, distinct kind

The {dimension functor} identifies these pairs; the kind layer keeps them apart —
including their units. -/

-- plane angle and solid angle: both dimension one, distinct kinds, distinct units.
example : planeAngle.dim = solidAngle.dim := rfl
example : planeAngle.kind ≠ solidAngle.kind := planeAngle_ne_solidAngle
example : ¬ radian.Commensurable steradian := radian_steradian_not_commensurable

-- frequency and angular frequency: both `T⁻¹`, distinct kinds, distinct units
-- (the famous Hz vs rad/s distinction, made structural).
example : frequency.dim = angularFrequency.dim := rfl
example : frequency.kind ≠ angularFrequency.kind := frequency_ne_angularFrequency
example : ¬ hertz.Commensurable radianPerSecond := hertz_radianPerSecond_not_commensurable

-- velocity and speed: both `L·T⁻¹`, distinct kinds (the vector and its magnitude).
example : velocity.kind ≠ speed.kind := velocity_ne_speed

-- the dimension-1 disambiguation, on standard quantities (cf. `dim_not_injective`).
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  iso80000_3_dim_one_collision

/-! ## (7) The volume-element remark (item 3-4) and the algebraic remarks -/

-- the volume element squares back to the determinant of the 3×3 metric tensor …
example (t : Fin 3 → EuclideanSpace ℝ (Fin 3)) : volumeElement t ^ 2 = metricDet t :=
  volumeElement_sq t
-- … and for a flat region it is the change-of-variables volume density `|det A|`.
example (t : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    volumeElement t = |(Matrix.of fun i j => t j i).det| :=
  volumeElement_eq_abs_det t

-- ALGEBRAIC REMARK (item 3-5): a plane angle is dimension one *because* it is a ratio
-- of two lengths (`α = s/r`) — the dimensionlessness is computed from the relation.
example : planeAngle.dim = pathLength.dim / radius.dim :=
  planeAngle_dim_from_arc_over_radius

-- ALGEBRAIC REMARK (item 3-17.1): a frequency built as the reciprocal of a period
-- carries its classification certificate by construction, over `ℝ`.
example (T : Quantity periodDuration.kind ℝ) :
    (frequencyOf T).IsReciprocal frequency_recip_periodDuration T :=
  frequencyOf_isReciprocal T

-- the quotient kind-law for speed instantiates at a *different* carrier (`Int`), where
-- the construction also computes: `10 m / 2 s = 5 m/s`.
def speedInt : Quantity speed.kind Int :=
  Quantity.div speed_quot_pathLength_duration (⟨10⟩ : Quantity pathLength.kind Int) ⟨2⟩
#guard speedInt.magnitude == 5

/-! ## (8) Catalogue coverage — all 42 items carry their source as data -/

-- every ISO 80000-3 item is catalogued, in item order …
#guard PropertyKindCalculus.Iso80000.Part3.catalogue.length == 42
-- … with the corrected item designations (area is 3-3, volume 3-4, duration 3-9) …
#guard areaCK.item == "3-3"
#guard volumeCK.item == "3-4"
#guard durationCK.item == "3-9"
-- … each citing its full source …
#guard areaCK.cite == "ISO 80000-3, Second edition, 2019-10 item 3-3"
-- … and recording its coherent SI unit symbol as a locator.
#guard curvatureCK.coherentUnit == "m⁻¹"
#guard planeAngleCK.coherentUnit == "rad"
#guard frequencyCK.coherentUnit == "Hz"

end PropertyKindCalculus.Examples.Iso80000.Part3
