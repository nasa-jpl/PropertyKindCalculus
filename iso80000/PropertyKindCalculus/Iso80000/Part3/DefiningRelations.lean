/-
# ISO 80000-3 — defining relations from the Remarks (the algebraic remarks)

Several ISO 80000-3 *Remarks* state a quantity's **defining relation** to other
quantities as a product, quotient, or reciprocal:

  * curvature `κ = 1/ρ` — the reciprocal of the radius of curvature (item 3-2);
  * repetency `σ = 1/λ` — the reciprocal of the wavelength (item 3-20);
  * frequency `f = 1/T` — the reciprocal of the period duration (item 3-17.1);
  * speed `v = ds/dt` — path length per duration (item 3-10.2);
  * plane angle `α = s/r` — arc length per radius, so the lengths cancel and the
    angle is dimension one (item 3-5).

This module formalizes each as an R12 *kind-law* over the catalogued kinds, using the
quotient and reciprocal families of `QuantityClassification`. Two payoffs:

  1. **The dimension follows from the relation, as a checked computation.** Under the
     SI's defining relation `α = s/r`, with arc and radius taken as plain lengths,
     plane angle computes to dimension one (`planeAngle_dim_from_arc_over_radius`).
     This formalizes the *current* SI convention — which the metrology literature
     actively contests (Quincey, Mohr & Phillips and others argue an angle is
     inherently *neither* a length ratio *nor* dimensionless). PKC need not adjudicate
     that at the dimension layer: plane angle stays a distinct *kind* from every other
     dimension-one quantity either way, and it is the kind, not the dimension, that
     keeps the radian and the steradian apart.
  2. **Verified construction and certificates instantiate at the quantity level.** A
     frequency built as the reciprocal of a period carries its classification
     certificate by construction (`frequencyOf_isReciprocal`), and the certificate
     determines the quantity (canonicity), over the `ℝ` carrier.

No normative text from the licensed standard is reproduced; the relations are
restated in this work's own formalism.
-/

import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.QuantityClassification

namespace PropertyKindCalculus.Iso80000.Part3.DefiningRelations

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000.Part3

/-! ## (1) The kind-laws (scale preconditions verified)

Each kind-law is a `ReciprocalKind` / `QuotientKind` instance: a proof that the kinds
involved are all ratio-scale, the precondition for inverting or dividing quantities
(Dybkær §13.3.5). For these catalogued kinds the scale facts hold by reflexivity. -/

/-- **Curvature is the reciprocal of the radius of curvature** (item 3-2: `κ = 1/ρ`). -/
theorem curvature_recip_radiusOfCurvature :
    ReciprocalKind radiusOfCurvature.kind curvature.kind := ⟨rfl, rfl⟩

/-- **Repetency is the reciprocal of the wavelength** (item 3-20: `σ = 1/λ`). -/
theorem repetency_recip_wavelength :
    ReciprocalKind wavelength.kind repetency.kind := ⟨rfl, rfl⟩

/-- **Frequency is the reciprocal of the period duration** (item 3-17.1: `f = 1/T`). -/
theorem frequency_recip_periodDuration :
    ReciprocalKind periodDuration.kind frequency.kind := ⟨rfl, rfl⟩

/-- **Speed is path length per duration** (item 3-10.2: `v = ds/dt`). -/
theorem speed_quot_pathLength_duration :
    QuotientKind pathLength.kind duration.kind speed.kind := ⟨rfl, rfl, rfl⟩

/-- **Plane angle is arc length per radius** (item 3-5: `α = s/r`). -/
theorem planeAngle_quot_pathLength_radius :
    QuotientKind pathLength.kind radius.kind planeAngle.kind := ⟨rfl, rfl, rfl⟩

/-! ## (2) The dimension follows from the relation (checked computations) -/

/-- Curvature's dimension is the inverse of the radius of curvature's: `L⁻¹` because
`κ = 1/ρ`. -/
theorem curvature_dim_from_radius :
    curvature.dim = (radiusOfCurvature.dim)⁻¹ := rfl

/-- Frequency's dimension is the inverse of the period's: `T⁻¹` because `f = 1/T`. -/
theorem frequency_dim_from_period :
    frequency.dim = (periodDuration.dim)⁻¹ := rfl

/-- Speed's dimension is length over duration: `L·T⁻¹` because `v = ds/dt`. -/
theorem speed_dim_from_pathLength_duration :
    speed.dim = pathLength.dim / duration.dim := rfl

/-- A ratio of two equal dimensions is dimension one. -/
theorem length_div_length : Dim.length / Dim.length = 1 := by
  ext <;> simp [Dim.length]

/-- **Under the SI's `α = s/r`, plane angle computes to dimension one.** With arc and
radius taken as plain lengths, `s/r` cancels the dimension — a checked computation
that reproduces the *current SI convention* rather than settling it. That the relation
*forces* dimensionlessness is exactly what the metrology reform literature disputes:
read arc and radius as carrying an angle dimension and `s/r` need not be dimensionless.
PKC formalizes the standard as published and leaves the dimensional stance open —
plane angle nonetheless stays a distinct *kind* from every other dimension-one quantity
(see `Part3.iso80000_3_dim_one_collision`), which is what keeps the radian and the
steradian non-interchangeable, whatever dimension the SI ultimately assigns. -/
theorem planeAngle_dim_from_arc_over_radius :
    planeAngle.dim = pathLength.dim / radius.dim := by
  show (1 : Dimension LTMCTDimensionBase) = Dim.length / Dim.length
  exact length_div_length.symm

/-! ## (3) Verified construction and certificates at the quantity level (`ℝ`)

The smart constructors build a classified quantity from its constituents, licensed by
the kind-law; the certificate holds by construction, and (canonicity) any quantity
carrying the certificate equals the constructed one. -/

/-- A frequency built as the reciprocal of a period — classified as a frequency **by
construction**. -/
noncomputable def frequencyOf (T : Quantity periodDuration.kind ℝ) :
    Quantity frequency.kind ℝ :=
  Quantity.recip frequency_recip_periodDuration T

/-- The constructed frequency satisfies the reciprocal certificate by construction. -/
theorem frequencyOf_isReciprocal (T : Quantity periodDuration.kind ℝ) :
    (frequencyOf T).IsReciprocal frequency_recip_periodDuration T := rfl

/-- **Canonicity, instantiated.** Any frequency certified as the reciprocal of a given
period equals the constructed one — a kind-law applied at the quantity level. -/
theorem frequency_certificate_canonical {T : Quantity periodDuration.kind ℝ}
    {f : Quantity frequency.kind ℝ}
    (h : f.IsReciprocal frequency_recip_periodDuration T) : f = frequencyOf T :=
  Quantity.eq_recip_of_isReciprocal frequency_recip_periodDuration h

/-- A speed built as path length per duration — classified as a speed **by
construction**. -/
noncomputable def speedOf (s : Quantity pathLength.kind ℝ) (t : Quantity duration.kind ℝ) :
    Quantity speed.kind ℝ :=
  Quantity.div speed_quot_pathLength_duration s t

/-- The constructed speed satisfies the quotient certificate by construction. -/
theorem speedOf_isQuotient (s : Quantity pathLength.kind ℝ) (t : Quantity duration.kind ℝ) :
    (speedOf s t).IsQuotient speed_quot_pathLength_duration s t := rfl

/-- A plane angle built as arc length per radius — classified as a plane angle **by
construction** (dimension one under the SI relation, `planeAngle_dim_from_arc_over_radius`). -/
noncomputable def planeAngleOf
    (s : Quantity pathLength.kind ℝ) (r : Quantity radius.kind ℝ) :
    Quantity planeAngle.kind ℝ :=
  Quantity.div planeAngle_quot_pathLength_radius s r

/-- The constructed plane angle satisfies the quotient certificate by construction. -/
theorem planeAngleOf_isQuotient
    (s : Quantity pathLength.kind ℝ) (r : Quantity radius.kind ℝ) :
    (planeAngleOf s r).IsQuotient planeAngle_quot_pathLength_radius s r := rfl

end PropertyKindCalculus.Iso80000.Part3.DefiningRelations
