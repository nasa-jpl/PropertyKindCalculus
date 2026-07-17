/-
# Requirement annotations on the worked examples — the `exemplifies` role

The `Examples` library carries the *worked, checked* scenarios the blueprint's
old "Concrete test" column described in prose — volumetric vs gravimetric water
content, width/height as sub-kinds of length, mass aggregating over a rock
assembly, a length built as speed × time, and so on. Because each is a real
declaration that the library elaborates under CI, tagging it `exemplifies`
promotes those concrete tests to typed traceability data: the matrix then shows,
per requirement, not only *what specifies/proves/implements it* but *the checked
example that exercises it*.

Applied from afar over the Mathlib-free `Examples` library. The example scenarios
that live in the PhysLib/Mathlib-backed layers (torque × angle = energy for R5,
torque ≡ energy in dimension for R7, the scale-spanning units for R13, the ladder
and adequacy examples for R14/R15) are tagged in `DimensionAnnotations` and
`UncertaintyAnnotations`, next to that layer's other annotations.
-/

import PropertyKindCalculus.Examples
import PropertyKindCalculus.Requirements.Attributes

/-! ## Kind structure (R1, R2, R3) -/

attribute [requirement "R1" exemplifies "volumetric vs gravimetric water content: two dimension-one kinds, provably distinct"]
  PropertyKindCalculus.Examples.Dedicated.vwc

attribute [requirement "R2" exemplifies "width and height specialize length, comparable yet distinct by examination principle"]
  PropertyKindCalculus.Examples.width

attribute [requirement "R3" exemplifies "a specific pencil's width — a term instantiating the kind `width`, not a subtype"]
  PropertyKindCalculus.Examples.pencilWidth

/-! ## Operation gating (R4, R6) -/

attribute [requirement "R4" exemplifies "same-kind Int lengths add (3 + 5 = 8); adding a length to a mass is a type error"]
  PropertyKindCalculus.Examples.MiniQuantity.lenA

attribute [requirement "R6" exemplifies "a nominal blood group admits only =/≠; a ratio length admits ×, ÷"]
  PropertyKindCalculus.Examples.Value.bloodGroup

/-! ## Soundness bridges (R8, R16) -/

-- R8 (expressiveness) is *demonstrated* by a unit built as a chosen value of a kind:
-- the centimetre is `length.unit "cm"`, one reference quantity of the length kind.
attribute [requirement "R8" exemplifies "the centimetre — a metrological unit built as a chosen value of the length kind (`length.unit \"cm\"`)"]
  PropertyKindCalculus.Examples.Unit.centimetre

-- R16 (verifiable) is exercised by the concrete round-trip: measuring 5 of the
-- centimetre reads back as 5, and re-applying the unit recovers the value.
attribute [requirement "R16" exemplifies "measuring 5 of the centimetre reads back as 5, and re-applying the unit recovers the value — the number-and-reference round-trip"]
  PropertyKindCalculus.Examples.Unit.fiveCm

-- R17 (verifiable) is exercised by the cm → km → cm conversion round-trip on the
-- exact Int exponent (the ℝ numeric analogue is exemplified in DimensionAnnotations).
attribute [requirement "R17" exemplifies "cm → km → cm recovers any magnitude's decimal exponent exactly (the km/cm factor is 10⁵, its reciprocal 10⁻⁵)"]
  PropertyKindCalculus.Examples.Unit.cm_km_roundtrip
-- … and the identical round-trip at radix 2 — IEC 80000-13 binary prefixes reuse the
-- same theorem, evidence that the base-parameterization is not a duplicate proof.
attribute [requirement "R17" exemplifies "KiB → MiB → KiB recovers exactly at radix two — the same convertExp_roundtrip, no new proof"]
  PropertyKindCalculus.Examples.Unit.kib_mib_roundtrip

/-! ## Aggregation (R9) -/

attribute [requirement "R9" exemplifies "mass is extensive: a three-sample rock assembly (3+5+7) reads 15 over its parts"]
  PropertyKindCalculus.Examples.MiniExtensivity.mass_extensive

/-! ## Representation parametricity (R10) -/

attribute [requirement "R10" exemplifies "the same Quantity layer runs at `R := Float` (3.0 + 0.5 = 3.5), not only at `Int`/`ℝ`"]
  PropertyKindCalculus.Examples.MiniQuantity.lenF

/-! ## Verified classification (R12) -/

attribute [requirement "R12" exemplifies "the kind-law `length = speed × time` (all three ratio-scale)"]
  PropertyKindCalculus.Examples.Classification.length_is_speed_times_time
attribute [requirement "R12" exemplifies "a length built through the kind-law, classified `length` by construction (60 × 2 = 120)"]
  PropertyKindCalculus.Examples.Classification.d
