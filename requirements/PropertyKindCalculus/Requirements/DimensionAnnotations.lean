/-
# Requirement annotations reaching into the Dimension layer

The requirements whose discharging declarations live in the PhysLib-backed
`Dimension` / `Interaction` / `ScaleSpanning` / `UnitConversion` libraries: R1's
dimension-1 disambiguation (`dim` is not injective), R5's interaction algebra, R7's
dimension homomorphism, R13's scale-spanning unit classification, and R17's numeric
(ℝ) unit-conversion round-trip. Applied from afar, so the layers being annotated
need no import of this machinery.

These pull in PhysLib (and, transitively, Mathlib), so — like
`CrossRefs.DimensionAnnotations` — this module is not Mathlib-free even though the
core-spine annotations in `Annotations` are.
-/

import PropertyKindCalculus.Dimension
import PropertyKindCalculus.Interaction
import PropertyKindCalculus.ScaleSpanning
import PropertyKindCalculus.UnitConversion
import PropertyKindCalculus.DimensionExamples.UnitConversion
import PropertyKindCalculus.Requirements.Attributes

namespace PropertyKindCalculus

/-! ## R1 — the dimension-1 disambiguation (many kinds, one dimension) -/

attribute [requirement "R1" proves "distinct kinds collapse to one dimension — dim is not injective"]
  dim_not_injective

/-! ## R5 — the interaction algebra (partial, typed, ternary product) -/

attribute [requirement "R5" specifies "the curated partial ternary product KMul (Flater App. C)"]
  InteractionAlgebra
attribute [requirement "R5" specifies "the division dual of the kind product"] InteractionAlgebra.KDiv
attribute [requirement "R5" proves "multiplication and division are inverse (a × b = c ⇔ c / b = a)"]
  InteractionAlgebra.kMul_iff_kDiv
attribute [requirement "R5" exemplifies "torque × angle = energy is sanctioned, though torque and energy share a dimension"]
  torque_angle_work

/-! ## R7 — dimension certifies coherence; it does not decide legality -/

attribute [requirement "R7" specifies "the forgetful functor dim : Kind → Dimension"]
  DimensionedKind.toDimension
attribute [requirement "R7" proves "dim is a homomorphism over the interaction algebra"]
  InteractionAlgebra.dim_homomorphism
attribute [requirement "R7" exemplifies "torque and energy share the dimension M·L²·T⁻² yet are different kinds"]
  Dim.torque_eq_energy

/-! ## R13 — scale-spanning units (a third unit category beyond base and derived) -/

attribute [requirement "R13" specifies "the three-way unit classification (base / derived / scale-spanning)"]
  UnitCategory
attribute [requirement "R13" specifies "a scale-spanning unit: dimensionally dependent, retained via a coefficient"]
  ScaleSpanningUnit
attribute [requirement "R13" specifies "the mechanical-reducibility criterion the dimension layer can detect"]
  Dimension.MechanicallyReducible
attribute [requirement "R13" proves "scale-spanning is not a function of dimension alone"]
  ScaleSpanning.scaleSpanning_not_determined_by_dimension
attribute [requirement "R13" exemplifies "the kelvin's scale-spanning character is invisible to the dimension layer (Θ kept independent)"]
  ScaleSpanning.kelvin_reduction_invisible_to_dimension
attribute [requirement "R13" exemplifies "the ampere is a genuine physical base — not scale-spanning — the contrast unit"]
  ScaleSpanning.ampere_is_physicalBase

/-! ## R17 — unit conversion round-trip, the numeric (ℝ) statement -/

-- The exact `Int`-exponent round-trip is proved core-side (`Annotations`); this is
-- the companion over the real carrier: the magnitude is multiplied by the
-- power-of-ten factor `10 ^ shift`, and the round-trip closes because the factor is
-- structurally nonzero — no chosen-reference nonzeroness needed.
attribute [requirement "R17" specifies "the §1.22 conversion factor as a real number, 10 ^ (power-of-ten shift)"]
  PrefixedUnit.realFactor
attribute [requirement "R17" proves "over ℝ, converting a magnitude between units and back is the identity (10 ^ shift · 10 ^ (−shift) = 1)"]
  PrefixedUnit.convertReal_roundtrip
attribute [requirement "R17" exemplifies "over ℝ, a cm magnitude converted to km and back returns exactly (×10⁵ then ×10⁻⁵)"]
  PropertyKindCalculus.Examples.UnitConversion.cm_km_real_roundtrip
attribute [requirement "R17" exemplifies "over ℝ at radix 2, a KiB magnitude converted to MiB and back returns exactly — the same theorem"]
  PropertyKindCalculus.Examples.UnitConversion.kib_mib_real_roundtrip

end PropertyKindCalculus
