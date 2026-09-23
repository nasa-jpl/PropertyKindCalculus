/-
# Worked examples for the function calculus — all five families

Exercises `PropertyKindCalculus.QuantityFunction` (core) and
`PropertyKindCalculus.Function` (the dimensioned layer) at two carriers: `Float` (the
run carrier, via `#guard`) and `ℝ` (the proof carrier, where the function laws hold).
One example per family A–E, plus the two disambiguation showpieces and a characteristic
number. Kept in the `DimensionExamples` library so no *library* module carries `#guard`.
-/

module

public import PropertyKindCalculus.Function
meta import PropertyKindCalculus.Function

@[expose] public section Blanket

namespace PropertyKindCalculus.DimensionExamples

open PropertyKindCalculus

/-! ## Family A — kind-preserving functions (`Float`) -/

-- `clamp` a reflectivity into its physical `[0, 1]` box (kind-preserving).
#guard (Quantity.clamp (⟨0.0⟩ : Quantity reflectivity.kind Float) ⟨1.0⟩ ⟨1.3⟩).magnitude == 1.0

-- `abs` of a (signed) length is its magnitude (kind-preserving).
#guard (Quantity.abs (⟨-3.0⟩ : Quantity lengthKind.kind Float)).magnitude == 3.0

/-! ## Family B — powers and roots (`Float` value, `ℝ`/`Dimension` certificate)

`sqrt` of an area is a length: the value runs on `Float`, and the *dimensional*
certificate `dim(√area) = (dim area)^(1/2) = L` is `sqrt_area_coherent`. -/

/-- The half-power kind law for area → length (both ratio-scale). -/
theorem area_to_length : PowerKind (1 / 2) areaK.kind lengthKind.kind := ⟨rfl, rfl⟩

-- `√(16 m²) = 4 m`, run on the executable carrier.
#guard (Quantity.sqrt area_to_length (⟨16.0⟩ : Quantity areaK.kind Float)).magnitude == 4.0

/-- The accompanying dimensional certificate (proved in the `Dimension` layer): the
square root scales the dimension by `1/2`, carrying `L²` to `L`. -/
example : DimPowerKind (1 / 2) areaK lengthKind := sqrt_area_coherent

/-! ## Family C — transcendentals (`ℝ` law transfer, `Float` value)

The function identities hold at the `ℝ` proof carrier (`LawfulMathCarrier ℝ`) and run —
without the laws — at `Float`. -/

/-- The exponential carries sums to products — a `LawfulMathCarrier ℝ` law, available at
the proof carrier for any quantity magnitudes. -/
example (a b : ℝ) : MathCarrier.exp (a + b) = MathCarrier.exp a * MathCarrier.exp b :=
  LawfulMathCarrier.exp_add a b

/-- The loss-tangent → number transcendental kind law (both ratio-scale). -/
theorem lossTangent_to_number : TranscendentalKind lossTangentK.kind numberK.kind := ⟨rfl, rfl⟩

-- `tanh 0 = 0`, run on the executable carrier (a dimensionless loss tangent in, a
-- dimensionless number out).
#guard (Quantity.tanh lossTangent_to_number (⟨0.0⟩ : Quantity lossTangentK.kind Float)).magnitude == 0.0

-- Euler's number is `exp 1`, derived (not a primitive constant) — definitionally so at
-- the carrier.
#guard MathCarrier.e (R := Float) == Float.exp 1.0

/-! ## Family D — trigonometric functions and the disambiguation -/

/-- The plane-angle → number kind law for `sin` (both ratio-scale). -/
theorem angle_to_number : TranscendentalKind angleKind.kind numberK.kind := ⟨rfl, rfl⟩

-- `cos 0 = 1` of a plane angle, run on the executable carrier.
#guard (Quantity.cos angle_to_number (⟨0.0⟩ : Quantity angleKind.kind Float)).magnitude == 1.0

/-- **The disambiguation, for functions.** `sin` is sanctioned on an angle, yielding a
number; the two are distinct kinds though both forget to dimension one. -/
example :
    siTrig.TFn .sin angleKind numberK
      ∧ angleKind.kind ≠ numberK.kind
      ∧ angleKind.toDimension = numberK.toDimension :=
  sin_angle_is_number

/-- **The forbidden application.** `sin` of a *reflectivity* is not sanctioned by the
curated trigonometric algebra — a category error, even though reflectivity is dimension
one exactly like an angle. A dimension-only system would wave this through. -/
example : ¬ siTrig.TFn .sin reflectivity numberK :=
  sin_reflectivity_not_sanctioned

/-! ## Family E — logarithmic levels (scale-aware) -/

/-- A sound pressure level (dB) is dimension one but **interval**-scale, so the
multiplicative calculus refuses it: there is no product kind with a level as a factor. -/
example {k₂ k : KindOfProperty} : ¬ ProductKind soundPressureLevelK.kind k₂ k :=
  level_no_product

/-- Levels may still be *added* — `Quantity.add` is gated only to scales that admit
differences, and **interval** scale does (it is a `DifferenceKind`) — which is exactly
right: a dB *difference* is meaningful, a dB *product* is not. -/
example (x y : Quantity soundPressureLevelK.kind Float) : Quantity soundPressureLevelK.kind Float :=
  Quantity.add (DifferenceKind.ofScale) x y

/-! ## Coda — a characteristic number is a kind, not a constant -/

/-- ISO/IEC 80000-11: Reynolds and Mach numbers are *distinct kinds*, both dimension one
— unlike `MathCarrier.pi` (a fixed magnitude in the carrier), each is a variable quantity
formed by the quotient calculus. -/
example :
    reynoldsK.kind ≠ machK.kind
      ∧ reynoldsK.toDimension = 1 ∧ machK.toDimension = 1 :=
  reynolds_ne_mach_but_both_dimensionless

end PropertyKindCalculus.DimensionExamples

end Blanket
