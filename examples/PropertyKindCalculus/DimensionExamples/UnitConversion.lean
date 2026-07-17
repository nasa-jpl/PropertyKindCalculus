/-
# Worked example — unit conversion over ℝ, the numeric round-trip (§1.22, R17)

The exact `Int`-exponent conversion round-trip is exercised in the Mathlib-free
`PropertyKindCalculus.Examples.MiniUnit`; this is the companion over the real
carrier. A magnitude in centimetres, converted to kilometres and back, multiplies
by `10⁵` then `10⁻⁵` and returns exactly — the numeric analogue, landing here
because `ℝ` needs Mathlib (the `convertReal` layer lives in the `Dimension` library).
-/

import PropertyKindCalculus.UnitConversion

namespace PropertyKindCalculus.Examples.UnitConversion

open PropertyKindCalculus

/-- A metre, as the reference unit of a rational `length` kind. -/
def metre : MetrologicalUnit := { kind := { id := "length", scale := .ratio }, symbol := "m" }
/-- The centimetre — the metre with the SI `centi` prefix (10⁻²). -/
def centi : PrefixedUnit := metre.withPrefix SIPrefix.centi
/-- The kilometre — the metre with the SI `kilo` prefix (10³). -/
def kilo : PrefixedUnit := metre.withPrefix SIPrefix.kilo

/-- **§1.22 numeric round-trip.** Over `ℝ`, converting a real magnitude from `cm` to
`km` and back multiplies by `10⁵` then `10⁻⁵`, recovering it exactly — for *every*
magnitude. The factor is structurally nonzero (a power of ten, radix ≠ 0), so the
round-trip needs no chosen-reference nonzeroness hypothesis. -/
theorem cm_km_real_roundtrip (x : ℝ) :
    kilo.convertReal centi (centi.convertReal kilo x) = x :=
  PrefixedUnit.convertReal_roundtrip centi kilo rfl (by decide) x

-- a concrete magnitude: 3.0 (of cm) survives the cm → km → cm trip.
example : kilo.convertReal centi (centi.convertReal kilo 3) = 3 :=
  cm_km_real_roundtrip 3

/-! ## The same round-trip for IEC 80000-13 binary prefixes -/

/-- A byte, as the reference unit of a rational `information` kind. -/
def byte : MetrologicalUnit := { kind := { id := "information", scale := .ratio }, symbol := "B" }
/-- The kibibyte — the byte with the IEC `kibi` prefix (2¹⁰). -/
def kibibyte : PrefixedUnit := byte.withBinaryPrefix BinaryPrefix.kibi
/-- The mebibyte — the byte with the IEC `mebi` prefix (2²⁰). -/
def mebibyte : PrefixedUnit := byte.withBinaryPrefix BinaryPrefix.mebi

/-- **The identical round-trip at radix 2.** Over `ℝ`, converting from `KiB` to `MiB`
and back multiplies by `2⁻¹⁰` then `2¹⁰` — one and the same theorem
(`convertReal_roundtrip`), now discharged at radix `2`. -/
theorem kib_mib_real_roundtrip (x : ℝ) :
    mebibyte.convertReal kibibyte (kibibyte.convertReal mebibyte x) = x :=
  PrefixedUnit.convertReal_roundtrip kibibyte mebibyte rfl (by decide) x

end PropertyKindCalculus.Examples.UnitConversion
