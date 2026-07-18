/-
# Validation probes — soundness bridges (R8, R16, R17)

Inhabitation and axiom-profile probes for the core-side soundness bridges: a unit is a chosen
value of a kind (R8, expressiveness), unit references are faithful and commensurability is an
equivalence (R16), and unit conversion round-trips exactly (R17). Each equivalence/round-trip law
is applied to concrete units, with the Rule-2 boundary being the *negative*: incommensurable
units (different kinds) and an ill-formed unit of a nominal kind. R17 is checked on *both* prefix
families (SI decimal and IEC binary), the two radices being its characteristic edges.
-/

import PropertyKindCalculus

namespace PropertyKindCalculus.Tests.SoundnessBridges

open PropertyKindCalculus

/-- Length and mass, two ratio kinds; colour, a nominal kind. -/
def lengthK : KindOfProperty := { id := "length", scale := .ratio }
def massK   : KindOfProperty := { id := "mass",   scale := .ratio }
def colourK : KindOfProperty := { id := "colour", scale := .nominal }
/-- Information content, a ratio kind (for the binary-prefix family). -/
def infoK   : KindOfProperty := { id := "information", scale := .ratio }

/-- The metre, centimetre, millimetre — units of `lengthK` — and the kilogram, of `massK`. -/
def metre  : MetrologicalUnit := lengthK.unit "m"
def cmU    : MetrologicalUnit := lengthK.unit "cm"
def mmU    : MetrologicalUnit := lengthK.unit "mm"
def kilogram : MetrologicalUnit := massK.unit "kg"

/-! ## R8 — a unit is one chosen value of a kind (expressiveness) -/

-- The construction that typechecks *is* the demonstration: a `MetrologicalUnit` is the kind it
-- references together with a symbol.
example : metre.kind = lengthK := rfl

-- Boundary: a nominal kind bears no unit — a unit of `colourK` is provably ill-formed, so "unit
-- of a kind" is not vacuously available for every kind.
theorem r8_colour_unit_illformed : ¬ (colourK.unit "??").WellFormed :=
  MetrologicalUnit.not_wellFormed_of_nominal rfl

/-! ## R16 — commensurability is an equivalence; the number-and-reference form round-trips -/

-- Inhabitation of the equivalence on concrete units: reflexive, symmetric, transitive across
-- three units of one kind.
theorem r16_refl  : metre.Commensurable metre := MetrologicalUnit.Commensurable.refl metre
theorem r16_m_cm  : metre.Commensurable cmU := rfl
theorem r16_cm_m  : cmU.Commensurable metre := MetrologicalUnit.Commensurable.symm r16_m_cm
theorem r16_cm_mm : cmU.Commensurable mmU := rfl
theorem r16_trans : metre.Commensurable mmU :=
  MetrologicalUnit.Commensurable.trans r16_m_cm r16_cm_mm

-- Boundary (Rule 2): a metre and a kilogram are *not* commensurable (distinct kinds) — the only
-- relation a unit converts along genuinely excludes cross-kind pairs.
theorem r16_incommensurable : ¬ metre.Commensurable kilogram := by
  unfold MetrologicalUnit.Commensurable; decide

-- The §13.3.3 number-and-reference round-trip: measure 5 metres, read back the numeral (5), and
-- re-apply the unit to recover the value exactly.
#guard (metre.measure 5).numeral == 5

theorem r16_roundtrip : metre.measure (metre.measure 5).numeral = metre.measure 5 :=
  MetrologicalUnit.measure_eq_of_measures (MetrologicalUnit.measures_measure metre 5)

/-- info: 'PropertyKindCalculus.MetrologicalUnit.Commensurable.refl' does not depend on any axioms -/
#guard_msgs in #print axioms MetrologicalUnit.Commensurable.refl
/-- info: 'PropertyKindCalculus.MetrologicalUnit.Commensurable.symm' does not depend on any axioms -/
#guard_msgs in #print axioms MetrologicalUnit.Commensurable.symm
/-- info: 'PropertyKindCalculus.MetrologicalUnit.Commensurable.trans' does not depend on any axioms -/
#guard_msgs in #print axioms MetrologicalUnit.Commensurable.trans
/-- info: 'PropertyKindCalculus.MetrologicalUnit.measure_numeral' does not depend on any axioms -/
#guard_msgs in #print axioms MetrologicalUnit.measure_numeral
/-- info: 'PropertyKindCalculus.MetrologicalUnit.measure_eq_of_measures' does not depend on any axioms -/
#guard_msgs in #print axioms MetrologicalUnit.measure_eq_of_measures

/-! ## R17 — unit conversion is a faithful, exact round-trip (both prefix families) -/

/-- Centimetre and kilometre — SI decimal prefixes (radix 10) of the metre. -/
def cm : PrefixedUnit := metre.withPrefix SIPrefix.centi
def km : PrefixedUnit := metre.withPrefix SIPrefix.kilo
/-- Kibibyte and mebibyte — IEC binary prefixes (radix 2) of the byte. -/
def byteU : MetrologicalUnit := infoK.unit "B"
def kiB : PrefixedUnit := byteU.withBinaryPrefix BinaryPrefix.kibi
def miB : PrefixedUnit := byteU.withBinaryPrefix BinaryPrefix.mebi

-- The two conversion factors are reciprocal, and the round-trip is the identity — checked over
-- BOTH radices (decimal cm/km and binary KiB/MiB), the characteristic edges of the one theorem.
theorem r17_cm_km_reciprocal : cm.shift km + km.shift cm = 0 := PrefixedUnit.shift_add_symm cm km

theorem r17_cm_km_roundtrip (e : Int) : km.convertExp cm (cm.convertExp km e) = e :=
  PrefixedUnit.convertExp_roundtrip cm km e

theorem r17_kib_mib_roundtrip (e : Int) : miB.convertExp kiB (kiB.convertExp miB e) = e :=
  PrefixedUnit.convertExp_roundtrip kiB miB e

-- and the shifts are the exact integer exponents (cm→km = −2 − 3 = −5; KiB→MiB = 10 − 20 = −10).
#guard cm.shift km == -5
#guard kiB.shift miB == -10

/-- info: 'PropertyKindCalculus.PrefixedUnit.shift_add_symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms PrefixedUnit.shift_add_symm
/-- info: 'PropertyKindCalculus.PrefixedUnit.convertExp_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms PrefixedUnit.convertExp_roundtrip

end PropertyKindCalculus.Tests.SoundnessBridges
