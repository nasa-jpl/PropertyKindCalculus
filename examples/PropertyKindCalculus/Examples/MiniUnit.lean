/-
# Worked example: metrological units and the number-and-reference form

Demonstrates, as *checked* facts, the theses of the metrological-unit layer
(Dybkær Ch. 18, §13.3.3):

  1. **Commensurability is "of the same kind" (§9.13.4).** The metre and the
     centimetre are commensurable (both reference `length`); the metre and the
     kilogram are *not* — a type-level fact, and commensurability is an equivalence
     relation.
  2. **Only unitary kinds bear a unit (§13.3.3, §9.13.4).** A length unit is
     well-formed; an *ordinal* kind (Mohs hardness) bears no metrological unit, and
     neither does a *nominal* one (ABO blood group).
  3. **The number-and-reference round-trip (§13.3.3).** Measuring 5 of the
     centimetre is the property value "5 cm"; the numeral reads back as 5, and
     re-applying the unit to a value's numeral recovers the value. Measuring in a
     well-formed unit yields a *quantity* value, and values measured in
     commensurable units are comparable.

Like the other minis, this module is part of the separate `Examples` library and
imports the core `PropertyKindCalculus` library as any downstream consumer would.
-/

module

public import PropertyKindCalculus
-- Private scope only: the checks below reduce through bodies sealed in the core
-- library; `import all` gives this file the reduction without exposing them.
import all PropertyKindCalculus.UnitPrefix

@[expose] public section Blanket

namespace PropertyKindCalculus.Examples.Unit

open PropertyKindCalculus

/-! ## Kinds -/

/-- The broad rational kind-of-quantity length. -/
def length : KindOfProperty := { id := "length", scale := .ratio }
/-- Another rational kind, for the cross-kind non-commensurability check. -/
def mass : KindOfProperty := { id := "mass", scale := .ratio }
/-- An *ordinal* kind: Mohs hardness — rankable, but not a reference × number. -/
def mohsHardness : KindOfProperty := { id := "mohs-hardness", scale := .ordinal }
/-- A *nominal* kind: ABO blood group (Dybkær's own §9.15 example). -/
def bloodGroup : KindOfProperty := { id := "abo-blood-group", scale := .nominal }

/-! ## Units -/

/-- The metre — a metrological unit of `length` (§18.12). -/
def metre : MetrologicalUnit := length.unit "m"
/-- The centimetre — another unit of `length`, commensurable with the metre. -/
def centimetre : MetrologicalUnit := length.unit "cm"
/-- The kilogram — a unit of `mass`, *not* commensurable with the metre. -/
def kilogram : MetrologicalUnit := mass.unit "kg"

/-! ## (1) Commensurability is "of the same kind" (§9.13.4) -/

-- the metre and the centimetre reference the same kind …
example : metre.Commensurable centimetre := rfl

-- … the metre and the kilogram do NOT (a metre is not a kilogram).
example : ¬ metre.Commensurable kilogram := by
  unfold MetrologicalUnit.Commensurable metre kilogram length mass KindOfProperty.unit
  decide

-- commensurability is an equivalence relation (symmetry and transitivity shown).
example : centimetre.Commensurable metre :=
  MetrologicalUnit.Commensurable.symm (show metre.Commensurable centimetre from rfl)

example : metre.Commensurable centimetre :=
  MetrologicalUnit.Commensurable.trans
    (show metre.Commensurable metre from rfl)
    (show metre.Commensurable centimetre from rfl)

/-! ## (2) Only unitary kinds bear a unit (§13.3.3, §9.13.4) -/

-- the metre is well-formed: its kind (length, ratio) bears a unit.
example : metre.WellFormed := KindOfProperty.rational_bears_unit rfl

-- an ordinal kind bears no metrological unit — Dybkær §9.13.4 exactly.
example : ¬ (mohsHardness.unit "mohs").WellFormed :=
  MetrologicalUnit.not_wellFormed_of_ordinal rfl

-- nor does a nominal kind.
example : ¬ (bloodGroup.unit "abo").WellFormed :=
  MetrologicalUnit.not_wellFormed_of_nominal rfl

/-! ## (3) The number-and-reference round-trip (§13.3.3) -/

/-- Measuring 5 of the centimetre: the property value "5 cm". -/
def fiveCm : PropertyValue := centimetre.measure 5

-- `quantity / unit = number`: the numeral reads back as 5 …
example : fiveCm.numeral = 5 := rfl
-- … against the centimetre reference …
example : fiveCm.reference = "cm" := rfl
-- … of kind length.
example : fiveCm.kind = length := rfl

-- `number × unit = quantity`: re-applying the unit to a measured value's numeral
-- recovers the value exactly (the §13.3.3 round-trip).
example : centimetre.measure fiveCm.numeral = fiveCm :=
  MetrologicalUnit.measure_eq_of_measures (centimetre.measures_measure 5)

-- measuring in a well-formed unit yields a quantity value (§16.10).
example : fiveCm.IsQuantityValue :=
  MetrologicalUnit.measure_isQuantityValue
    (u := centimetre) (KindOfProperty.rational_bears_unit rfl) 5

-- values measured in commensurable units are comparable (§9.13.4) …
example : (metre.measure 1).Comparable (centimetre.measure 100) :=
  MetrologicalUnit.comparable_of_measures
    (metre.measures_measure 1) (centimetre.measures_measure 100) rfl

-- … and live on the same value scale (§10.14).
example : metre.kind.valueScale = centimetre.kind.valueScale :=
  MetrologicalUnit.valueScale_eq_of_commensurable rfl

-- a measured value lives on its unit's kind's value scale.
example : (centimetre.kind.valueScale).Admits fiveCm := rfl

/-! ## (4) Unit conversion is a faithful round-trip (§1.22) -/

/-- The centimetre as a *prefixed* unit — the metre with the SI `centi` prefix (10⁻²). -/
def centi : PrefixedUnit := metre.withPrefix SIPrefix.centi
/-- The kilometre — the metre with the SI `kilo` prefix (10³). -/
def kilo : PrefixedUnit := metre.withPrefix SIPrefix.kilo

-- the §1.22 conversion factor km → cm is 10⁵ (a power-of-ten exponent) …
example : kilo.shift centi = 5 := by decide
-- … and cm → km is its exact reciprocal, 10⁻⁵.
example : centi.shift kilo = -5 := by decide

/-- **§1.22 round-trip.** Converting a magnitude's decimal exponent from `cm` to `km`
and back recovers it *exactly*, for every value — the faithful conversion round-trip
on the exact `Int` exponent. -/
theorem cm_km_roundtrip (x : Int) :
    kilo.convertExp centi (centi.convertExp kilo x) = x :=
  PrefixedUnit.convertExp_roundtrip centi kilo x

-- concretely, 7 survives the cm → km → cm trip.
example : kilo.convertExp centi (centi.convertExp kilo 7) = 7 := by decide

/-! ## (5) The same round-trip for IEC 80000-13 binary prefixes -/

/-- A byte — the reference unit of a rational `information` kind. -/
def byte : MetrologicalUnit := { kind := { id := "information", scale := .ratio }, symbol := "B" }
/-- The kibibyte and mebibyte — binary prefixings of the byte (2¹⁰, 2²⁰). -/
def kibibyte : PrefixedUnit := byte.withBinaryPrefix BinaryPrefix.kibi
def mebibyte : PrefixedUnit := byte.withBinaryPrefix BinaryPrefix.mebi

-- the binary conversion factor MiB → KiB is 2¹⁰ (exponent 10) …
example : mebibyte.shift kibibyte = 10 := by decide
-- … and both live at radix 2, so conversion between them is defined.
example : kibibyte.SameRadix mebibyte := rfl

/-- **The identical round-trip at radix 2.** Exactly the same theorem as
`cm_km_roundtrip` — `convertExp_roundtrip` is blind to the radix, so the IEC binary
prefixes reuse it with no new proof. -/
theorem kib_mib_roundtrip (x : Int) :
    mebibyte.convertExp kibibyte (kibibyte.convertExp mebibyte x) = x :=
  PrefixedUnit.convertExp_roundtrip kibibyte mebibyte x

end PropertyKindCalculus.Examples.Unit

end Blanket
