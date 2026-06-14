/-
# Worked example: property values and their value scale

Demonstrates, as *checked* facts, the theses of the property-value layer
(Dybkær Ch. 9, 16, 10, 17):

  1. **Comparison is within a kind (§9.15).** Two length values are comparable; a
     length value and a mass value are *not* — comparability is an equivalence
     relation, and comparable values share the same operator set.
  2. **Quantity value vs nominal value (§16.10, §12.4).** "5 cm" is a quantity
     value (its kind has magnitude); a blood-group designation is not.
  3. **The value scale (§10.14).** Both length values live on `length`'s value
     scale and are therefore mutually comparable; the scale admits ratios, and its
     true/examined provenance does not change which operations it supports.

The nominal example (ABO blood group, value `A`) is Dybkær's own §9.15 example.

Like the other minis, this module is part of the separate `Examples` library and
imports the core `PropertyKindCalculus` library as any downstream consumer would.
-/

import PropertyKindCalculus

namespace PropertyKindCalculus.Examples.Value

open PropertyKindCalculus

/-! ## Kinds -/

/-- The broad rational kind-of-quantity length. -/
def length : KindOfProperty := { id := "length", scale := .ratio }
/-- Another rational kind, for the cross-kind non-comparability check. -/
def mass : KindOfProperty := { id := "mass", scale := .ratio }
/-- A *nominal* kind: ABO blood group (Dybkær's own §9.15 example). -/
def bloodGroup : KindOfProperty := { id := "abo-blood-group", scale := .nominal }

/-! ## Property values -/

/-- A length quantity value: 5 cm (numeral × reference, §16.10). -/
def fiveCm : PropertyValue := { kind := length, numeral := 5, reference := "cm" }
/-- Another length value: 12 cm. -/
def twelveCm : PropertyValue := { kind := length, numeral := 12, reference := "cm" }
/-- A third length value, for the transitivity witness: 30 cm. -/
def thirtyCm : PropertyValue := { kind := length, numeral := 30, reference := "cm" }
/-- A mass value: 1 kg. -/
def oneKg : PropertyValue := { kind := mass, numeral := 1, reference := "kg" }
/-- A nominal property value: this sample's blood group is `A` (no magnitude). -/
def groupA : PropertyValue := { kind := bloodGroup, numeral := 0, reference := "A" }

/-! ## (1) Comparison is within a kind (§9.15) -/

-- two length values are comparable …
example : fiveCm.Comparable twelveCm := rfl

-- … a length value and a mass value are NOT.
example : ¬ fiveCm.Comparable oneKg := by
  unfold PropertyValue.Comparable
  decide

-- comparability is an equivalence relation (symmetry and transitivity shown).
example : twelveCm.Comparable fiveCm :=
  PropertyValue.Comparable.symm (show fiveCm.Comparable twelveCm from rfl)

example : fiveCm.Comparable thirtyCm :=
  PropertyValue.Comparable.trans
    (show fiveCm.Comparable twelveCm from rfl)
    (show twelveCm.Comparable thirtyCm from rfl)

-- comparable values are governed by the same operator set (§9.15, Table 17.4).
example : fiveCm.scale = twelveCm.scale :=
  PropertyValue.scale_eq_of_comparable rfl

/-! ## (2) Quantity value vs nominal value (§16.10, §12.4) -/

-- "5 cm" is a quantity value: its kind has magnitude.
example : fiveCm.IsQuantityValue := KindOfProperty.rational_isQuantity rfl

-- the blood-group designation is NOT a quantity value.
example : ¬ groupA.IsQuantityValue :=
  PropertyValue.not_quantityValue_of_nominal rfl

/-! ## (3) The value scale (§10.14, §10.16, Table 17.4) -/

-- both length values live on length's (true) value scale …
example : (length.valueScale).Admits fiveCm := rfl
example : (length.valueScale).Admits twelveCm := rfl

-- … and are therefore mutually comparable, read off the scale (§10.14).
example : fiveCm.Comparable twelveCm :=
  ValueScale.comparable_of_mem (s := length.valueScale) rfl rfl

-- length's value scale admits ratios (`×, ÷`).
example : (length.valueScale).scaleType.AllowsRatio :=
  ValueScale.ratio_allows_ratio rfl

-- true vs examined provenance does not change which operations the scale supports.
example :
    ValueScale.scaleType { kind := length, provenance := .true_ }
      = ValueScale.scaleType { kind := length, provenance := .examined } :=
  ValueScale.scaleType_provenance_irrelevant length .true_ .examined

end PropertyKindCalculus.Examples.Value
