/-
# Property value — number-and-reference, gated by kind (Dybkær Ch. 9, 16)

Dybkær (2009), Chapters 9 and 16; aligned with the VIM4 2CD (2023-07-31) *value
of a quantity* (quantity value, 1.24).

  * **§9.15 property value** (value of a property) — "inherent feature of a
    property used in comparing it with other properties of the *same*
    kind-of-property (§6.19)"; it is a member of a conventionally defined set of
    possible values forming a *property value scale* (§10.14).
  * **§16.10 unitary quantity value** (= §12.17 / §12.22.6) — the special case
    whose magnitude is expressed as *a reference quantity multiplied by a number*:
    a numerical value times a reference, with `quantity / unit = numerical value`.

A property value carries the kind it belongs to, so the only well-formed
comparison is *within a kind* (§9.15). That comparability is an **equivalence
relation**, that comparable values are governed by the *same* operator set, and
that the number-times-reference form is a *quantity* value only when the kind has
magnitude (§13.3.1) — these are statements about relations and operations a
description logic can record an instance of, but can neither state nor prove as
laws.
-/

module

public import PropertyKindCalculus.Kind

public section Interface

namespace PropertyKindCalculus

/-- **§9.15 property value** — an inherent feature of a property used in comparing
it with other properties of the *same* kind-of-property. Carried as a kind
together with its representation (§9.15 Note 2): a numeral and the reference the
numeral is taken against. -/
structure PropertyValue where
  /-- §9.15 — the kind-of-property this value belongs to; a value is comparable
  only with values of the same kind. -/
  kind : KindOfProperty
  /-- §16.10 — the numerical value (numeral). For a quantity value the magnitude
  is this number times the `reference`; for a nominal value (§12.4) it is a bare
  type-number / label. -/
  numeral : Int
  /-- §16.10 — the reference the numeral is taken against: a metrological unit id
  for a quantity value (§18.12), or a category/designation id for a nominal one. -/
  reference : String
deriving DecidableEq, Repr

namespace PropertyValue

/-- The scale type governing which operations are defined on this value
(Table 17.4): that of its kind. -/
def scale (v : PropertyValue) : ScaleType := v.kind.scale

/-- **§16.10** — a property value is a *quantity value* iff its kind has magnitude
(is a kind-of-quantity, §13.3.1): only then does the number-times-reference form
carry a metric meaning. -/
@[expose] def IsQuantityValue (v : PropertyValue) : Prop := v.kind.IsQuantity

/-- **§9.15** — two property values are *comparable* iff they are of the same
kind-of-property. Comparison across kinds is not defined. -/
@[expose] def Comparable (v w : PropertyValue) : Prop := v.kind = w.kind

namespace Comparable

/-- Comparability is reflexive: every value is comparable with itself. -/
theorem refl (v : PropertyValue) : v.Comparable v := rfl

/-- Comparability is symmetric. -/
theorem symm {v w : PropertyValue} (h : v.Comparable w) : w.Comparable v :=
  Eq.symm h

/-- Comparability is transitive — the law a description logic cannot state. -/
theorem trans {u v w : PropertyValue}
    (h₁ : u.Comparable v) (h₂ : v.Comparable w) : u.Comparable w :=
  Eq.trans h₁ h₂

end Comparable

/-- Comparable values are governed by the *same* scale type: the same operators
are defined on both (§9.15, Table 17.4). -/
theorem scale_eq_of_comparable {v w : PropertyValue} (h : v.Comparable w) :
    v.scale = w.scale :=
  congrArg KindOfProperty.scale h

/-- **§12.4** — a value of a nominal kind is, by construction, *not* a quantity
value: it has no magnitude. Mirrors `KindOfProperty.nominal_not_quantity`. -/
theorem not_quantityValue_of_nominal {v : PropertyValue} (h : v.kind.IsNominal) :
    ¬ v.IsQuantityValue :=
  KindOfProperty.nominal_not_quantity h

end PropertyValue

end PropertyKindCalculus

end Interface
