/-
# Metrological unit — the chosen reference quantity of a kind (Dybkær Ch. 18, §13.3.3)

Dybkær (2009), Chapter 18 and §13.3.3; aligned with the VIM4 2CD (2023-07-31)
*measurement unit* (1.12).

  * **§18.12 metrological unit** — Dybkær's §9.13.4 quotes the VIM definition:
    "real scalar quantity, defined and adopted by convention, with which any other
    quantity of the *same kind* can be compared to express the ratio of the two
    quantities as a number" (VIM4 2CD 1.12). It is, concretely, one quantity of a
    kind *chosen as the reference* (§6.9: "among which one is chosen as a reference
    quantity, here kilogram, under the concept unit of measurement").
  * **§13.3.3 unitary kind-of-quantity** — a kind-of-quantity "for quantities with
    magnitudes expressed as *a reference quantity multiplied by a number*"; the
    NOTE adds "the reference quantity is a metrological unit (§18.12)". So a
    metrological unit belongs to a *unitary* kind — differential (§13.3.4) or
    rational (§13.3.5). Dybkær §9.13.4 is explicit that **ordinal quantities are
    not related to metrological units**, and nominal ones have no magnitude at all.

Two theses are checked here that a description logic can record an instance of but
can neither state nor prove as laws. First, *commensurability* — "of the same
kind", the only relation along which units convert — is an **equivalence relation**
(a metre and a centimetre are commensurable; a metre and a kilogram are not, and
that is a type-level fact, not a runtime check). Second, the §13.3.3
*number-and-reference* form is a faithful **round-trip**: measuring a quantity in a
unit yields a numeral, and re-applying the unit to that numeral recovers the value
(`quantity / unit = number`, `number × unit = quantity`), gated so that only a
unitary kind bears a unit and only then is the result a quantity value.
-/

module

public import PropertyKindCalculus.ValueScale

public section Interface

namespace PropertyKindCalculus

/-- **§13.3.3 — a kind *bears a metrological unit* (is a unitary kind-of-quantity)**
iff its scale is at least differential: its magnitudes are "a reference quantity
multiplied by a number" (§13.3.4 differential, §13.3.5 rational). Ordinal and
nominal kinds do **not** bear a unit (Dybkær §9.13.4). -/
@[expose] def KindOfProperty.BearsUnit (k : KindOfProperty) : Prop := k.scale.AllowsDifference

/-- **§9.13.4** — a nominal kind bears no metrological unit: it has no magnitude. -/
theorem KindOfProperty.nominal_bears_no_unit {k : KindOfProperty} (h : k.IsNominal) :
    ¬ k.BearsUnit := by
  unfold KindOfProperty.BearsUnit
  unfold KindOfProperty.IsNominal at h
  rw [h]
  intro hc
  exact (hc : False)

/-- **§9.13.4 — ordinal quantities are not related to metrological units.** An
ordinal kind is rankable but its magnitudes are not a reference-times-number, so it
bears no unit. (The exclusion scale-and-dimension reasoning would miss.) -/
theorem KindOfProperty.ordinal_bears_no_unit {k : KindOfProperty} (h : k.IsOrdinal) :
    ¬ k.BearsUnit := by
  unfold KindOfProperty.BearsUnit
  unfold KindOfProperty.IsOrdinal at h
  rw [h]
  intro hc
  exact (hc : False)

/-- **§13.3.5** — a rational kind bears a metrological unit. -/
theorem KindOfProperty.rational_bears_unit {k : KindOfProperty} (h : k.IsRational) :
    k.BearsUnit := by
  unfold KindOfProperty.BearsUnit
  unfold KindOfProperty.IsRational at h
  rw [h]
  trivial

/-- **§13.3.3 ⊂ §13.3.1** — bearing a unit (being unitary) implies being a
kind-of-quantity: a reference-times-number magnitude is, in particular, a
magnitude. -/
theorem KindOfProperty.bearsUnit_isQuantity {k : KindOfProperty} (h : k.BearsUnit) :
    k.IsQuantity := by
  unfold KindOfProperty.BearsUnit at h
  unfold KindOfProperty.IsQuantity
  cases hs : k.scale <;>
    simp_all [ScaleType.AllowsDifference, ScaleType.HasMagnitude]

/-- **§18.12 metrological unit** — one quantity of a kind chosen as the reference,
"with which any other quantity of the same kind can be compared". Carried as the
kind it references together with its terminological `symbol` (the §18.12 unit id,
e.g. `"m"`, `"kg"`). Like `KindOfProperty`, it is an open value so applications
declare units as `def`s. -/
structure MetrologicalUnit where
  /-- §18.12 / §13.3.3 — the kind whose quantities this unit references. A
  well-formed unit's kind must bear a unit (`WellFormed`). -/
  kind : KindOfProperty
  /-- §18.12 — the terminological identity of the unit (the unit id, e.g. `"m"`). -/
  symbol : String
deriving DecidableEq, Repr

namespace MetrologicalUnit

/-- **§18.12** — a metrological unit is *well-formed* iff its kind actually bears a
unit (§13.3.3): there is no metrological unit of a nominal or ordinal kind. -/
@[expose] def WellFormed (u : MetrologicalUnit) : Prop := u.kind.BearsUnit

/-- A metrological unit of a nominal kind is ill-formed (§9.13.4). -/
theorem not_wellFormed_of_nominal {u : MetrologicalUnit} (h : u.kind.IsNominal) :
    ¬ u.WellFormed :=
  KindOfProperty.nominal_bears_no_unit h

/-- A metrological unit of an ordinal kind is ill-formed (§9.13.4). -/
theorem not_wellFormed_of_ordinal {u : MetrologicalUnit} (h : u.kind.IsOrdinal) :
    ¬ u.WellFormed :=
  KindOfProperty.ordinal_bears_no_unit h

/-- **§9.13.4 "of the same kind"** — two units are *commensurable* iff they
reference the same kind. This is the only relation along which a value converts:
a metre and a centimetre are commensurable (both length); a metre and a kilogram
are not — and that is a fact of the types, not a runtime guard. -/
@[expose] def Commensurable (u₁ u₂ : MetrologicalUnit) : Prop := u₁.kind = u₂.kind

namespace Commensurable

/-- Commensurability is reflexive. -/
theorem refl (u : MetrologicalUnit) : u.Commensurable u := by rw [Commensurable]

/-- Commensurability is symmetric. -/
theorem symm {u₁ u₂ : MetrologicalUnit} (h : u₁.Commensurable u₂) :
    u₂.Commensurable u₁ :=
  Eq.symm h

/-- Commensurability is transitive — the law a description logic cannot state. -/
theorem trans {u₁ u₂ u₃ : MetrologicalUnit}
    (h₁ : u₁.Commensurable u₂) (h₂ : u₂.Commensurable u₃) : u₁.Commensurable u₃ :=
  Eq.trans h₁ h₂

end Commensurable

/-! ## Number and reference (§13.3.3) -/

/-- **§13.3.3 — a magnitude expressed as a reference quantity multiplied by a
number.** Measuring `n` of this unit is the property value "`n` × `symbol`": the
numeral `n` taken against this unit's reference. -/
def measure (u : MetrologicalUnit) (n : Int) : PropertyValue :=
  { kind := u.kind, numeral := n, reference := u.symbol }

@[simp] theorem measure_kind (u : MetrologicalUnit) (n : Int) :
    (u.measure n).kind = u.kind := by rw [measure]

/-- **`quantity / unit = number`** — the numeral read back off a measured value is
the number it was measured with. -/
@[simp] theorem measure_numeral (u : MetrologicalUnit) (n : Int) :
    (u.measure n).numeral = n := by rw [measure]

@[simp] theorem measure_reference (u : MetrologicalUnit) (n : Int) :
    (u.measure n).reference = u.symbol := by rw [measure]

/-- **§16.10** — measuring in a *well-formed* unit yields a *quantity* value: the
result has a magnitude because the unit's kind is a kind-of-quantity (§13.3.3). -/
theorem measure_isQuantityValue {u : MetrologicalUnit} (h : u.WellFormed) (n : Int) :
    (u.measure n).IsQuantityValue :=
  KindOfProperty.bearsUnit_isQuantity h

/-- **§13.3.3 — a value *is measured in* a unit** iff it is of the unit's kind and
taken against the unit's reference. (The value-side reading of "reference quantity
multiplied by a number".) -/
def Measures (u : MetrologicalUnit) (v : PropertyValue) : Prop :=
  v.kind = u.kind ∧ v.reference = u.symbol

/-- Every value the unit produces is, by construction, measured in that unit. -/
theorem measures_measure (u : MetrologicalUnit) (n : Int) : u.Measures (u.measure n) :=
  ⟨rfl, rfl⟩

/-- **`number × unit = quantity`** — re-applying a unit to the numeral of a value
measured in it recovers the value exactly. Together with `measure_numeral` this is
the §13.3.3 number-and-reference *round-trip*: the unit is a faithful reference. -/
theorem measure_eq_of_measures {u : MetrologicalUnit} {v : PropertyValue}
    (h : u.Measures v) : u.measure v.numeral = v := by
  obtain ⟨hk, hr⟩ := h
  unfold MetrologicalUnit.measure
  rw [← hk, ← hr]

/-- **§9.13.4** — values measured in *commensurable* units are comparable: they are
of the same kind, so the value-layer comparison (§9.15) is defined on them. -/
theorem comparable_of_measures {u₁ u₂ : MetrologicalUnit} {v w : PropertyValue}
    (hv : u₁.Measures v) (hw : u₂.Measures w) (hc : u₁.Commensurable u₂) :
    v.Comparable w := by
  unfold PropertyValue.Comparable
  unfold MetrologicalUnit.Commensurable at hc
  exact hv.1.trans (hc.trans hw.1.symm)

/-! ## The unit and its value scale (§10.14, §18.12) -/

/-- A value measured in a unit lives on that unit's kind's value scale (§10.14):
the scale of the kind the unit references. -/
theorem measure_on_valueScale (u : MetrologicalUnit) (n : Int) :
    (u.kind.valueScale).Admits (u.measure n) := by
  rw [measure, ValueScale.Admits, KindOfProperty.valueScale]

/-- **§9.13.4 / §10.14** — commensurable units reference the *same* value scale:
"of the same kind" is exactly "ordered by the same value scale". -/
theorem valueScale_eq_of_commensurable {u₁ u₂ : MetrologicalUnit}
    (h : u₁.Commensurable u₂) : u₁.kind.valueScale = u₂.kind.valueScale :=
  congrArg KindOfProperty.valueScale h

end MetrologicalUnit

/-- **§13.3.3** — the metrological units a kind admits are exactly references to
that kind; this canonical constructor builds one from a kind and a symbol. -/
@[expose] def KindOfProperty.unit (k : KindOfProperty) (symbol : String) : MetrologicalUnit :=
  { kind := k, symbol := symbol }

/-- A canonical unit of a kind references that kind: it is commensurable with every
other unit of the kind. -/
theorem KindOfProperty.unit_commensurable (k : KindOfProperty) (s₁ s₂ : String) :
    (k.unit s₁).Commensurable (k.unit s₂) := by
  rw [KindOfProperty.unit, MetrologicalUnit.Commensurable]; rfl

end PropertyKindCalculus

end Interface
