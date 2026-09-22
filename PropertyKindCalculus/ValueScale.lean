/-
# Property value scale — the ordered set a value lives in (Dybkær Ch. 10, 17)

Dybkær (2009), Chapters 10 and 17; aligned with the VIM4 2CD (2023-07-31)
*measurement scale* (1.23 — the term the VIM3 called "quantity-value scale").

  * **§10.14 property value scale** (scale of values of properties, scale) —
    "ordered set of possible, mutually comparable property values (§9.15)", used
    to order and compare instances of a given kind-of-property (§6.19).
  * **§10.16 generic division** — a value scale is *true* (§10.16.1, consistent
    with the definitions of the corresponding properties) or *examined* (§10.16.2,
    obtained by following an examination procedure), exactly paralleling §9.17 /
    §9.19 for the values themselves.
  * **Table 17.4** — which statistical manipulations a scale admits is fixed by
    its scale type (Ch. 12), so the value scale inherits the proved operator
    gating of `ScaleType`.

The defining law — *a value scale holds only mutually comparable values* (§10.14)
— quantifies over the scale's members and so is, again, outside what a
description logic can express; here it is proved, as is the inheritance of
operator-availability monotonicity from the scale layer.
-/

module

public import PropertyKindCalculus.PropertyValue

public section -- pkc-blanket

namespace PropertyKindCalculus

/-- **§10.16 provenance** of a value scale: whether it is a *true* or an
*examined* property-value scale. -/
inductive ScaleProvenance
  /-- §10.16.1 true property-value scale — consistent with the definitions of the
  corresponding properties (§5.5). -/
  | true_
  /-- §10.16.2 examined property-value scale — obtained by following an
  examination procedure (§7.3). -/
  | examined
deriving DecidableEq, Repr

/-- **§10.14 property value scale** — the ordered set of possible, mutually
comparable property values of one kind. Carried as that kind together with its
provenance (§10.16). -/
structure ValueScale where
  /-- §10.14 — the kind-of-property whose values this scale orders. -/
  kind : KindOfProperty
  /-- §10.16 — whether this is a true or an examined property-value scale. -/
  provenance : ScaleProvenance := .true_
deriving DecidableEq, Repr

namespace ValueScale

/-- The scale type the value scale is governed by — the datum Table 17.4 uses to
gate which manipulations a scale admits. -/
@[expose] def scaleType (s : ValueScale) : ScaleType := s.kind.scale

/-- **§10.14** — a value scale *admits* a value iff the value is of the scale's
kind. (Membership is the value-layer side of "of a given kind-of-property".) -/
@[expose] def Admits (s : ValueScale) (v : PropertyValue) : Prop := v.kind = s.kind

/-- **§10.14 — a value scale holds only mutually comparable values.** Any two
values a scale admits are of the scale's kind, and so are comparable. This is the
defining property of a value scale, and it quantifies over the scale's members. -/
theorem comparable_of_mem {s : ValueScale} {v w : PropertyValue}
    (hv : s.Admits v) (hw : s.Admits w) : v.Comparable w := by
  unfold Admits at hv hw
  unfold PropertyValue.Comparable
  exact hv.trans hw.symm

/-- **Table 17.4 / §10.16** — true and examined value scales of one kind share
their scale type: the examination provenance does not change which operations the
scale supports. (The value-scale analogue of a refinement preserving structure.) -/
theorem scaleType_provenance_irrelevant (k : KindOfProperty) (p q : ScaleProvenance) :
    scaleType { kind := k, provenance := p } = scaleType { kind := k, provenance := q } :=
  rfl

/-- **Table 17.4** — a ratio value scale admits ratios (`×, ÷`). -/
theorem ratio_allows_ratio {s : ValueScale} (h : s.scaleType = .ratio) :
    s.scaleType.AllowsRatio := by
  rw [h]; trivial

/-- **Table 17.4** — operator availability is *monotone* in the scale type: a
value scale whose type is at least another's licenses every manipulation the
poorer one does. Inherited directly from the proved scale-layer monotonicity. -/
theorem allows_mono_of_le {s t : ValueScale} (h : s.scaleType ≤ t.scaleType) :
    (s.scaleType.AllowsOrder → t.scaleType.AllowsOrder)
      ∧ (s.scaleType.AllowsDifference → t.scaleType.AllowsDifference)
      ∧ (s.scaleType.AllowsRatio → t.scaleType.AllowsRatio) :=
  ScaleType.allows_mono h

end ValueScale

/-- **§9.15 ↔ §10.14** — every kind induces its canonical *true* value scale, the
set of its possible values. This is the link §9.15 names: a property value is a
member of the value scale formed by its kind. -/
@[expose] def KindOfProperty.valueScale (k : KindOfProperty) : ValueScale := { kind := k }

/-- A value is on its kind's value scale exactly when it is of that kind. -/
theorem KindOfProperty.mem_valueScale {k : KindOfProperty} {v : PropertyValue} :
    (k.valueScale).Admits v ↔ v.kind = k :=
  Iff.rfl

end PropertyKindCalculus

end -- pkc-blanket
