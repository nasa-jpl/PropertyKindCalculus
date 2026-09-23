/-
# Kind-of-property and kind-of-quantity

Dybkær (2009), Chapters 6 and 13.

  * **§6.19 kind-of-property** — "common defining aspect of mutually comparable
    properties."
  * **§13.3.1 kind-of-quantity** — a kind-of-property for properties *having a
    magnitude*.

Design choices (see the project README for rationale):

  * A kind is an **open value** (`structure`), so applications declare new kinds
    as `def`s without editing a central enum — Dybkær's ontology is open, and a
    fixed `inductive` would not be extensible.
  * A kind carries its `scale` (Ch. 12) and an optional `examPrinciple` (§7.5).
    Dybkær's 1993 definition tied kind-of-quantity to *how a value is obtained*;
    the examination principle is therefore a legitimate *defining aspect* that
    can individuate otherwise-comparable kinds (e.g. width vs. height).
-/

module

public import PropertyKindCalculus.Scale
public import PropertyKindCalculus.Foundations

public section Interface

namespace PropertyKindCalculus

-- `@[expose] section` rather than an attribute: `deriving DecidableEq` generates
-- `instDecidableEqKindOfProperty.decEq`, and a generated declaration carries no attribute of
-- its own. Kind identity is decided by the kernel all over this library and downstream, so
-- this body is part of the contract rather than an implementation detail.
@[expose] section
/-- **§6.19 kind-of-property** — common defining aspect of mutually comparable
properties. In four-category terms (Lowe, Fig. 7.1) this is the *Attributes* corner —
the non-substantial universal, instantiated by individual quantities (its modes) and
characterizing sorts of system through the §20 dedicated kinds. -/
structure KindOfProperty where
  /-- Terminological identity (mirrors the OML `id`). -/
  id : String
  /-- The scale type (Ch. 12) — which operations are defined on its instances. -/
  scale : ScaleType
  /-- **§7.5 examination principle** used as a defining aspect, when present. -/
  examPrinciple : Option String := none
deriving DecidableEq, Repr
end

namespace KindOfProperty

/-- **§13.3.1** — a kind-of-property is a *kind-of-quantity* iff its instances
have a magnitude. -/
@[expose] def IsQuantity (k : KindOfProperty) : Prop := k.scale.HasMagnitude

/-! ## The scale-based generic division of ⟨kind-of-property⟩ (§13.2) -/

/-- §13.2.1 nominal kind-of-property (no magnitude, comparable for equality). -/
@[expose] def IsNominal (k : KindOfProperty) : Prop := k.scale = .nominal
/-- §13.2.2 ordinal kind-of-property (rankable, not subtractive). -/
@[expose] def IsOrdinal (k : KindOfProperty) : Prop := k.scale = .ordinal
/-- §13.2.3 differential kind-of-property (subtractive, not divisible). -/
@[expose] def IsDifferential (k : KindOfProperty) : Prop := k.scale = .interval
/-- §13.2.4 rational kind-of-property (divisible). -/
@[expose] def IsRational (k : KindOfProperty) : Prop := k.scale = .ratio

/-- A nominal kind is, by construction, not a kind-of-quantity (§13.3.1). -/
theorem nominal_not_quantity {k : KindOfProperty} (h : k.IsNominal) : ¬ k.IsQuantity := by
  simp [IsQuantity, IsNominal, ScaleType.HasMagnitude] at *
  simp [h]

/-- A rational kind *is* a kind-of-quantity. -/
theorem rational_isQuantity {k : KindOfProperty} (h : k.IsRational) : k.IsQuantity := by
  simp [IsQuantity, IsRational, ScaleType.HasMagnitude] at *
  simp [h]

end KindOfProperty

-- `@[expose] section`, not an attribute: a structure cannot carry `@[expose]`. An
-- individual property is compared for identity by the kernel in the object-type examples.
@[expose] section
/-- The **instance** layer (OML `IndividualUnitaryQuantity`). An individual
property *instantiates* a kind and *characterizes* an object.

This is deliberately a **term**, not a subtype of its kind: the relation
"the width of this pencil" ↦ "Width" is *instantiation*, not *specialization*.
Specialization is a relation among kinds (see `PropertyKindCalculus.Specialization`). -/
structure IndividualProperty where
  /-- OML `Instantiates`: the kind this individual is an instance of. -/
  kind : KindOfProperty
  /-- OML `Characterizes`: the object whose feature this is. -/
  carrier : Object
end

end PropertyKindCalculus

end Interface
