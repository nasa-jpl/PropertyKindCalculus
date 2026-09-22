/-
# Specialization and mutual comparability

The OML relation `Specializes` runs `GeneralUnitaryQuantity → GeneralUnitary
Quantity` — i.e. it relates *kinds* to *kinds*. Flater (NIST TN 1943, §6.2)
stresses that the result need not be a tree but may be a **lattice**.

We generate `Specializes` as the reflexive–transitive closure of an
application-supplied *direct-parent* edge relation `E`. Different "systems of
quantities" supply different `E`, so the hierarchy is open and per-application —
exactly the extensibility a fixed `inductive` would deny.

That `Specializes` is a preorder, and that mutual comparability is reflexive and
symmetric, are stated and **proved** here. Stating — let alone proving — such
algebraic laws is outside what an OWL2 reasoner can do.
-/

module

public import PropertyKindCalculus.Kind

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus

/-- Reflexive–transitive closure of a direct-parent edge relation `E`. -/
inductive Specializes (E : KindOfProperty → KindOfProperty → Prop) :
    KindOfProperty → KindOfProperty → Prop
  /-- Reflexivity of the closure: every kind specializes itself. -/
  | refl (a : KindOfProperty) : Specializes E a a
  /-- Prepend a direct-parent edge `E a b` to a specialization `b ⊑ c`. -/
  | step {a b c : KindOfProperty} : E a b → Specializes E b c → Specializes E a c

namespace Specializes

variable {E : KindOfProperty → KindOfProperty → Prop}

/-- A single parent edge specializes. -/
theorem of_edge {a b : KindOfProperty} (h : E a b) : Specializes E a b :=
  Specializes.step h (Specializes.refl b)

/-- Specialization is transitive (it is a preorder, together with `refl`). -/
theorem trans {a b c : KindOfProperty}
    (h₁ : Specializes E a b) (h₂ : Specializes E b c) : Specializes E a c := by
  induction h₁ with
  | refl _ => exact h₂
  | step hab _ ih => exact Specializes.step hab (ih h₂)

end Specializes

/-- **Dybkær §6 / VIM4 2CD 1.2** (quantities of the same kind) — two kinds are
*mutually comparable* (belong to one broad kind) iff they share a common
super-kind. This is how `width` and `height` remain comparable as lengths even
though they are distinct sub-kinds. -/
def MutuallyComparable (E : KindOfProperty → KindOfProperty → Prop)
    (a b : KindOfProperty) : Prop :=
  ∃ p, Specializes E a p ∧ Specializes E b p

namespace MutuallyComparable

variable {E : KindOfProperty → KindOfProperty → Prop}

theorem refl (a : KindOfProperty) : MutuallyComparable E a a :=
  ⟨a, .refl a, .refl a⟩

theorem symm {a b : KindOfProperty}
    (h : MutuallyComparable E a b) : MutuallyComparable E b a :=
  let ⟨p, ha, hb⟩ := h; ⟨p, hb, ha⟩

/-- If `a` specializes `b`, they are mutually comparable (witness `b`). -/
theorem of_specializes {a b : KindOfProperty}
    (h : Specializes E a b) : MutuallyComparable E a b :=
  ⟨b, h, .refl b⟩

end MutuallyComparable

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
