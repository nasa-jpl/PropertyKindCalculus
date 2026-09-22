/-
# Examination — principle, method, procedure (defining aspects)

Dybkær (2009), Chapters 7 and 14; aligned with the VIM4 2CD (2023-07-31)
measurement-process vocabulary.

  * **§7.5 examination principle** (VIM4 2CD 2.4 *measurement principle*) — the
    phenomenon serving as the basis of an examination (e.g. the thermal expansion
    of a liquid, for a temperature measurement).
  * **examination method** (Dybkær Ch. 7; VIM4 2CD 2.5 *measurement method*) — a
    generic, logical description of the operations of an examination, *based on* a
    principle.
  * **examination procedure** (Dybkær Ch. 7; VIM4 2CD 2.7 *measurement
    procedure*) — a detailed, application-specific description, *based on* a
    method.

These refine one another (procedure ⊑ method ⊑ principle, by the "based-on"
relation) and are *defining aspects* of a kind-of-property (§6.19, §7.5): two
properties examined by different principles are different kinds, even when their
scale (and, later, their dimension) coincide. This is exactly what keeps width
and height apart while both remain lengths.

Like `Specializes`, the refinement relation is an algebraic *law* — reflexive,
transitive, and principle-preserving — none of which a description logic can
state, let alone prove.
-/

module

public import PropertyKindCalculus.Kind

public section -- pkc-blanket

namespace PropertyKindCalculus

/-- **§7.5 examination principle** (VIM4 2CD 2.4) — the phenomenon serving as the
basis of an examination. Carries a terminological `id` (OML-style). -/
structure ExaminationPrinciple where
  /-- Terminological identity of the examination principle (OML-style). -/
  id : String
deriving DecidableEq, Repr

/-- **Examination method** (Dybkær Ch. 7; VIM4 2CD 2.5) — a generic description of
an examination, *based on* an `ExaminationPrinciple`. -/
structure ExaminationMethod where
  /-- Terminological identity of the examination method. -/
  id : String
  /-- The principle this method is based on. -/
  principle : ExaminationPrinciple
deriving DecidableEq, Repr

/-- **Examination procedure** (Dybkær Ch. 7; VIM4 2CD 2.7) — a detailed
description, *based on* an `ExaminationMethod`. -/
structure ExaminationProcedure where
  /-- Terminological identity of the examination procedure. -/
  id : String
  /-- The method this procedure is based on. -/
  method : ExaminationMethod
deriving DecidableEq, Repr

/-- The principle a procedure ultimately rests on, via its method. -/
@[expose] def ExaminationProcedure.principle (q : ExaminationProcedure) : ExaminationPrinciple :=
  q.method.principle

/-- The three layers of the examination refinement chain, gathered into one
carrier so that "based-on" / "refines" is a *homogeneous* relation. -/
inductive ExaminationItem
  /-- An examination principle — the base layer of the chain. -/
  | principle (p : ExaminationPrinciple)
  /-- An examination method, viewed as an item of the chain. -/
  | method    (m : ExaminationMethod)
  /-- An examination procedure, viewed as an item of the chain. -/
  | procedure (q : ExaminationProcedure)
deriving DecidableEq, Repr

namespace ExaminationItem

/-- The principle at the base of an item's based-on chain — the forgetful
projection of any examination down to its principle layer. -/
@[expose] def basePrinciple : ExaminationItem → ExaminationPrinciple
  | principle p => p
  | method m    => m.principle
  | procedure q => q.principle

end ExaminationItem

/-- The defining **"based-on"** edges (VIM4 2CD): a method is based on its
principle, a procedure on its method. -/
inductive BasedOn : ExaminationItem → ExaminationItem → Prop
  /-- A method is based on the principle it cites. -/
  | method_principle (m : ExaminationMethod) :
      BasedOn (.method m) (.principle m.principle)
  /-- A procedure is based on the method it cites. -/
  | procedure_method (q : ExaminationProcedure) :
      BasedOn (.procedure q) (.method q.method)

/-- **Refinement** of examinations: the reflexive–transitive closure of
`BasedOn`. A more specific examination *refines* a more generic one
(procedure ⊑ method ⊑ principle). Mirrors `Specializes` over kinds. -/
inductive Refines : ExaminationItem → ExaminationItem → Prop
  /-- Reflexivity of the closure: every examination refines itself. -/
  | refl (a : ExaminationItem) : Refines a a
  /-- Prepend a based-on edge `BasedOn a b` to a refinement `b ⊑ c`. -/
  | step {a b c : ExaminationItem} : BasedOn a b → Refines b c → Refines a c

namespace BasedOn

/-- A single based-on edge preserves the base principle. -/
theorem basePrinciple_eq {a b : ExaminationItem} (h : BasedOn a b) :
    a.basePrinciple = b.basePrinciple := by
  cases h <;> rfl

end BasedOn

namespace Refines

/-- A based-on edge is a refinement. -/
theorem of_basedOn {a b : ExaminationItem} (h : BasedOn a b) : Refines a b :=
  Refines.step h (Refines.refl b)

/-- Refinement is transitive (a preorder, together with `refl`). -/
theorem trans {a b c : ExaminationItem}
    (h₁ : Refines a b) (h₂ : Refines b c) : Refines a c := by
  induction h₁ with
  | refl _ => exact h₂
  | step hab _ ih => exact Refines.step hab (ih h₂)

/-- **Coherence — refinement preserves the principle.** Every examination in one
refinement chain rests on the *same* principle: a procedure, the method it is
based on, and the principle under that all share one base principle. The
forgetful projection `basePrinciple` is invariant along `Refines` — the
examination analogue of `dim` being a homomorphism, and a law no description
logic can phrase. -/
theorem basePrinciple_eq {a b : ExaminationItem} (h : Refines a b) :
    a.basePrinciple = b.basePrinciple := by
  induction h with
  | refl _ => rfl
  | step hab _ ih => exact (hab.basePrinciple_eq).trans ih

end Refines

/-- A kind is **examined by** a principle when its terminological
examination-principle link (§7.5) names that principle. The link is by `id`,
mirroring how OML relates a kind to its defining aspects. -/
@[expose] def KindOfProperty.examinedBy (k : KindOfProperty) (p : ExaminationPrinciple) : Prop :=
  k.examPrinciple = some p.id

/-- **§7.5 — the examination principle is a defining aspect.** Two kinds examined
by different principles are *distinct kinds* — independently of scale and (later)
dimension. This is what individuates otherwise-comparable kinds such as width and
height: same scale, same dimension, different examination principle, hence
different kinds. -/
theorem KindOfProperty.distinct_of_examPrinciple {k₁ k₂ : KindOfProperty}
    (h : k₁.examPrinciple ≠ k₂.examPrinciple) : k₁ ≠ k₂ := by
  intro hk; subst hk; exact h rfl

end PropertyKindCalculus

end -- pkc-blanket
