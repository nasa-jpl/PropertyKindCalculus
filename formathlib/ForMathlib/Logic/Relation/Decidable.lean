module

public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Card

/-!
# Decidability of `Relation.ReflTransGen` and `Relation.TransGen` on a `Fintype`

`Relation.ReflTransGen r` is the reachability relation of `r`. On a `Fintype` with decidable
equality and a decidable relation it is itself decidable: `b` is reachable from `a` iff `b` is
a member of the saturation of `{a}` under one-step successors, and on a finite type the
saturation is complete after `Fintype.card α` steps, because each step before the fixpoint
strictly grows the set. `Relation.TransGen` follows through `Relation.TransGen.head'_iff`.

The saturation itself (`Relation.reachSet`) is an executable forward-closure computation, so
these instances make reachability facts on concrete finite relations provable by `decide` and
computable by `#eval`.

Upstream target: `Mathlib/Logic/Relation.lean` (or a `Decidable` satellite of it) — Mathlib
has no decidability instance for either closure.
-/

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace Relation

variable {α : Type*} [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]

/-- One saturation step of reachability: `s` together with every one-step `r`-successor of a
member of `s`. -/
def stepSet (s : Finset α) : Finset α :=
  s ∪ Finset.univ.filter fun b => ∃ a ∈ s, r a b

variable {s : Finset α} {a b : α}

theorem mem_stepSet : b ∈ stepSet r s ↔ b ∈ s ∨ ∃ a ∈ s, r a b := by
  simp [stepSet]

theorem subset_stepSet : s ⊆ stepSet r s := Finset.subset_union_left

theorem subset_stepSet_iterate : ∀ n, s ⊆ (stepSet r)^[n] s
  | 0 => subset_refl s
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact (subset_stepSet_iterate n).trans (subset_stepSet r)

private theorem le_card_stepSet_iterate :
    ∀ n, (∀ m < n, stepSet r ((stepSet r)^[m] s) ≠ (stepSet r)^[m] s) →
      n + s.card ≤ (((stepSet r)^[n] s)).card
  | 0, _ => by simp
  | n + 1, h => by
    have hne := h n (Nat.lt_succ_self n)
    have hlt : ((stepSet r)^[n] s).card < ((stepSet r)^[n + 1] s).card := by
      rw [Function.iterate_succ_apply']
      exact Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr ⟨subset_stepSet r, Ne.symm hne⟩)
    have := le_card_stepSet_iterate n fun m hm => h m (hm.trans (Nat.lt_succ_self n))
    omega

/-- Saturation from a singleton seed is a fixpoint of `stepSet` after `Fintype.card α`
steps: each non-fixpoint step strictly grows the set, and a `Finset` cannot outgrow the
type. -/
theorem stepSet_iterate_card_fixed (a : α) :
    stepSet r ((stepSet r)^[Fintype.card α] {a}) = (stepSet r)^[Fintype.card α] {a} := by
  obtain ⟨m, hm, hfix⟩ :
      ∃ m < Fintype.card α, stepSet r ((stepSet r)^[m] {a}) = (stepSet r)^[m] {a} := by
    by_contra h
    push Not at h
    have hbound := le_card_stepSet_iterate r (s := {a}) (Fintype.card α) fun m hm => h m hm
    have hcap : (((stepSet r)^[Fintype.card α] ({a} : Finset α))).card ≤ Fintype.card α :=
      Finset.card_le_univ _
    simp only [Finset.card_singleton] at hbound
    omega
  have hstable : (stepSet r)^[Fintype.card α] ({a} : Finset α) = (stepSet r)^[m] {a} := by
    conv_lhs => rw [show Fintype.card α = (Fintype.card α - m) + m from
      (Nat.sub_add_cancel hm.le).symm]
    rw [Function.iterate_add_apply, Function.iterate_fixed hfix]
  rw [hstable, hfix]

/-- The set of points `ReflTransGen r`-reachable from `a`, as an executable forward
closure. -/
def reachSet (a : α) : Finset α := (stepSet r)^[Fintype.card α] {a}

theorem stepSet_reachSet (a : α) : stepSet r (reachSet r a) = reachSet r a :=
  stepSet_iterate_card_fixed r a

@[simp]
theorem mem_reachSet : b ∈ reachSet r a ↔ ReflTransGen r a b := by
  constructor
  · suffices h : ∀ n (x : α), x ∈ (stepSet r)^[n] {a} → ReflTransGen r a x from h _ b
    intro n
    induction n with
    | zero => intro x hx; rw [Finset.mem_singleton.mp hx]
    | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply'] at hx
      rcases (mem_stepSet r).mp hx with h | ⟨c, hc, hcx⟩
      · exact ih x h
      · exact (ih c hc).tail hcx
  · intro h
    induction h with
    | refl => exact subset_stepSet_iterate r _ (Finset.mem_singleton_self a)
    | tail _ hbc ih =>
      rw [← stepSet_reachSet r a]
      exact (mem_stepSet r).mpr (Or.inr ⟨_, ih, hbc⟩)

instance : DecidableRel (ReflTransGen r) := fun _ b =>
  decidable_of_iff (b ∈ reachSet r _) (mem_reachSet r)

instance : DecidableRel (TransGen r) := fun a c =>
  decidable_of_iff (∃ b, r a b ∧ ReflTransGen r b c) TransGen.head'_iff.symm

end Relation

end -- pkc-blanket-expose
end -- pkc-blanket
