import ForMathlib.Combinatorics.Digraph.Reach
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Separators and the weak Menger inequality

`Digraph.IsSeparator G A B S` states that every walk from `A` to `B` meets `S`: removing `S`
disconnects `B` from `A`. This module provides the separator vocabulary and the *weak* —
sound — direction of Menger's theorem (`Digraph.IsSeparator.card_le_of_disjoint`): a family
of pairwise vertex-disjoint `A`–`B` walks injects into any separator, so no separator is
smaller than the largest such family. The equality direction (a disjoint family matching a
minimum separator exists) is a genuinely harder theorem and is deliberately not stated here.

Upstream target: `Mathlib/Combinatorics/Digraph/Separator.lean`.
-/

namespace Digraph

variable {V : Type*} {G : Digraph V} {A B S T : Set V} {a b : V}

/-- `S` separates `A` from `B` when every walk from a vertex of `A` to a vertex of `B`
passes through `S`. Walks of length zero count: a vertex of `A ∩ B` must itself lie in
`S`. -/
def IsSeparator (G : Digraph V) (A B S : Set V) : Prop :=
  ∀ ⦃a b : V⦄, a ∈ A → b ∈ B → ∀ p : G.Walk a b, ∃ v ∈ p.support, v ∈ S

theorem IsSeparator.mono (h : G.IsSeparator A B S) (hST : S ⊆ T) : G.IsSeparator A B T :=
  fun _ _ ha hb p => (h ha hb p).imp fun _ ⟨hv, hvS⟩ => ⟨hv, hST hvS⟩

theorem IsSeparator.anti {A' B' : Set V} (h : G.IsSeparator A B S) (hA : A' ⊆ A)
    (hB : B' ⊆ B) : G.IsSeparator A' B' S :=
  fun _ _ ha hb p => h (hA ha) (hB hb) p

/-- The source side is always a separator. -/
theorem isSeparator_left (G : Digraph V) (A B : Set V) : G.IsSeparator A B A :=
  fun a _ ha _ p => ⟨a, p.start_mem_support, ha⟩

/-- The target side is always a separator. -/
theorem isSeparator_right (G : Digraph V) (A B : Set V) : G.IsSeparator A B B :=
  fun _ b _ hb p => ⟨b, p.end_mem_support, hb⟩

/-- A separator disconnects: with `S` empty there is no walk from `A` to `B` at all. -/
theorem IsSeparator.not_reachable (h : G.IsSeparator A B ∅) (ha : a ∈ A) (hb : b ∈ B) :
    ¬G.Reachable a b := by
  rintro ⟨p⟩
  obtain ⟨v, -, hv⟩ := h ha hb p
  exact hv

/-- **The weak Menger inequality.** A family of pairwise vertex-disjoint `A`–`B` walks
injects into any separator — each walk meets the separator, and disjointness makes the
meeting vertices distinct — so no separator is smaller than the family. -/
theorem IsSeparator.card_le_of_disjoint {ι : Type*} (hS : G.IsSeparator A B S)
    (hSfin : S.Finite) {wa wb : ι → V} (w : ∀ i, G.Walk (wa i) (wb i))
    (ha : ∀ i, wa i ∈ A) (hb : ∀ i, wb i ∈ B)
    (hdisj : Pairwise fun i j => ∀ v, v ∈ (w i).support → v ∈ (w j).support → False) :
    Nat.card ι ≤ S.ncard := by
  have hmeet : ∀ i, ∃ v ∈ (w i).support, v ∈ S := fun i => hS (ha i) (hb i) (w i)
  choose f hf hfS using hmeet
  have := hSfin.to_subtype
  have hinj : Function.Injective fun i => (⟨f i, hfS i⟩ : S) := by
    intro i j hij
    by_contra hne
    have hfeq : f i = f j := congrArg Subtype.val hij
    exact hdisj hne (f i) (hf i) (by rw [hfeq]; exact hf j)
  calc Nat.card ι ≤ Nat.card S := Nat.card_le_card_of_injective _ hinj
    _ = S.ncard := Nat.card_coe_set_eq S

end Digraph
