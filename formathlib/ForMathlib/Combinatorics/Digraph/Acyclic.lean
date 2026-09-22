module

public import ForMathlib.Combinatorics.Digraph.Reach
public import Mathlib.Order.Extension.Linear
public import Mathlib.Data.Fintype.Sort

/-!
# Acyclic digraphs

A digraph is acyclic when no vertex reaches itself through at least one edge. On an acyclic
digraph reachability is a partial order (`Digraph.IsAcyclic.isPartialOrder`); gluing that to
the Szpilrajn extension theorem yields a linear extension of reachability
(`Digraph.IsAcyclic.exists_linear_extension`), and hence, on a finite vertex type, a
topological sort: an injective rank function under which every edge increases rank
(`Digraph.IsAcyclic.exists_rank`), equivalently a duplicate-free enumeration of the vertices
listing every edge's source before its target (`Digraph.IsAcyclic.exists_topologicalSort`).

Upstream target: `Mathlib/Combinatorics/Digraph/Acyclic.lean`.
-/

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace Digraph

variable {V : Type*} {G : Digraph V} {a b : V}

/-- A digraph is acyclic when no vertex reaches itself through at least one edge. -/
def IsAcyclic (G : Digraph V) : Prop := ∀ a : V, ¬Relation.TransGen G.Adj a a

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] : Decidable G.IsAcyclic :=
  decidable_of_iff (∀ a : V, ¬Relation.TransGen G.Adj a a) Iff.rfl

theorem transGen_adj_iff_exists_walk :
    Relation.TransGen G.Adj a b ↔ ∃ p : G.Walk a b, 0 < p.length := by
  constructor
  · intro h
    induction h with
    | single h => exact ⟨Walk.cons h Walk.nil, by simp⟩
    | tail _ hbc ih =>
      obtain ⟨p, _⟩ := ih
      exact ⟨p.append (Walk.cons hbc Walk.nil), by simp⟩
  · rintro ⟨p, hp⟩
    cases p with
    | nil => simp at hp
    | cons h q =>
      exact Relation.TransGen.head' h (reachable_iff_reflTransGen.mp ⟨q⟩)

/-- Acyclicity stated on walks: every closed walk is trivial. -/
theorem isAcyclic_iff_forall_closed_walk :
    G.IsAcyclic ↔ ∀ ⦃a : V⦄ (p : G.Walk a a), p.length = 0 := by
  constructor
  · intro h a p
    rcases Nat.eq_zero_or_pos p.length with h0 | hpos
    · exact h0
    · exact absurd (transGen_adj_iff_exists_walk.mpr ⟨p, hpos⟩) (h a)
  · intro h a ha
    obtain ⟨p, hp⟩ := transGen_adj_iff_exists_walk.mp ha
    simp [h p] at hp

theorem IsAcyclic.reachable_antisymm (h : G.IsAcyclic) (hab : G.Reachable a b)
    (hba : G.Reachable b a) : a = b := by
  by_contra hne
  rw [reachable_iff_reflTransGen] at hab hba
  have h1 : Relation.TransGen G.Adj a b :=
    (Relation.reflTransGen_iff_eq_or_transGen.mp hab).resolve_left fun h' => hne h'.symm
  exact h a (h1.trans_left hba)

/-- On an acyclic digraph, reachability is a partial order. -/
theorem IsAcyclic.isPartialOrder (h : G.IsAcyclic) : IsPartialOrder V G.Reachable where
  refl := Reachable.refl
  trans _ _ _ := Reachable.trans
  antisymm _ _ hab hba := h.reachable_antisymm hab hba

/-- Szpilrajn glue: reachability of an acyclic digraph extends to a linear order. -/
theorem IsAcyclic.exists_linear_extension (h : G.IsAcyclic) :
    ∃ s : V → V → Prop, IsLinearOrder V s ∧ ∀ ⦃a b⦄, G.Reachable a b → s a b := by
  have := h.isPartialOrder
  obtain ⟨s, hs, hsub⟩ := extend_partialOrder G.Reachable
  exact ⟨s, hs, fun a b hab => hsub a b hab⟩

/-- A finite acyclic digraph has a topological rank: an injective enumeration of the
vertices under which every edge increases rank. -/
theorem IsAcyclic.exists_rank [Fintype V] (h : G.IsAcyclic) :
    ∃ f : V → Fin (Fintype.card V), Function.Injective f ∧
      ∀ ⦃a b⦄, G.Adj a b → f a < f b := by
  classical
  obtain ⟨s, hs, hsub⟩ := h.exists_linear_extension
  -- Package the strict form of `s` as a `LinearOrder` and enumerate it monotonically.
  let t : V → V → Prop := fun a b => s a b ∧ a ≠ b
  have htrans : ∀ a b c : V, t a b → t b c → t a c := by
    rintro a b c ⟨hab, hne₁⟩ ⟨hbc, hne₂⟩
    refine ⟨hs.trans a b c hab hbc, fun hac => hne₂ ?_⟩
    subst hac
    exact hs.antisymm b a hbc hab
  have hirr : ∀ a : V, ¬t a a := fun a ha => ha.2 rfl
  have : Std.Trichotomous t := ⟨fun a b hnab hnba => by
    by_contra hne
    rcases hs.total a b with hab | hba
    · exact hnab ⟨hab, hne⟩
    · exact hnba ⟨hba, Ne.symm hne⟩⟩
  have : IsTrans V t := ⟨htrans⟩
  have : Std.Irrefl t := ⟨hirr⟩
  have : IsStrictTotalOrder V t := {}
  let _ : LinearOrder V := linearOrderOfSTO t
  let e := monoEquivOfFin V rfl
  refine ⟨e.symm, e.symm.injective, fun a b hadj => ?_⟩
  have hne : a ≠ b := fun h' => h b (Relation.TransGen.single (h' ▸ hadj))
  have hlt : a < b := ⟨hsub hadj.reachable, hne⟩
  exact e.symm.strictMono hlt

/-- A finite acyclic digraph has a topological sort: a duplicate-free enumeration of all
vertices listing every edge's source before its target. -/
theorem IsAcyclic.exists_topologicalSort [Fintype V] (h : G.IsAcyclic) :
    ∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧
      ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), G.Adj l[i] l[j] → i < j := by
  obtain ⟨f, hinj, hf⟩ := h.exists_rank
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp⟩
  let e := Equiv.ofBijective f hbij
  refine ⟨(List.finRange (Fintype.card V)).map e.symm, ?_, ?_, ?_⟩
  · exact (List.nodup_finRange _).map e.symm.injective
  · intro v
    exact List.mem_map.mpr ⟨e v, List.mem_finRange _, e.symm_apply_apply v⟩
  · intro i j hi hj hadj
    simp only [List.length_map, List.length_finRange] at hi hj
    simp only [List.getElem_map, List.getElem_finRange] at hadj
    have := hf hadj
    rwa [show ∀ x, f (e.symm x) = x from fun x => e.apply_symm_apply x,
      show ∀ x, f (e.symm x) = x from fun x => e.apply_symm_apply x, Fin.mk_lt_mk] at this

end Digraph

end -- pkc-blanket-expose
end -- pkc-blanket
