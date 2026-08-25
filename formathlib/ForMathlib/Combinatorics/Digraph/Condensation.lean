import ForMathlib.Combinatorics.Digraph.Acyclic

/-!
# Strongly connected components and the condensation of a digraph

Mutual reachability is an equivalence on the vertices of a digraph
(`Digraph.sccSetoid`); its classes are the strongly connected components
(`Digraph.StrongComponent`). The condensation is the digraph induced on the components by
the edges crossing between distinct components (`Digraph.condensation`). Reachability
descends to the condensation exactly (`Digraph.condensation_reachable`), the condensation is
acyclic (`Digraph.isAcyclic_condensation`) — a cycle of components would merge them — and
therefore reachability between components is a partial order
(`Digraph.isPartialOrder_condensation_reachable`): the condensation of a digraph is its
reachability hierarchy.

On a finite vertex type with decidable adjacency everything here is decidable — components,
condensation adjacency, and condensation reachability — so component questions on concrete
digraphs close by `decide`.

Upstream target: `Mathlib/Combinatorics/Digraph/Condensation.lean`.
-/

namespace Digraph

variable {V : Type*} (G : Digraph V) {a b : V}

/-- Mutual reachability, the equivalence whose classes are the strongly connected
components. -/
def sccSetoid : Setoid V where
  r a b := G.Reachable a b ∧ G.Reachable b a
  iseqv :=
    ⟨fun a => ⟨.refl a, .refl a⟩, fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩,
      fun ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ => ⟨h₁.trans h₃, h₄.trans h₂⟩⟩

/-- The strongly connected components of a digraph: vertices up to mutual reachability. -/
def StrongComponent := Quotient G.sccSetoid

/-- The strongly connected component of a vertex. -/
def strongComponentMk (a : V) : G.StrongComponent := Quotient.mk G.sccSetoid a

theorem strongComponentMk_eq_iff :
    G.strongComponentMk a = G.strongComponentMk b ↔ G.Reachable a b ∧ G.Reachable b a :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

/-- The condensation: the digraph induced on the strongly connected components by the edges
crossing between distinct components. -/
def condensation : Digraph G.StrongComponent where
  Adj c d := c ≠ d ∧ ∃ a b : V,
    G.strongComponentMk a = c ∧ G.strongComponentMk b = d ∧ G.Adj a b

theorem condensation_adj {c d : G.StrongComponent} :
    G.condensation.Adj c d ↔ c ≠ d ∧ ∃ a b : V,
      G.strongComponentMk a = c ∧ G.strongComponentMk b = d ∧ G.Adj a b :=
  Iff.rfl

/-- Reachability descends to the condensation exactly. -/
theorem condensation_reachable :
    G.condensation.Reachable (G.strongComponentMk a) (G.strongComponentMk b) ↔
      G.Reachable a b := by
  constructor
  · intro h
    rw [reachable_iff_reflTransGen] at h
    suffices key : ∀ c d, Relation.ReflTransGen G.condensation.Adj c d →
        ∀ x y : V, G.strongComponentMk x = c → G.strongComponentMk y = d →
          G.Reachable x y by
      exact key _ _ h a b rfl rfl
    intro c d h
    induction h with
    | refl =>
      intro x y hx hy
      exact ((G.strongComponentMk_eq_iff).mp (hx.trans hy.symm)).1
    | tail _ hcd ih =>
      intro x y hx hy
      obtain ⟨-, x', y', hx', hy', hadj⟩ := hcd
      exact ((ih x x' hx hx').trans hadj.reachable).trans
        ((G.strongComponentMk_eq_iff).mp (hy'.trans hy.symm)).1
  · intro h
    rw [reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact .refl _
    | @tail x y _ hxy ih =>
      rcases eq_or_ne (G.strongComponentMk x) (G.strongComponentMk y) with heq | hne
      · exact heq ▸ ih
      · exact ih.trans (Adj.reachable ⟨hne, x, y, rfl, rfl, hxy⟩)

/-- The condensation is acyclic: a cycle of components would merge its components. -/
theorem isAcyclic_condensation : G.condensation.IsAcyclic := by
  intro c hc
  obtain ⟨d, hcd, hdc⟩ := Relation.TransGen.head'_iff.mp hc
  obtain ⟨hne, x, y, rfl, rfl, hxy⟩ := hcd
  have hyx : G.Reachable y x :=
    (G.condensation_reachable).mp (reachable_iff_reflTransGen.mpr hdc)
  exact hne ((G.strongComponentMk_eq_iff).mpr ⟨hxy.reachable, hyx⟩)

/-- The reachability hierarchy: reachability between strongly connected components is a
partial order. -/
theorem isPartialOrder_condensation_reachable :
    IsPartialOrder G.StrongComponent G.condensation.Reachable :=
  G.isAcyclic_condensation.isPartialOrder

section Decidable

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

instance : DecidableRel G.sccSetoid.r := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

instance : DecidableEq G.StrongComponent :=
  inferInstanceAs (DecidableEq (Quotient G.sccSetoid))

instance : Fintype G.StrongComponent :=
  inferInstanceAs (Fintype (Quotient G.sccSetoid))

instance : DecidableRel G.condensation.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

end Decidable

end Digraph
