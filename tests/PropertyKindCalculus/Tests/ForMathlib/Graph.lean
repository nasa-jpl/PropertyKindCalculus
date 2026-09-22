/-
# Validation probes — ForMathlib digraph/quiver theory

Three dangers this probe file closes for the staging area:

  * **vacuity** — the classical theorems (topological sort, weak Menger, path finiteness) are
    each applied to a *concrete* witness, so a vacuously-quantified statement could not
    compile here;
  * **dead executability** — the decidability instances (reachability, acyclicity,
    components, condensation) are driven by `decide`/`#guard` on a concrete digraph whose
    component structure is known, so an instance that stopped reducing would fail the build;
  * **silent axioms** — the load-bearing theorems' axiom profiles are pinned with
    `#guard_msgs`, so a proof relocated behind `sorry` is caught.
-/

module

public import ForMathlib
meta import ForMathlib

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Tests.ForMathlib

open Digraph

/-! ### A concrete digraph with a nontrivial component structure

A chain `0 → 1 → 2 → 3` with the back edge `2 → 1`, so `{1, 2}` is a genuine strongly
connected component, plus an isolated vertex `4`. Components: `{0}, {1,2}, {3}, {4}`. -/

/-- The probe digraph (an `abbrev`, so the `Digraph.mk'` decidability instance fires). -/
abbrev G : Digraph (Fin 5) :=
  Digraph.mk' fun a b =>
    decide ((a, b) ∈ [((0 : Fin 5), (1 : Fin 5)), (1, 2), (2, 1), (2, 3)])

-- Reachability follows edges, transitively, one way only; the isolated vertex reaches
-- nothing but itself. Kernel-checked through the executable forward closure.
example : G.Reachable 0 3 := by decide
example : ¬G.Reachable 3 0 := by decide
example : ¬G.Reachable 0 4 := by decide
example : G.Reachable 4 4 := by decide

-- The components are computed by the instances: `1` and `2` are mutually reachable, hence
-- identified; `0` is not identified with `1`; and there are exactly four components.
example : G.strongComponentMk 1 = G.strongComponentMk 2 := by decide
example : G.strongComponentMk 0 ≠ G.strongComponentMk 1 := by decide
#guard Fintype.card G.StrongComponent == 4

-- The condensation of `G` is acyclic *by computation* — the general theorem
-- (`Digraph.isAcyclic_condensation`) says this for every digraph; the probe checks the
-- decidable instances agree on the concrete one.
#guard decide G.condensation.IsAcyclic

-- `G` itself is not acyclic (the `1 ↔ 2` cycle), so acyclicity is discriminating.
example : ¬G.IsAcyclic := fun h =>
  h 1 (Relation.TransGen.head (show G.Adj 1 2 by decide)
    (.single (show G.Adj 2 1 by decide)))

/-! ### Topological sort on a concrete DAG -/

/-- A diamond with a tail: `0 → 1 → 2`, `0 → 2`, `2 → 3`. -/
abbrev D : Digraph (Fin 4) :=
  Digraph.mk' fun a b =>
    decide ((a, b) ∈ [((0 : Fin 4), (1 : Fin 4)), (1, 2), (0, 2), (2, 3)])

theorem D_isAcyclic : D.IsAcyclic := by decide

-- The Szpilrajn-glued existence theorems, applied: their conclusions are inhabited on a real
-- DAG, not vacuous.
example : ∃ f : Fin 4 → Fin (Fintype.card (Fin 4)), Function.Injective f ∧
    ∀ ⦃a b⦄, D.Adj a b → f a < f b :=
  D_isAcyclic.exists_rank

example : ∃ l : List (Fin 4), l.Nodup ∧ (∀ v, v ∈ l) ∧
    ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), D.Adj l[i] l[j] → i < j :=
  D_isAcyclic.exists_topologicalSort

/-! ### The weak Menger inequality on a concrete separator -/

/-- The walk `0 → 1 → 2 → 3` through `G`. -/
def w03 : G.Walk 0 3 :=
  .cons (show G.Adj 0 1 by decide) (.cons (show G.Adj 1 2 by decide)
    (.cons (show G.Adj 2 3 by decide) .nil))

-- A one-walk disjoint family against the source-side separator: the inequality `1 ≤ 1`
-- arrives as an instance of the theorem, with every hypothesis discharged concretely.
example : Nat.card (Fin 1) ≤ ({0} : Set (Fin 5)).ncard :=
  (isSeparator_left G {0} {3}).card_le_of_disjoint (Set.finite_singleton _)
    (w := fun _ => w03) (fun _ => rfl) (fun _ => rfl)
    (fun i j hne => absurd (Subsingleton.elim i j) hne)

/-! ### Path finiteness on a concrete acyclic quiver -/

/-- A three-vertex quiver whose arrows strictly increase the vertex index. -/
def UpV := Fin 3

instance : Quiver UpV := ⟨fun i j => PLift (Fin.val i < Fin.val j)⟩

instance : Finite UpV := inferInstanceAs (Finite (Fin 3))

instance (x y : UpV) : Finite (x ⟶ y) :=
  Finite.of_injective (fun _ => ()) fun a b _ => by
    cases a; cases b; rfl

theorem UpV.le_of_path {i j : UpV} (p : Quiver.Path i j) (hp : 0 < p.length) :
    Fin.val i < Fin.val j := by
  induction p with
  | nil => simp at hp
  | cons q e ih =>
    rcases Nat.eq_zero_or_pos q.length with h0 | hq
    · obtain rfl := Quiver.Path.eq_of_length_zero q h0
      exact e.down
    · exact (ih hq).trans e.down

theorem UpV.isAcyclic : Quiver.IsAcyclic UpV := fun _ p => by
  rcases Nat.eq_zero_or_pos p.length with h0 | hp
  · exact h0
  · exact absurd (le_of_path p hp) (lt_irrefl _)

/-- The bottom vertex of the probe quiver. -/
def UpV.v0 : UpV := (0 : Fin 3)

/-- The top vertex of the probe quiver. -/
def UpV.v2 : UpV := (2 : Fin 3)

-- Path finiteness, applied: the paths between two concrete vertices of a concrete acyclic
-- quiver form a finite type.
example : Finite (Quiver.Path UpV.v0 UpV.v2) :=
  UpV.isAcyclic.finite_path _ _

/-! ### Axiom profiles -/

/-- info: 'Relation.mem_reachSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Relation.mem_reachSet

/-- info: 'Digraph.IsAcyclic.exists_topologicalSort' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Digraph.IsAcyclic.exists_topologicalSort

/-- info: 'Digraph.IsSeparator.card_le_of_disjoint' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Digraph.IsSeparator.card_le_of_disjoint

/-- info: 'Digraph.isAcyclic_condensation' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in #print axioms Digraph.isAcyclic_condensation

/-- info: 'Quiver.IsAcyclic.finite_path' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in #print axioms Quiver.IsAcyclic.finite_path

end PropertyKindCalculus.Tests.ForMathlib

end -- pkc-blanket-expose
end -- pkc-blanket
