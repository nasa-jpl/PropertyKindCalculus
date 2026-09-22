module

public import ForMathlib.Combinatorics.Digraph.Walk
public import ForMathlib.Logic.Relation.Decidable

/-!
# Reachability in a digraph

`Digraph.Reachable a b` holds when some walk leads from `a` to `b`. It is a preorder — not an
equivalence, since edges are one-way (compare the symmetric `SimpleGraph.Reachable`) — and it
coincides with `Relation.ReflTransGen` of the adjacency relation
(`Digraph.reachable_iff_reflTransGen`), which carries decidability onto finite digraphs with
decidable adjacency: reachability questions on concrete digraphs close by `decide`.

Upstream target: `Mathlib/Combinatorics/Digraph/Connectivity.lean`.
-/

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace Digraph

variable {V : Type*} {G : Digraph V} {a b c : V}

/-- Two vertices are reachable when a directed walk leads from the first to the second. -/
def Reachable (G : Digraph V) (a b : V) : Prop := Nonempty (G.Walk a b)

protected theorem Reachable.elim {p : Prop} (h : G.Reachable a b)
    (hp : G.Walk a b → p) : p :=
  Nonempty.elim h hp

protected theorem Walk.reachable (p : G.Walk a b) : G.Reachable a b := ⟨p⟩

protected theorem Adj.reachable (h : G.Adj a b) : G.Reachable a b :=
  ⟨Walk.cons h Walk.nil⟩

@[refl] protected theorem Reachable.refl (a : V) : G.Reachable a a := ⟨Walk.nil⟩

protected theorem Reachable.rfl : G.Reachable a a := .refl a

@[trans] protected theorem Reachable.trans (hab : G.Reachable a b) (hbc : G.Reachable b c) :
    G.Reachable a c :=
  hab.elim fun p => hbc.elim fun q => ⟨p.append q⟩

instance : IsPreorder V G.Reachable where
  refl := Reachable.refl
  trans _ _ _ := Reachable.trans

theorem reachable_iff_reflTransGen :
    G.Reachable a b ↔ Relation.ReflTransGen G.Adj a b := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact .refl
    | cons h _ ih => exact ih.head h
  · intro h
    induction h with
    | refl => exact .refl a
    | tail _ hbc ih => exact ih.trans hbc.reachable

/-- Reachability by a walk is reachability by a path: shortcut repeated vertices. -/
theorem Reachable.exists_isPath (h : G.Reachable a b) :
    ∃ p : G.Walk a b, p.IsPath := by
  classical
  obtain ⟨p⟩ := h
  exact ⟨p.bypass, p.bypass_isPath⟩

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] : DecidableRel G.Reachable :=
  fun _ _ => decidable_of_iff _ reachable_iff_reflTransGen.symm

end Digraph

end -- pkc-blanket-expose
end -- pkc-blanket
