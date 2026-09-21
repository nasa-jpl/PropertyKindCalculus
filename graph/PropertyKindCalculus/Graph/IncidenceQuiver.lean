import PropertyKindCalculus.Graph.Flow
import ForMathlib.Combinatorics.Quiver.Acyclic
import Mathlib.Basic.Finite.Sum

/-!
# The incidence quiver — occurrence multiplicity as arrows, and finite budgets

The value-flow digraph forgets *which operand position* carries an influence: `kx / kx`
is one edge there. The incidence quiver keeps it. Vertices are the graph's nodes and its
occurrences (each by index, so the vertex type is finite whatever the node type);
arrows run from a node into each occurrence position it fills — one arrow per position,
so a repeated operand is two arrows — and from an occurrence to its result. Paths
therefore enumerate derivation chains at full incidence resolution: exactly the index
set of a sum over paths, an uncertainty budget's shape.

What is proved: every quiver path denotes reachability in the value-flow digraph
(`Provenance.IncidenceVert.path_transGen`), so on an acyclic graph the incidence quiver
is acyclic (`Provenance.Acyclic.isAcyclic_incidenceQuiver`) and the paths between any
two vertices form a **finite type** (`Provenance.Acyclic.finite_incidencePath`) — the
well-formedness of a budget as a finite sum over paths, discharged by the same
executable `acyclic` check a probe evaluates.
-/

namespace PropertyKindCalculus

namespace Provenance

variable {ν κ : Type}

/-- A vertex of the incidence quiver: a node of the graph (by index in `nodeList`) or an
occurrence (by position). Index-typed, so the vertex type is finite whatever `ν` is. -/
inductive IncidenceVert [BEq ν] (g : Provenance ν κ) : Type where
  | node (i : Fin g.nodeList.length)
  | occ (e : Fin g.occurrences.length)
deriving DecidableEq

namespace IncidenceVert

variable [BEq ν] {g : Provenance ν κ}

private def toSum : IncidenceVert g → Fin g.nodeList.length ⊕ Fin g.occurrences.length
  | .node i => .inl i
  | .occ e => .inr e

instance : Finite (IncidenceVert g) :=
  Finite.of_injective toSum (by
    rintro (i | e) (j | f) h <;> simp [toSum] at h <;> simp [h])

/-- The arrows: a node enters an occurrence at each operand position it fills — one
arrow per position, so occurrence multiplicity is definitional — and an occurrence
exits to its result. -/
instance : Quiver (IncidenceVert g) where
  Hom v w :=
    match v, w with
    | .node i, .occ e =>
      { j : Fin (g.occurrences.get e).operands.length //
          ((g.occurrences.get e).operands.get j).1 = g.nodeList.get i }
    | .occ e, .node i => PLift ((g.occurrences.get e).result = g.nodeList.get i)
    | _, _ => Empty

instance (v w : IncidenceVert g) : Finite (v ⟶ w) := by
  cases v with
  | node i =>
    cases w with
    | node j => exact inferInstanceAs (Finite Empty)
    | occ e => exact inferInstanceAs (Finite { j // _ })
  | occ e =>
    cases w with
    | node i =>
      exact Finite.of_injective (fun _ => ()) fun a b _ => by cases a; cases b; rfl
    | occ f => exact inferInstanceAs (Finite Empty)

/-- What a vertex stands for in the value flow: a node vertex its node, an occurrence
vertex its result. -/
def den : IncidenceVert g → ν
  | .node i => g.nodeList.get i
  | .occ e => (g.occurrences.get e).result

/-- Every arrow denotes a hop or an equality in the value flow: entering an occurrence
is one `stepRel` hop to its result, leaving it to its result node is denotation
equality. -/
theorem den_hop {v w : IncidenceVert g} (f : v ⟶ w) :
    stepRel g.occurrences (den v) (den w) ∨ den v = den w := by
  cases v with
  | node i =>
    cases w with
    | node j => exact f.elim
    | occ e =>
      exact Or.inl ⟨g.occurrences.get e, (g.occurrences.get_mem e), rfl,
        (g.occurrences.get e).operands.get f.1, ((g.occurrences.get e).operands.get_mem f.1),
        f.2⟩
  | occ e =>
    cases w with
    | node i => exact Or.inr f.down
    | occ f' => exact f.elim

/-- The hop an entering arrow denotes: a node's value flows to the occurrence's
result. -/
theorem stepRel_of_arrow {i : Fin g.nodeList.length} {e : Fin g.occurrences.length}
    (f : (IncidenceVert.node i : IncidenceVert g) ⟶ .occ e) :
    stepRel g.occurrences (den (IncidenceVert.node i : IncidenceVert g))
      (den (IncidenceVert.occ e : IncidenceVert g)) :=
  ⟨g.occurrences.get e, g.occurrences.get_mem e, rfl,
    (g.occurrences.get e).operands.get f.1,
    ((g.occurrences.get e).operands).get_mem f.1, f.2⟩

/-- A positive path denotes transitive reachability in the value flow — except for the
single occurrence-to-result arrow, which denotes an equality and is recognizable by its
endpoint shapes. The disjunction is what makes closed paths contradictory: a closed
positive path either yields a value-flow cycle or asserts one vertex is both an
occurrence and a node. -/
theorem path_transGen : ∀ {v w : IncidenceVert g} (p : Quiver.Path v w),
    0 < p.length →
      Relation.TransGen (stepRel g.occurrences) (den v) (den w) ∨
        (den v = den w ∧ (∃ e, v = .occ e) ∧ ∃ i, w = .node i)
  | _, _, .nil, h => by simp at h
  | v, w, @Quiver.Path.cons _ _ _ b _ p f, _ => by
    rcases Nat.eq_zero_or_pos p.length with h0 | hpos
    · -- The single-arrow case: `p` is trivial, so the arrow's endpoint shapes decide.
      obtain rfl := Quiver.Path.eq_of_length_zero p h0
      cases v with
      | node i =>
        cases w with
        | node j => exact (f : Empty).elim
        | occ e => exact Or.inl (.single (stepRel_of_arrow f))
      | occ e =>
        cases w with
        | node i => exact Or.inr ⟨f.down, ⟨e, rfl⟩, ⟨i, rfl⟩⟩
        | occ e' => exact (f : Empty).elim
    · rcases path_transGen p hpos with hTG | ⟨heq, -, i, rfl⟩
      · -- Extend the accumulated reachability by the last arrow, by shape.
        cases b with
        | node i =>
          cases w with
          | node j => exact (f : Empty).elim
          | occ e => exact Or.inl (hTG.tail (stepRel_of_arrow f))
        | occ e =>
          cases w with
          | node i =>
            have hden : den (IncidenceVert.occ e : IncidenceVert g) =
                den (IncidenceVert.node i : IncidenceVert g) := f.down
            exact Or.inl (hden ▸ hTG)
          | occ e' => exact (f : Empty).elim
      · -- `p` ended on a node vertex, so the arrow `f` leaves a node: it is the
        -- entering arrow of an occurrence, a genuine hop.
        cases w with
        | node j => exact (f : Empty).elim
        | occ e =>
          exact Or.inl (heq ▸ Relation.TransGen.single (stepRel_of_arrow f))

end IncidenceVert

/-- On an acyclic graph the incidence quiver is acyclic: a nontrivial closed path would
denote a value-flow cycle, or assert one vertex is both an occurrence and a node. -/
theorem Acyclic.isAcyclic_incidenceQuiver [BEq ν] [LawfulBEq ν] {g : Provenance ν κ}
    (h : g.Acyclic) : Quiver.IsAcyclic (IncidenceVert g) := by
  intro v p
  by_contra hne
  rcases IncidenceVert.path_transGen p (Nat.pos_of_ne_zero hne) with hTG | ⟨-, ⟨e, rfl⟩, i, hv⟩
  · exact (acyclic_iff_isAcyclic.mp h) _ hTG
  · cases hv

/-- **Budgets are finite sums**: on an acyclic graph the incidence-quiver paths between
any two vertices form a finite type, so a sum indexed by the derivation chains from a
source to an output — an uncertainty budget at full incidence resolution — is well
formed. Discharged by the same executable `acyclic` check a probe evaluates. -/
theorem Acyclic.finite_incidencePath [BEq ν] [LawfulBEq ν] {g : Provenance ν κ}
    (h : g.Acyclic) (v w : IncidenceVert g) : Finite (Quiver.Path v w) :=
  h.isAcyclic_incidenceQuiver.finite_path v w

end Provenance

end PropertyKindCalculus
