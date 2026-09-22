module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Data.Fintype.Card

/-!
# Acyclic quivers and finiteness of paths

A quiver is acyclic when every closed path is trivial. Along a path of an acyclic quiver the
vertices are pairwise distinct (`Quiver.IsAcyclic.nodup_cons_toList`) — a repeated vertex
would bound a nontrivial closed subpath — so on a finite vertex type path lengths are bounded
by the number of vertices (`Quiver.IsAcyclic.length_lt_card`), and with finitely many arrows
between any two vertices the paths between any two vertices form a finite type
(`Quiver.IsAcyclic.finite_path`). Finiteness is what makes a sum over `Path a b` — the shape
of path-indexed aggregations over a dependency graph — well formed.

The injection into arrow lists (`Quiver.Path.arrows`) is independent of acyclicity: unlike
`Quiver.Path.toList`, which is injective only when arrows are subsingletons, the arrow list
determines the path for any quiver.

Upstream target: `Mathlib/Combinatorics/Quiver/Path.lean` (or an `Acyclic` satellite).
-/

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace Quiver

universe v u

variable {V : Type u} [Quiver.{v} V]

/-- A quiver is acyclic when every closed path is trivial. -/
def IsAcyclic (V : Type u) [Quiver.{v} V] : Prop :=
  ∀ ⦃a : V⦄ (p : Path a a), p.length = 0

namespace Path

variable {a b c v : V}

@[simp]
theorem length_toList (p : Path a b) : p.toList.length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih]

/-- Splitting a path at any of its vertices: the vertices of `p : Path a b` are `b` and the
entries of `p.toList`, and each is the junction of a decomposition of `p`. -/
theorem eq_comp_of_mem_cons_toList (p : Path a b) (hv : v ∈ b :: p.toList) :
    ∃ (q : Path a v) (r : Path v b), p = q.comp r := by
  induction p with
  | nil =>
    obtain rfl : v = a := by simpa using hv
    exact ⟨.nil, .nil, rfl⟩
  | @cons c b' p e ih =>
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact ⟨p.cons e, .nil, rfl⟩
    · obtain ⟨q, r, rfl⟩ := ih hv'
      exact ⟨q, r.cons e, by rw [comp_cons]⟩

/-- The arrows along a path, most recent first, each packaged with its endpoints. Unlike
`Quiver.Path.toList` this determines the path even in the presence of parallel arrows
(`Quiver.Path.arrows_injective`). -/
def arrows : ∀ {b : V}, Path a b → List (Σ x y : V, x ⟶ y)
  | _, .nil => []
  | _, .cons p e => ⟨_, _, e⟩ :: p.arrows

@[simp] theorem arrows_nil : (Path.nil : Path a a).arrows = [] := rfl

@[simp] theorem arrows_cons (p : Path a b) (e : b ⟶ c) :
    (p.cons e).arrows = ⟨b, c, e⟩ :: p.arrows := rfl

@[simp]
theorem length_arrows (p : Path a b) : p.arrows.length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih]

theorem arrows_injective : ∀ {b : V} (p q : Path a b), p.arrows = q.arrows → p = q
  | _, .nil, .nil, _ => rfl
  | _, .nil, .cons q f, h => by simp at h
  | _, .cons p e, .nil, h => by simp at h
  | _, .cons p e, .cons q f, h => by
    simp only [arrows_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨rfl, h1⟩ := Sigma.mk.inj_iff.mp h1
    obtain ⟨-, h1⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h1)
    obtain rfl := eq_of_heq h1
    rw [arrows_injective p q h2]

theorem arrows_inj {p q : Path a b} : p.arrows = q.arrows ↔ p = q :=
  ⟨arrows_injective p q, by rintro rfl; rfl⟩

end Path

namespace IsAcyclic

open Path

variable {a b : V}

/-- In an acyclic quiver the vertices along a path are pairwise distinct. -/
theorem nodup_cons_toList (h : IsAcyclic V) (p : Path a b) :
    (b :: p.toList).Nodup := by
  induction p with
  | nil => simp
  | @cons c b' p e ih =>
    rw [Path.toList, List.nodup_cons]
    refine ⟨fun hb => ?_, ih⟩
    obtain ⟨q, r, rfl⟩ := p.eq_comp_of_mem_cons_toList hb
    have := h (r.cons e)
    simp at this

/-- In a finite acyclic quiver, path lengths are bounded by the number of vertices. -/
theorem length_lt_card (h : IsAcyclic V) [Fintype V] (p : Path a b) :
    p.length < Fintype.card V := by
  have h1 : p.length + 1 ≤ Fintype.card V := by
    simpa [length_toList] using (h.nodup_cons_toList p).length_le_card
  omega

/-- In a finite acyclic quiver, the paths between any two vertices form a finite type: the
arrow list injects a path into the duplicate-free-bounded lists over the finitely many
arrows. -/
theorem finite_path (h : IsAcyclic V) [Finite V] [∀ x y : V, Finite (x ⟶ y)] (a b : V) :
    Finite (Path a b) := by
  cases nonempty_fintype V
  have key : ∀ p : Path a b,
      p.arrows ∈ {l : List (Σ x y : V, x ⟶ y) | l.length ≤ Fintype.card V} := fun p => by
    simp only [Set.mem_ofPred_eq, length_arrows]
    exact (h.length_lt_card p).le
  have hfin : {l : List (Σ x y : V, x ⟶ y) | l.length ≤ Fintype.card V}.Finite :=
    List.finite_length_le _ _
  have := hfin.to_subtype
  exact Finite.of_injective
    (fun p : Path a b =>
      (⟨p.arrows, key p⟩ : {l : List (Σ x y : V, x ⟶ y) | l.length ≤ Fintype.card V}))
    fun p q hpq => arrows_injective p q (congrArg Subtype.val hpq)

end IsAcyclic

end Quiver

end -- pkc-blanket-expose
end -- pkc-blanket
