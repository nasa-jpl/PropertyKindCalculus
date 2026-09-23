module

public import Mathlib.Combinatorics.Digraph.Basic

/-!
# Walks in a digraph

A walk in a digraph is a directed chain of adjacent vertices; this module transfers the core
`SimpleGraph.Walk` vocabulary to `Digraph`, where edges are one-way: `Walk`, `length`,
`support`, `append`, `IsPath`, the `takeUntil`/`dropUntil` decomposition at a support vertex,
and `bypass`, which shortcuts a walk between repeated vertices to produce a path with the
same endpoints. Nothing here uses symmetry, so the statements are the directed halves of
their `SimpleGraph` counterparts (in particular there is no `reverse`).

Upstream target: `Mathlib/Combinatorics/Digraph/Walk.lean`, seeding the walk layer of the
`Digraph` stub from the mature `SimpleGraph` development.
-/

@[expose] public section Blanket

namespace Digraph

universe u

variable {V : Type u} {G : Digraph V} {a b c d u : V}

/-- A walk from `a` to `b` in a digraph `G` is a chain of vertices, each adjacent to the
next in the direction of the walk. -/
inductive Walk (G : Digraph V) : V → V → Type u
  | nil {a : V} : Walk G a a
  | cons {a b c : V} (h : G.Adj a b) (p : Walk G b c) : Walk G a c
  deriving DecidableEq

namespace Walk

/-- The number of edges along a walk. -/
def length : ∀ {a b : V}, G.Walk a b → ℕ
  | _, _, nil => 0
  | _, _, cons _ p => p.length + 1

@[simp] theorem length_nil : (nil : G.Walk a a).length = 0 := rfl

@[simp] theorem length_cons (h : G.Adj a b) (p : G.Walk b c) :
    (cons h p).length = p.length + 1 := rfl

/-- The vertices along a walk, in order, starting with `a` and ending with `b`. -/
def support : ∀ {a b : V}, G.Walk a b → List V
  | a, _, nil => [a]
  | a, _, cons _ p => a :: p.support

@[simp] theorem support_nil : (nil : G.Walk a a).support = [a] := rfl

@[simp] theorem support_cons (h : G.Adj a b) (p : G.Walk b c) :
    (cons h p).support = a :: p.support := rfl

theorem support_ne_nil (p : G.Walk a b) : p.support ≠ [] := by cases p <;> simp

@[simp] theorem start_mem_support (p : G.Walk a b) : a ∈ p.support := by cases p <;> simp

@[simp] theorem end_mem_support (p : G.Walk a b) : b ∈ p.support := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp [ih]

theorem mem_support_nil_iff : u ∈ (nil : G.Walk a a).support ↔ u = a := by simp

theorem support_eq_cons (p : G.Walk a b) : p.support = a :: p.support.tail := by
  cases p <;> simp

@[simp] theorem length_support (p : G.Walk a b) : p.support.length = p.length + 1 := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp [ih]

/-- Concatenation of walks sharing an endpoint. -/
def append : ∀ {a b c : V}, G.Walk a b → G.Walk b c → G.Walk a c
  | _, _, _, nil, q => q
  | _, _, _, cons h p, q => cons h (p.append q)

@[simp] theorem nil_append (q : G.Walk a b) : (nil : G.Walk a a).append q = q := rfl

@[simp] theorem cons_append (h : G.Adj a b) (p : G.Walk b c) (q : G.Walk c d) :
    (cons h p).append q = cons h (p.append q) := rfl

@[simp] theorem append_nil (p : G.Walk a b) : p.append nil = p := by
  induction p with
  | nil => rfl
  | cons h p ih => rw [cons_append, ih]

@[simp] theorem length_append (p : G.Walk a b) (q : G.Walk b c) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp [ih]; omega

theorem support_append (p : G.Walk a b) (q : G.Walk b c) :
    (p.append q).support = p.support ++ q.support.tail := by
  induction p with
  | nil => simpa using support_eq_cons q
  | cons _ _ ih => simp [ih]

theorem tail_support_append (p : G.Walk a b) (q : G.Walk b c) :
    (p.append q).support.tail = p.support.tail ++ q.support.tail := by
  rw [support_append, support_eq_cons p, List.cons_append, List.tail_cons]
  rfl

theorem mem_support_append_iff (p : G.Walk a b) (q : G.Walk b c) :
    u ∈ (p.append q).support ↔ u ∈ p.support ∨ u ∈ q.support := by
  rw [support_append, List.mem_append]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (List.mem_of_mem_tail h)
  · rintro (h | h)
    · exact Or.inl h
    · rw [support_eq_cons q] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (end_mem_support p)
      · exact Or.inr h

/-! ### Paths -/

/-- A path is a walk with no repeated vertices. -/
def IsPath (p : G.Walk a b) : Prop := p.support.Nodup

theorem isPath_def (p : G.Walk a b) : p.IsPath ↔ p.support.Nodup := Iff.rfl

@[simp] theorem isPath_nil : (nil : G.Walk a a).IsPath := by simp [IsPath]

@[simp] theorem cons_isPath_iff (h : G.Adj a b) (p : G.Walk b c) :
    (cons h p).IsPath ↔ p.IsPath ∧ a ∉ p.support := by
  rw [IsPath, IsPath, support_cons, List.nodup_cons, and_comm]

theorem IsPath.length_le_card [Fintype V] {p : G.Walk a b} (hp : p.IsPath) :
    p.length + 1 ≤ Fintype.card V := by
  rw [← length_support]
  exact List.Nodup.length_le_card hp

theorem IsPath.of_append_left {p : G.Walk a b} {q : G.Walk b c}
    (h : (p.append q).IsPath) : p.IsPath := by
  rw [IsPath, support_append] at h
  exact h.of_append_left

theorem IsPath.of_append_right {p : G.Walk a b} {q : G.Walk b c}
    (h : (p.append q).IsPath) : q.IsPath := by
  rw [IsPath, support_append] at h
  rw [IsPath, support_eq_cons q, List.nodup_cons]
  exact ⟨fun hb => (List.disjoint_of_nodup_append h) (end_mem_support p) hb,
    h.of_append_right⟩

/-! ### Decomposition at a support vertex -/

section WalkDecomp

variable [DecidableEq V]

/-- Given a vertex in the support of a walk, the walk up until (and including) that
vertex. -/
def takeUntil : ∀ {a b : V} (p : G.Walk a b) (u : V), u ∈ p.support → G.Walk a u
  | _, _, nil, _, h => by obtain rfl := mem_support_nil_iff.mp h; exact nil
  | a, _, cons r p, u, h =>
    if hx : a = u then by subst hx; exact nil
    else cons r (p.takeUntil u ((List.mem_cons.mp h).resolve_left fun h' => hx h'.symm))

/-- Given a vertex in the support of a walk, the walk from (and including) that vertex to
the end. -/
def dropUntil : ∀ {a b : V} (p : G.Walk a b) (u : V), u ∈ p.support → G.Walk u b
  | _, _, nil, _, h => by obtain rfl := mem_support_nil_iff.mp h; exact nil
  | a, _, cons r p, u, h =>
    if hx : a = u then by subst hx; exact cons r p
    else p.dropUntil u ((List.mem_cons.mp h).resolve_left fun h' => hx h'.symm)

/-- `takeUntil` and `dropUntil` split a walk at a support vertex. -/
@[simp] theorem take_spec (p : G.Walk a b) (h : u ∈ p.support) :
    (p.takeUntil u h).append (p.dropUntil u h) = p := by
  induction p with
  | nil =>
    obtain rfl := mem_support_nil_iff.mp h
    rfl
  | cons r p ih =>
    simp only [takeUntil, dropUntil]
    split_ifs with h'
    · subst h'
      rfl
    · rw [cons_append, ih]

theorem support_takeUntil_subset (p : G.Walk a b) (h : u ∈ p.support) :
    (p.takeUntil u h).support ⊆ p.support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inl hx

theorem support_dropUntil_subset (p : G.Walk a b) (h : u ∈ p.support) :
    (p.dropUntil u h).support ⊆ p.support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inr hx

protected theorem IsPath.takeUntil {p : G.Walk a b} (hp : p.IsPath) (h : u ∈ p.support) :
    (p.takeUntil u h).IsPath :=
  IsPath.of_append_left (q := p.dropUntil u h) (by rwa [take_spec])

protected theorem IsPath.dropUntil {p : G.Walk a b} (hp : p.IsPath) (h : u ∈ p.support) :
    (p.dropUntil u h).IsPath :=
  IsPath.of_append_right (p := p.takeUntil u h) (by rwa [take_spec])

/-- Shortcut a walk between repeated vertices, producing a path with the same endpoints
(`Digraph.Walk.bypass_isPath`) supported on a subset of the walk's support
(`Digraph.Walk.support_bypass_subset`). -/
def bypass : ∀ {a b : V}, G.Walk a b → G.Walk a b
  | _, _, nil => nil
  | a, _, cons ha p =>
    let p' := p.bypass
    if hs : a ∈ p'.support then p'.dropUntil a hs else cons ha p'

theorem bypass_isPath (p : G.Walk a b) : p.bypass.IsPath := by
  induction p with
  | nil => simp [bypass]
  | cons _ p ih =>
    dsimp only [bypass]
    split_ifs with hs
    · exact ih.dropUntil hs
    · rw [cons_isPath_iff]
      exact ⟨ih, hs⟩

theorem support_bypass_subset (p : G.Walk a b) : p.bypass.support ⊆ p.support := by
  induction p with
  | nil => simp [bypass]
  | cons _ p ih =>
    dsimp only [bypass]
    split_ifs with hs
    · exact fun x hx =>
        List.mem_cons_of_mem _ (ih (support_dropUntil_subset _ hs hx))
    · simp only [support_cons]
      exact List.cons_subset_cons _ ih

end WalkDecomp

end Walk

end Digraph

end Blanket
