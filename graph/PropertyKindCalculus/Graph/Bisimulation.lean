module

public import PropertyKindCalculus.Graph.Flow
public import PropertyKindCalculus.Derivation
public import PropertyKindCalculus.Paradigm.TapeGraph
public import Cslib.Foundations.Semantics.LTS.Bisimulation

/-!
# The kind-transporting weak bisimulation — the provenance hypergraph against the tape graph

The second capstone's relation, in the textbook sense (Sangiorgi 2011, through cslib's
labelled transition systems). Three transition systems share one label alphabet
(`KindLabel`): a visible step is an edge family with the operand position it enters at, and
the silent step τ is the wiring the harvest records as `copy`, a procedure edge, and every
carrier-level interior step.

  * `Provenance.lts` — **the provenance layer**: a hop from an operand of an occurrence to its
    result, labelled by the family and the position;
  * `Match.contracted` — **the contracted tape graph**: one hyperedge per realized
    occurrence, from a component of an operand to a component of the result, with no
    interior;
  * `Match.tapeLts` — **the computational tape graph**: the tape's own edges, labelled through
    the match — an edge into a realized sub-graph is visible at its frontier and silent inside.

Under acceptance of the match (`Match.accepts`) and well-formedness of the hypergraph:

  * `Match.isBisimulation_contracted` — the relation "node to its components" is a *strong*
    bisimulation between the hypergraph and the contracted tape graph (the contraction
    lemma: every step on one side is matched by exactly one step on the other);
  * `Match.isSWBisimulation_contraction` — the contraction, relating a component to every
    component of the same node and a root to the interior of its realization, is a *weak*
    bisimulation between the contracted and the actual tape graph;
  * `Match.isWeakBisimulation_weak` — their composite, `Match.weak`, is the
    **kind-transporting weak bisimulation** between the hypergraph and the tape graph: the
    weak bisimulation factors as the strong one composed with the contraction;
  * `Match.reachable_of_tape_path_comps` — the direction the seal consumes: every path of the
    tape graph between components projects to a path of the hypergraph between the nodes
    they realize;
  * `Match.occurrence_of_edge` — every tape edge between observable vertices realizes one
    hop of one occurrence, so the kinds transported along the relation change only where an
    occurrence of the hypergraph states the change.

Everything is proved from the acceptance clauses alone (`Match.Acc`), each clause read as
the proposition it decides.
-/

@[expose] public section Blanket

open Cslib

namespace PropertyKindCalculus

open Provenance (Occurrence EdgeFamily stepRel)

namespace Paradigm

/-! ## The label alphabet -/

/-- The label alphabet of the kind-transporting bisimulation: a visible step is an edge
family with the operand position it enters at; τ is `none`. -/
abbrev KindLabel := Option (EdgeFamily × Nat)

instance : HasTau KindLabel := ⟨none⟩

lemma KindLabel.tau_eq : (HasTau.τ : KindLabel) = none := rfl

/-- The label a family puts on a hop at an operand position: silent for the identity wire
and the procedure edge, visible for every witness family. -/
def labelOf : EdgeFamily → Nat → KindLabel
  | .copy, _ => none
  | .step _ _ _, _ => none
  | f, i => some (f, i)

end Paradigm

/-! ## The provenance layer as a labelled transition system -/

namespace Provenance

variable {ν κ : Type}

/-- **The provenance layer**: a hop from the operand at a position of an occurrence to its
result, labelled by the family and the position. Its unlabelled shadow is `stepRel`, the
value-flow digraph. -/
def lts (g : Provenance ν κ) : LTS ν Paradigm.KindLabel where
  Tr a μ b := ∃ o ∈ g.occurrences, b = o.result ∧
    ∃ i k, o.operands[i]? = some (a, k) ∧ μ = Paradigm.labelOf o.family i

lemma stepRel_of_lts_tr {g : Provenance ν κ} {a b : ν} {μ : Paradigm.KindLabel}
    (h : g.lts.Tr a μ b) : stepRel g.occurrences a b := by
  obtain ⟨o, ho, rfl, i, k, hi, -⟩ := h
  exact ⟨o, ho, rfl, (a, k), List.mem_of_getElem? hi, rfl⟩

lemma lts_tr_of_stepRel {g : Provenance ν κ} {a b : ν} (h : stepRel g.occurrences a b) :
    ∃ μ, g.lts.Tr a μ b := by
  obtain ⟨o, ho, rfl, oc, hoc, rfl⟩ := h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hoc
  exact ⟨Paradigm.labelOf o.family i, o, ho, rfl, i, oc.2, hi, rfl⟩

lemma reflTransGen_of_τSTr {g : Provenance ν κ} {a b : ν} (h : g.lts.τSTr a b) :
    Relation.ReflTransGen (stepRel g.occurrences) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih => exact ih.tail (stepRel_of_lts_tr hxy)

lemma reflTransGen_of_sTr {g : Provenance ν κ} {a b : ν} {μ : Paradigm.KindLabel}
    (h : g.lts.STr a μ b) : Relation.ReflTransGen (stepRel g.occurrences) a b := by
  cases h with
  | refl => exact Relation.ReflTransGen.refl
  | tr h1 h2 h3 =>
    exact (reflTransGen_of_τSTr h1).trans
      ((Relation.ReflTransGen.single (stepRel_of_lts_tr h2)).trans (reflTransGen_of_τSTr h3))

/-- A saturated step of the provenance layer is a path of the value-flow digraph. -/
lemma reachable_of_sTr {g : Provenance ν κ} {a b : ν} {μ : Paradigm.KindLabel}
    (h : g.lts.STr a μ b) : g.flowDigraph.Reachable a b :=
  Digraph.reachable_iff_reflTransGen.mpr (reflTransGen_of_sTr h)

end Provenance

namespace Paradigm

/-! ## Small facts about the tape graph -/

namespace TapeGraph

lemma parents_eq_nil_of_size_le (T : TapeGraph) {v : Nat} (h : T.size ≤ v) :
    T.parents v = [] := by
  simp [TapeGraph.parents, TapeGraph.vertex?, List.getElem?_eq_none h]

lemma lt_size_of_mem_parents (T : TapeGraph) {v p : Nat} (hp : p ∈ T.parents v) :
    v < T.size := by
  by_contra h
  rw [parents_eq_nil_of_size_le T (Nat.le_of_not_lt h)] at hp
  simp at hp

lemma lt_size_of_isOp (T : TapeGraph) {v : Nat} (h : T.isOp v = true) : v < T.size := by
  simp only [TapeGraph.isOp, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

lemma lt_size_of_isLeaf (T : TapeGraph) {v : Nat} (h : T.isLeaf v = true) : v < T.size := by
  simp only [TapeGraph.isLeaf, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

lemma isOp_of_mem_parents (T : TapeGraph) {v p : Nat} (hp : p ∈ T.parents v) :
    T.isOp v = true := by
  have hlt := lt_size_of_mem_parents T hp
  have hne : (T.parents v).isEmpty = false := by
    cases hpv : T.parents v with
    | nil => rw [hpv] at hp; simp at hp
    | cons q qs => rfl
  simp [TapeGraph.isOp, hlt, hne]

end TapeGraph

namespace Match

variable {ν κ : Type} [BEq ν] [LawfulBEq ν] [BEq κ]

/-! ## The three transition systems and the two relations -/

/-- `v` is a component of the operand at position `i` of a realized occurrence: a vertex of
the sub-graph's frontier, at that position. -/
def FrontierAt (g : Provenance ν κ) (m : Match ν) (r : Realized) (i : Nat) (v : Nat) : Prop :=
  ∃ a, operandAt g r i = some a ∧ v ∈ m.comps a

/-- **The contracted tape graph**: one hyperedge per realized occurrence, from a component
of the operand at a position to a component of the result, labelled by the family and the
position; a wire is a τ step. No interior. -/
def contracted (g : Provenance ν κ) (m : Match ν) : LTS Nat KindLabel where
  Tr v μ w := ∃ r ∈ m.realized, ∃ i, FrontierAt g m r i v ∧ w ∈ m.roots g r ∧
    ∃ o, occOf g r = some o ∧ μ = labelOf o.family i

/-- **The computational tape graph, labelled through the match**: the tape's own edges, an
edge into a non-wire realization visible at its frontier — labelled by the family and the
position the parent is a component of — and silent from the interior. Its unlabelled shadow
is exactly the tape's edge relation (`tapeLts_of_edge`). -/
def tapeLts (g : Provenance ν κ) (T : TapeGraph) (m : Match ν) : LTS Nat KindLabel where
  Tr v μ w := T.edge v w = true ∧ ∃ r ∈ m.realized, m.isWire g r = false ∧ w ∈ m.body g r ∧
    ((v ∈ r.interior ∧ μ = none) ∨
      ∃ i, FrontierAt g m r i v ∧ ∃ o, occOf g r = some o ∧ μ = labelOf o.family i)

/-- The observable relation: a node to each of its components. -/
def obs (m : Match ν) (a : ν) (v : Nat) : Prop := v ∈ m.comps a

/-- **The contraction**: a component to every component of the same node, and a root to
every interior vertex of its realization — the relation under which the interior is the
result under construction. -/
def contraction (g : Provenance ν κ) (m : Match ν) (v v' : Nat) : Prop :=
  (∃ a, v ∈ m.comps a ∧ v' ∈ m.comps a) ∨
    ∃ r ∈ m.realized, m.isWire g r = false ∧ v ∈ m.roots g r ∧ v' ∈ r.interior

/-- **The kind-transporting weak bisimulation**: the observable relation composed with the
contraction — a node to each of its components, and the result of a realized occurrence to
each interior vertex of the realization. -/
def weak (g : Provenance ν κ) (m : Match ν) : ν → Nat → Prop :=
  Relation.Comp (obs m) (contraction g m)

omit [LawfulBEq ν] [BEq κ] in
lemma weak_of_mem_comps {g : Provenance ν κ} {m : Match ν} {a : ν} {v : Nat}
    (h : v ∈ m.comps a) : weak g m a v :=
  ⟨v, h, Or.inl ⟨a, h, h⟩⟩

/-! ## Acceptance, clause by clause -/

/-- The acceptance judgment, one field per clause. -/
structure Acc (g : Provenance ν κ) (T : TapeGraph) (m : Match ν) : Prop where
  ord : T.ordered = true
  tot : totalOnNodes g T m = true
  uniq : Match.uniqueKeys m = true
  keys : keysDeclared g m = true
  disj : componentsDisjoint m = true
  leafSrc : leavesAreSources g T m = true
  srcLeaf : sourcesAreLeaves g T m = true
  rok : m.realized.all (realizedOk g T m) = true
  ints : interiorsDisjoint m = true
  cov : covering g T m = true
  all : realizesAll g m = true
  inG : realizedInGraph g m = true

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.of_accepts {g : Provenance ν κ} {T : TapeGraph} {m : Match ν}
    (h : m.accepts g T = true) : Acc g T m := by
  simp only [accepts, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

section Clauses

variable {g : Provenance ν κ} {T : TapeGraph} {m : Match ν}

lemma exists_entry_of_mem_comps {n : ν} {v : Nat} (hv : v ∈ m.comps n) :
    ∃ e ∈ m.components, e.1 = n ∧ v ∈ e.2 := by
  unfold comps at hv
  split at hv
  · rename_i e he
    exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, hv⟩
  · simp at hv

omit [LawfulBEq ν] [BEq κ] in
lemma roots_eq {r : Realized} {o : Occurrence ν κ} (ho : occOf g r = some o) :
    m.roots g r = m.comps o.result := by
  simp [roots, ho]

omit [LawfulBEq ν] [BEq κ] in
lemma mem_body_iff {r : Realized} {w : Nat} :
    w ∈ m.body g r ↔ w ∈ r.interior ∨ w ∈ m.roots g r :=
  List.mem_append

omit [LawfulBEq ν] [BEq κ] in
lemma frontierAt_of_mem_frontier {r : Realized} {v : Nat} (hv : v ∈ m.frontier g r) :
    ∃ i, FrontierAt g m r i v := by
  unfold frontier at hv
  split at hv
  · rename_i o ho
    obtain ⟨oc, hoc, hvc⟩ := List.mem_flatMap.mp hv
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hoc
    exact ⟨i, oc.1, by simp [operandAt, ho, hi], hvc⟩
  · simp at hv

omit [LawfulBEq ν] [BEq κ] in
lemma mem_frontier_of_frontierAt {r : Realized} {i v : Nat} (h : FrontierAt g m r i v) :
    v ∈ m.frontier g r := by
  obtain ⟨a, ha, hva⟩ := h
  unfold operandAt at ha
  split at ha
  · rename_i o ho
    simp only [Option.map_eq_some_iff] at ha
    obtain ⟨oc, hoc, rfl⟩ := ha
    unfold frontier
    rw [ho]
    exact List.mem_flatMap.mpr ⟨oc, List.mem_of_getElem? hoc, hva⟩
  · exact absurd ha (by simp)

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.parent_lt (hA : Acc g T m) {v p : Nat} (hp : p ∈ T.parents v) : p < v := by
  by_cases hv : v < T.size
  · have h := hA.ord
    simp only [TapeGraph.ordered, List.all_eq_true, List.mem_range] at h
    exact of_decide_eq_true (h v hv p hp)
  · rw [TapeGraph.parents_eq_nil_of_size_le T (Nat.le_of_not_lt hv)] at hp
    simp at hp

omit [BEq κ] in
lemma Acc.comps_inj (hA : Acc g T m) {a b : ν} {v : Nat} (ha : v ∈ m.comps a)
    (hb : v ∈ m.comps b) : a = b := by
  obtain ⟨ea, hea, rfl, hva⟩ := exists_entry_of_mem_comps ha
  obtain ⟨eb, heb, rfl, hvb⟩ := exists_entry_of_mem_comps hb
  have hd := hA.disj
  simp only [componentsDisjoint, List.all_eq_true] at hd
  have hlen : (m.components.filter (·.2.contains v)).length = 1 := by
    simpa using hd ea hea v hva
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  have hma : ea ∈ m.components.filter (·.2.contains v) :=
    List.mem_filter.mpr ⟨hea, List.contains_iff_mem.mpr hva⟩
  have hmb : eb ∈ m.components.filter (·.2.contains v) :=
    List.mem_filter.mpr ⟨heb, List.contains_iff_mem.mpr hvb⟩
  rw [hx] at hma hmb
  rw [List.mem_singleton.mp hma, List.mem_singleton.mp hmb]

omit [BEq κ] in
lemma Acc.comps_lt (hA : Acc g T m) {n : ν} {v : Nat} (hv : v ∈ m.comps n) : v < T.size := by
  obtain ⟨e, he, rfl, hve⟩ := exists_entry_of_mem_comps hv
  have hk := hA.keys
  simp only [keysDeclared, List.all_eq_true] at hk
  have hdecl : e.1 ∈ nodesOf g := List.contains_iff_mem.mp (hk e he)
  have ht := hA.tot
  simp only [totalOnNodes, List.all_eq_true, Bool.and_eq_true] at ht
  exact of_decide_eq_true ((ht e.1 hdecl).2 v hv)

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.comps_nonempty (hA : Acc g T m) {n : ν} (hn : n ∈ nodesOf g) : m.comps n ≠ [] := by
  have ht := hA.tot
  simp only [totalOnNodes, List.all_eq_true, Bool.and_eq_true] at ht
  have h1 := (ht n hn).1
  intro h
  rw [h] at h1
  simp at h1

omit [BEq κ] in
lemma Acc.not_mem_comps_of_mem_interior (hA : Acc g T m) {r : Realized} (hr : r ∈ m.realized)
    {v : Nat} (hv : v ∈ r.interior) (a : ν) : v ∉ m.comps a := by
  intro hva
  obtain ⟨e, he, -, hve⟩ := exists_entry_of_mem_comps hva
  have hi := hA.ints
  simp only [interiorsDisjoint, List.all_eq_true, Bool.and_eq_true] at hi
  have h1 := (hi r hr v hv).1
  have h2 : m.isComponent v = true := by
    unfold isComponent
    exact List.any_eq_true.mpr ⟨e, he, List.contains_iff_mem.mpr hve⟩
  rw [h2] at h1
  simp at h1

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.interior_inj (hA : Acc g T m) {r r' : Realized} (hr : r ∈ m.realized)
    (hr' : r' ∈ m.realized) {v : Nat} (hv : v ∈ r.interior) (hv' : v ∈ r'.interior) : r = r' := by
  have hi := hA.ints
  simp only [interiorsDisjoint, List.all_eq_true, Bool.and_eq_true] at hi
  have hlen : (m.realized.filter (·.interior.contains v)).length = 1 := by
    simpa using (hi r hr v hv).2
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  have hma : r ∈ m.realized.filter (·.interior.contains v) :=
    List.mem_filter.mpr ⟨hr, List.contains_iff_mem.mpr hv⟩
  have hmb : r' ∈ m.realized.filter (·.interior.contains v) :=
    List.mem_filter.mpr ⟨hr', List.contains_iff_mem.mpr hv'⟩
  rw [hx] at hma hmb
  rw [List.mem_singleton.mp hma, List.mem_singleton.mp hmb]

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.occOf_some (hA : Acc g T m) {r : Realized} (hr : r ∈ m.realized) :
    ∃ o, occOf g r = some o := by
  have h := hA.inG
  simp only [realizedInGraph, List.all_eq_true] at h
  have hlt : r.occ < g.occurrences.length := of_decide_eq_true (h r hr)
  exact ⟨g.occurrences[r.occ], by unfold occOf; exact List.getElem?_eq_getElem hlt⟩

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.exists_realized (hA : Acc g T m) {o : Occurrence ν κ} (ho : o ∈ g.occurrences) :
    ∃ r ∈ m.realized, occOf g r = some o := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ho
  have h := hA.all
  simp only [realizesAll, List.all_eq_true, List.mem_range, List.any_eq_true] at h
  have hjlt : j < g.occurrences.length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨r, hr, hrj⟩ := h j hjlt
  refine ⟨r, hr, ?_⟩
  unfold occOf
  rw [show r.occ = j by simpa using hrj]
  exact hj

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.realizedOk_of_mem (hA : Acc g T m) {r : Realized} (hr : r ∈ m.realized) :
    realizedOk g T m r = true :=
  List.all_eq_true.mp hA.rok r hr

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.nonwire_clauses (hA : Acc g T m) {r : Realized} (hr : r ∈ m.realized)
    (hw : m.isWire g r = false) :
    realizedClosed g T m r = true ∧ interiorPrivate g T m r = true ∧
      interiorProgress g T m r = true ∧ frontierUsed g T m r = true ∧ bodyOps g T m r = true := by
  have h := hA.realizedOk_of_mem hr
  simp only [realizedOk, hw, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.closed (hA : Acc g T m) {r : Realized} (hr : r ∈ m.realized)
    (hw : m.isWire g r = false) {w : Nat} (hwb : w ∈ m.body g r) {p : Nat}
    (hp : p ∈ T.parents w) : p ∈ r.interior ∨ ∃ i, FrontierAt g m r i p := by
  have hc := (hA.nonwire_clauses hr hw).1
  simp only [realizedClosed, List.all_eq_true] at hc
  rcases Bool.or_eq_true .. ▸ hc w hwb p hp with h1 | h1
  · exact Or.inl (List.contains_iff_mem.mp h1)
  · exact Or.inr (frontierAt_of_mem_frontier (List.contains_iff_mem.mp h1))

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.private_ (hA : Acc g T m) {r : Realized} (hr : r ∈ m.realized)
    (hw : m.isWire g r = false) {p : Nat} (hp : p ∈ r.interior) {w : Nat}
    (he : T.edge p w = true) : w ∈ m.body g r := by
  have hc := (hA.nonwire_clauses hr hw).2.1
  simp only [interiorPrivate, List.all_eq_true, List.mem_range] at hc
  have hpw : p ∈ T.parents w := List.contains_iff_mem.mp he
  have hwlt : w < T.size := TapeGraph.lt_size_of_mem_parents T hpw
  rcases Bool.or_eq_true .. ▸ hc w hwlt with h1 | h1
  · exfalso
    have : (T.parents w).any r.interior.contains = true :=
      List.any_eq_true.mpr ⟨p, hpw, List.contains_iff_mem.mpr hp⟩
    rw [this] at h1
    simp at h1
  · exact List.contains_iff_mem.mp h1

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.progress (hA : Acc g T m) {r : Realized} (hr : r ∈ m.realized)
    (hw : m.isWire g r = false) {p : Nat} (hp : p ∈ r.interior) :
    ∃ w ∈ m.body g r, T.edge p w = true := by
  have hc := (hA.nonwire_clauses hr hw).2.2.1
  simp only [interiorProgress, List.all_eq_true, List.any_eq_true] at hc
  exact hc p hp

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.used (hA : Acc g T m) {r : Realized} (hr : r ∈ m.realized)
    (hw : m.isWire g r = false) {i v : Nat} (hv : FrontierAt g m r i v) :
    ∃ w ∈ m.body g r, T.edge v w = true := by
  have hc := (hA.nonwire_clauses hr hw).2.2.2.1
  simp only [frontierUsed, List.all_eq_true, List.any_eq_true] at hc
  exact hc v (mem_frontier_of_frontierAt hv)

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.body_isOp (hA : Acc g T m) {r : Realized} (hr : r ∈ m.realized)
    (hw : m.isWire g r = false) {w : Nat} (hwb : w ∈ m.body g r) : T.isOp w = true := by
  have hc := (hA.nonwire_clauses hr hw).2.2.2.2
  simp only [bodyOps, List.all_eq_true] at hc
  exact hc w hwb

omit [BEq ν] [LawfulBEq ν] [BEq κ] in
lemma wireOk_iff {r : Realized} {o : Occurrence ν κ} (ho : occOf g r = some o) :
    wireOk g r = true ↔ o.family = .copy ∨ ∃ mb j a, o.family = .step mb j a := by
  unfold wireOk
  simp only [familyOf, ho, Option.map_some]
  cases o.family <;> simp

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.wire_spec (hA : Acc g T m) {r : Realized} (hr : r ∈ m.realized)
    (hw : m.isWire g r = true) :
    ∃ (o : Occurrence ν κ) (oc : ν × κ), occOf g r = some o ∧ o.operands = [oc] ∧
      (∀ v, v ∈ m.comps oc.1 ↔ v ∈ m.comps o.result) ∧
      (o.family = .copy ∨ ∃ mb j a, o.family = .step mb j a) := by
  have hw' := hw
  unfold isWire at hw'
  simp only [Bool.and_eq_true] at hw'
  obtain ⟨-, hm⟩ := hw'
  split at hm
  · rename_i o ho
    split at hm
    · rename_i oc hops
      simp only [Bool.and_eq_true, List.all_eq_true] at hm
      obtain ⟨h1, h2⟩ := hm
      refine ⟨o, oc, ho, hops, fun v => ⟨fun hv => List.contains_iff_mem.mp (h1 v hv),
        fun hv => List.contains_iff_mem.mp (h2 v hv)⟩, ?_⟩
      have hok := hA.realizedOk_of_mem hr
      simp only [realizedOk, hw, ↓reduceIte] at hok
      exact (wireOk_iff ho).mp hok
    · simp at hm
  · simp at hm

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.covered (hA : Acc g T m) {v : Nat} (hv : T.isOp v = true) :
    ∃ r ∈ m.realized, m.isWire g r = false ∧ v ∈ m.body g r := by
  have h := hA.cov
  simp only [covering, List.all_eq_true, List.any_eq_true, Bool.and_eq_true] at h
  have hvo : v ∈ T.ops :=
    List.mem_filter.mpr ⟨List.mem_range.mpr (TapeGraph.lt_size_of_isOp T hv), hv⟩
  obtain ⟨r, hr, h1, h2⟩ := h v hvo
  exact ⟨r, hr, by simpa using h1, List.contains_iff_mem.mp h2⟩

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.leaf_comps (hA : Acc g T m) {v : Nat} (hv : T.isLeaf v = true) :
    ∃ s ∈ g.sources, v ∈ m.comps s := by
  have h := hA.leafSrc
  simp only [leavesAreSources, List.all_eq_true, List.any_eq_true] at h
  have hvl : v ∈ T.leaves :=
    List.mem_filter.mpr ⟨List.mem_range.mpr (TapeGraph.lt_size_of_isLeaf T hv), hv⟩
  obtain ⟨s, hs, hvs⟩ := h v hvl
  exact ⟨s, hs, List.contains_iff_mem.mp hvs⟩

omit [LawfulBEq ν] [BEq κ] in
lemma Acc.source_leaf (hA : Acc g T m) {s : ν} (hs : s ∈ g.sources) {v : Nat}
    (hv : v ∈ m.comps s) : T.isLeaf v = true := by
  have h := hA.srcLeaf
  simp only [sourcesAreLeaves, List.all_eq_true] at h
  exact h s hs v hv

/-- The result of an occurrence of a well-formed graph is a declared node. -/
lemma result_declared (hwf : g.WellFormed) {o : Occurrence ν κ} (ho : o ∈ g.occurrences) :
    o.result ∈ nodesOf g := by
  have h := hwf.clauses.2.2.1
  simp only [Provenance.resultsAreDerivations, List.all_eq_true] at h
  rcases Bool.or_eq_true .. ▸ h o ho with h1 | h1
  · obtain ⟨i, hi, hh⟩ := List.any_eq_true.mp h1
    have : i.node = o.result := beq_iff_eq.mp (Bool.and_eq_true .. ▸ hh).1
    exact List.mem_append_right _ (List.mem_map.mpr ⟨i, hi, this⟩)
  · obtain ⟨p, hp, hh⟩ := List.any_eq_true.mp h1
    have : p.node = o.result := beq_iff_eq.mp (Bool.and_eq_true .. ▸ hh).1
    exact List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, this⟩)

omit [LawfulBEq ν] [BEq κ] in
/-- An interior vertex of a non-wire realization reaches a root of it through silent steps. -/
lemma Acc.interior_reaches_root (hA : Acc g T m) {r : Realized} (hr : r ∈ m.realized)
    (hw : m.isWire g r = false) :
    ∀ (n p : Nat), T.size - p = n → p ∈ r.interior →
      ∃ u ∈ m.roots g r, (m.tapeLts g T).τSTr p u := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih p hn hp
  obtain ⟨x, hx, hpx⟩ := hA.progress hr hw hp
  have htr : (m.tapeLts g T).Tr p none x := ⟨hpx, r, hr, hw, hx, Or.inl ⟨hp, rfl⟩⟩
  rcases mem_body_iff.mp hx with hxi | hxr
  · have hpx' : p < x := hA.parent_lt (List.contains_iff_mem.mp hpx)
    have hxlt : x < T.size := TapeGraph.lt_size_of_isOp T (hA.body_isOp hr hw hx)
    obtain ⟨u, hu, hchain⟩ := ih (T.size - x) (by omega) x rfl hxi
    exact ⟨u, hu, Relation.ReflTransGen.head htr hchain⟩
  · exact ⟨x, hxr, Relation.ReflTransGen.single htr⟩

end Clauses

/-! ## The strong bisimulation with the contracted tape graph -/

/-- **The contraction lemma.** Under acceptance, "node to its components" is a strong
bisimulation between the provenance layer and the contracted tape graph: every hop of the
hypergraph is matched by one hyperedge of the contraction and conversely, with no silent
step. -/
lemma isBisimulation_contracted {g : Provenance ν κ} {T : TapeGraph} {m : Match ν}
    (hwf : g.WellFormed) (hA : Acc g T m) :
    LTS.IsBisimulation g.lts (m.contracted g) (obs m) := by
  intro a v hav μ
  constructor
  · intro b hab
    obtain ⟨o, ho, rfl, i, k, hi, rfl⟩ := hab
    obtain ⟨r, hr, hro⟩ := hA.exists_realized ho
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ (hA.comps_nonempty (result_declared hwf ho))
    refine ⟨w, ⟨r, hr, i, ⟨a, ?_, hav⟩, ?_, o, hro, rfl⟩, hw⟩
    · simp [operandAt, hro, hi]
    · rw [roots_eq hro]; exact hw
  · intro w hvw
    obtain ⟨r, hr, i, ⟨a', ha', hva'⟩, hw, o, hro, rfl⟩ := hvw
    obtain rfl : a = a' := hA.comps_inj hav hva'
    simp only [operandAt, hro, Option.map_eq_some_iff] at ha'
    obtain ⟨oc, hoc, rfl⟩ := ha'
    refine ⟨o.result, ⟨o, List.mem_of_getElem? hro, rfl, i, oc.2, hoc, rfl⟩, ?_⟩
    rw [roots_eq hro] at hw
    exact hw

/-! ## The contraction is a weak bisimulation with the tape graph -/

/-- **The contraction is a weak bisimulation** between the contracted tape graph and the
tape graph: a hyperedge of the contraction is matched on the tape by the edge into the
realization, whose interior the contraction absorbs, and a tape edge is matched by the
hyperedge it belongs to — or by nothing at all, when it is an interior step. -/
lemma isSWBisimulation_contraction {g : Provenance ν κ} {T : TapeGraph} {m : Match ν}
    (hwf : g.WellFormed) (hA : Acc g T m) :
    LTS.IsSWBisimulation (m.contracted g) (m.tapeLts g T) (contraction g m) := by
  intro v v' hvv' μ
  constructor
  · intro w hvw
    obtain ⟨r, hr, i, ⟨a', ha', hva'⟩, hw, o, hro, rfl⟩ := hvw
    rw [roots_eq hro] at hw
    by_cases hwire : m.isWire g r = true
    · obtain ⟨o', oc, hro', hops, hcomp, hfam⟩ := hA.wire_spec hr hwire
      rw [hro] at hro'
      obtain rfl := Option.some.inj hro'
      have hlab : labelOf o.family i = none := by
        rcases hfam with h | ⟨mb, j, ar, h⟩ <;> simp [h, labelOf]
      have ha'oc : a' = oc.1 := by
        simp only [operandAt, hro, hops] at ha'
        cases i with
        | zero => exact (Option.some.inj ha').symm
        | succ j => exact nomatch ha'
      subst ha'oc
      refine ⟨v', by rw [hlab]; exact LTS.STr.refl, ?_⟩
      rcases hvv' with ⟨c, hvc, hv'c⟩ | ⟨r₀, hr₀, hw₀, hvr₀, hv'i⟩
      · rw [hA.comps_inj hvc hva'] at hv'c
        exact Or.inl ⟨o.result, hw, (hcomp v').mp hv'c⟩
      · obtain ⟨o₀, hro₀⟩ := hA.occOf_some hr₀
        rw [roots_eq hro₀] at hvr₀
        have hres : o₀.result = oc.1 := hA.comps_inj hvr₀ hva'
        refine Or.inr ⟨r₀, hr₀, hw₀, ?_, hv'i⟩
        rw [roots_eq hro₀, hres]
        exact (hcomp w).mpr hw
    · have hw' : m.isWire g r = false := by simpa using hwire
      have hu : ∃ u, u ∈ m.comps a' ∧ (m.tapeLts g T).τSTr v' u := by
        rcases hvv' with ⟨c, hvc, hv'c⟩ | ⟨r₀, hr₀, hw₀, hvr₀, hv'i⟩
        · rw [hA.comps_inj hvc hva'] at hv'c
          exact ⟨v', hv'c, Relation.ReflTransGen.refl⟩
        · obtain ⟨o₀, hro₀⟩ := hA.occOf_some hr₀
          rw [roots_eq hro₀] at hvr₀
          obtain ⟨u, hu, hchain⟩ := hA.interior_reaches_root hr₀ hw₀ _ v' rfl hv'i
          rw [roots_eq hro₀] at hu
          have hres : o₀.result = a' := hA.comps_inj hvr₀ hva'
          exact ⟨u, hres ▸ hu, hchain⟩
      obtain ⟨u, hua', hchain⟩ := hu
      have hfu : FrontierAt g m r i u := ⟨a', ha', hua'⟩
      obtain ⟨x, hx, hux⟩ := hA.used hr hw' hfu
      have htr : (m.tapeLts g T).Tr u (labelOf o.family i) x :=
        ⟨hux, r, hr, hw', hx, Or.inr ⟨i, hfu, o, hro, rfl⟩⟩
      refine ⟨x, LTS.STr.tr hchain htr Relation.ReflTransGen.refl, ?_⟩
      rcases mem_body_iff.mp hx with hxi | hxr
      · exact Or.inr ⟨r, hr, hw', by rw [roots_eq hro]; exact hw, hxi⟩
      · rw [roots_eq hro] at hxr
        exact Or.inl ⟨o.result, hw, hxr⟩
  · intro x hv'x
    obtain ⟨hedge, r, hr, hw', hx, hcase⟩ := hv'x
    rcases hcase with ⟨hv'i, rfl⟩ | ⟨i, ⟨a', ha', hv'a'⟩, o, hro, rfl⟩
    · rcases hvv' with ⟨c, hvc, hv'c⟩ | ⟨r₀, hr₀, hw₀, hvr₀, hv'i₀⟩
      · exact absurd hv'c (hA.not_mem_comps_of_mem_interior hr hv'i c)
      · obtain rfl : r₀ = r := hA.interior_inj hr₀ hr hv'i₀ hv'i
        refine ⟨v, LTS.STr.refl, ?_⟩
        rcases mem_body_iff.mp hx with hxi | hxr
        · exact Or.inr ⟨r₀, hr₀, hw₀, hvr₀, hxi⟩
        · obtain ⟨o₀, hro₀⟩ := hA.occOf_some hr₀
          rw [roots_eq hro₀] at hvr₀ hxr
          exact Or.inl ⟨o₀.result, hvr₀, hxr⟩
    · have hva' : v ∈ m.comps a' := by
        rcases hvv' with ⟨c, hvc, hv'c⟩ | ⟨r₀, hr₀, hw₀, hvr₀, hv'i₀⟩
        · rw [hA.comps_inj hv'c hv'a'] at hvc
          exact hvc
        · exact absurd hv'a' (hA.not_mem_comps_of_mem_interior hr₀ hv'i₀ a')
      have hdecl : o.result ∈ nodesOf g := result_declared hwf (List.mem_of_getElem? hro)
      rcases mem_body_iff.mp hx with hxi | hxr
      · obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ (hA.comps_nonempty hdecl)
        refine ⟨w, LTS.STr.single ⟨r, hr, i, ⟨a', ha', hva'⟩, ?_, o, hro, rfl⟩,
          Or.inr ⟨r, hr, hw', ?_, hxi⟩⟩ <;> (rw [roots_eq hro]; exact hw)
      · refine ⟨x, LTS.STr.single ⟨r, hr, i, ⟨a', ha', hva'⟩, hxr, o, hro, rfl⟩, ?_⟩
        rw [roots_eq hro] at hxr
        exact Or.inl ⟨o.result, hxr, hxr⟩

/-! ## The kind-transporting weak bisimulation, as the composite -/

/-- A strong bisimulation is a weak one: every step it matches is a saturated step. -/
lemma _root_.Cslib.LTS.IsBisimulation.isWeakBisimulation' {S₁ S₂ L : Type} [HasTau L]
    {l₁ : LTS S₁ L} {l₂ : LTS S₂ L} {r : S₁ → S₂ → Prop} (h : LTS.IsBisimulation l₁ l₂ r) :
    LTS.IsWeakBisimulation l₁ l₂ r := by
  refine LTS.IsSWBisimulation.isWeakBisimulation ?_
  intro s₁ s₂ hr μ
  obtain ⟨h1, h2⟩ := h hr μ
  exact ⟨fun s₁' ht => (h1 s₁' ht).elim fun s₂' ⟨ht', hr'⟩ => ⟨s₂', LTS.STr.single ht', hr'⟩,
    fun s₂' ht => (h2 s₂' ht).elim fun s₁' ⟨ht', hr'⟩ => ⟨s₁', LTS.STr.single ht', hr'⟩⟩

/-- **The kind-transporting weak bisimulation.** Under well-formedness and acceptance, the
composite of "node to its components" with the contraction is a weak bisimulation between
the provenance layer and the tape graph: the weak bisimulation factors as the strong one
with the contracted graph composed with the contraction. -/
lemma isWeakBisimulation_weak {g : Provenance ν κ} {T : TapeGraph} {m : Match ν}
    (hwf : g.WellFormed) (hA : Acc g T m) :
    LTS.IsWeakBisimulation g.lts (m.tapeLts g T) (weak g m) :=
  (isBisimulation_contracted hwf hA).isWeakBisimulation'.comp
    (isSWBisimulation_contraction hwf hA).isWeakBisimulation

/-! ## The direction the seal consumes -/

omit [LawfulBEq ν] [BEq κ] in
/-- Every edge of the tape graph is a transition of the labelled tape graph: the labelling
adds labels and forgets no edge. -/
lemma tapeLts_of_edge {g : Provenance ν κ} {T : TapeGraph} {m : Match ν} (hA : Acc g T m)
    {u w : Nat} (he : T.edge u w = true) : ∃ μ, (m.tapeLts g T).Tr u μ w := by
  have hu : u ∈ T.parents w := List.contains_iff_mem.mp he
  obtain ⟨r, hr, hw', hwb⟩ := hA.covered (TapeGraph.isOp_of_mem_parents T hu)
  rcases hA.closed hr hw' hwb hu with hui | ⟨i, hfi⟩
  · exact ⟨none, he, r, hr, hw', hwb, Or.inl ⟨hui, rfl⟩⟩
  · obtain ⟨o, hro⟩ := hA.occOf_some hr
    exact ⟨labelOf o.family i, he, r, hr, hw', hwb, Or.inr ⟨i, hfi, o, hro, rfl⟩⟩

/-- Every path of the tape graph from a vertex the relation reaches projects to a path of the
hypergraph: the tape-to-hypergraph half of the weak bisimulation, iterated. -/
lemma reachable_of_tape_path {g : Provenance ν κ} {T : TapeGraph} {m : Match ν}
    (hwf : g.WellFormed) (hA : Acc g T m) {u w : Nat}
    (hpath : Relation.ReflTransGen (fun x y => T.edge x y = true) u w)
    {a : ν} (hau : weak g m a u) : ∃ b, weak g m b w ∧ g.flowDigraph.Reachable a b := by
  induction hpath with
  | refl => exact ⟨a, hau, Digraph.Reachable.refl a⟩
  | @tail x y _ hxy ih =>
    obtain ⟨b, hbx, hab⟩ := ih
    obtain ⟨μ, htr⟩ := tapeLts_of_edge hA hxy
    have hs : (m.tapeLts g T).saturate.Tr x μ y := LTS.STr.single htr
    obtain ⟨c, hbc, hcy⟩ := (isWeakBisimulation_weak hwf hA hbx μ).2 y hs
    exact ⟨c, hcy, hab.trans (Provenance.reachable_of_sTr hbc)⟩

/-- **Soundness, the direction the seal consumes.** Under well-formedness and acceptance,
every path of the tape graph from a component of a node `s` to a component of a node `b` is
a path of the value-flow digraph from `s` to `b`. -/
lemma reachable_of_tape_path_comps {g : Provenance ν κ} {T : TapeGraph} {m : Match ν}
    (hwf : g.WellFormed) (hA : Acc g T m) {u w : Nat}
    (hpath : Relation.ReflTransGen (fun x y => T.edge x y = true) u w)
    {s b : ν} (hs : u ∈ m.comps s) (hb : w ∈ m.comps b) : g.flowDigraph.Reachable s b := by
  obtain ⟨c, hcw, hsc⟩ := reachable_of_tape_path hwf hA hpath (weak_of_mem_comps hs)
  obtain ⟨v, hcv, hvw⟩ := hcw
  rcases hvw with ⟨d, hvd, hwd⟩ | ⟨r, hr, -, -, hwi⟩
  · rw [hA.comps_inj hcv hvd, hA.comps_inj hwd hb] at hsc
    exact hsc
  · exact absurd hb (hA.not_mem_comps_of_mem_interior hr hwi b)

/-- **The kind clause.** Every tape edge between two observable vertices — a component of
`a` into a component of `b` — realizes one hop of one occurrence of the hypergraph, from
its operand `a` at some position to its result `b`; so the kinds transported along the
relation change across a tape edge only where an occurrence states the change, and the
kinds are those the occurrence names. -/
lemma occurrence_of_edge {g : Provenance ν κ} {T : TapeGraph} {m : Match ν}
    (hwf : g.WellFormed) (hA : Acc g T m) {u w : Nat} (he : T.edge u w = true)
    {a b : ν} (hu : u ∈ m.comps a) (hw : w ∈ m.comps b) :
    ∃ o ∈ g.occurrences, o.result = b ∧
      ∃ (i : Nat) (k : κ), o.operands[i]? = some (a, k) ∧
        (g.kindOf? a == some k) = true ∧ (g.kindOf? b == some o.resultKind) = true := by
  have hu' : u ∈ T.parents w := List.contains_iff_mem.mp he
  obtain ⟨r, hr, hw', hwb⟩ := hA.covered (TapeGraph.isOp_of_mem_parents T hu')
  obtain ⟨o, hro⟩ := hA.occOf_some hr
  have ho : o ∈ g.occurrences := List.mem_of_getElem? hro
  have hwr : w ∈ m.roots g r := by
    rcases mem_body_iff.mp hwb with hwi | hwr
    · exact absurd hw (hA.not_mem_comps_of_mem_interior hr hwi b)
    · exact hwr
  rw [roots_eq hro] at hwr
  obtain rfl : b = o.result := hA.comps_inj hw hwr
  rcases hA.closed hr hw' hwb hu' with hui | ⟨i, a', ha', hua'⟩
  · exact absurd hu (hA.not_mem_comps_of_mem_interior hr hui a)
  · obtain rfl : a = a' := hA.comps_inj hu hua'
    simp only [operandAt, hro, Option.map_eq_some_iff] at ha'
    obtain ⟨oc, hoc, rfl⟩ := ha'
    have ht := hwf.clauses.2.1
    simp only [Provenance.occurrencesTyped, List.all_eq_true, Bool.and_eq_true] at ht
    have hto := ht o ho
    exact ⟨o, ho, rfl, i, oc.2, hoc, hto.1.1.2 oc (List.mem_of_getElem? hoc), hto.1.2⟩

end Match

end Paradigm

end PropertyKindCalculus

end Blanket
