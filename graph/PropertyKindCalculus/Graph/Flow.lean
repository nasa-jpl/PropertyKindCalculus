import PropertyKindCalculus.Influence
import ForMathlib.Combinatorics.Digraph.Acyclic
import ForMathlib.Combinatorics.Digraph.Condensation

/-!
# The value-flow digraph — the executable closures against their path semantics

`Provenance.influencedFrom` and `Provenance.ancestorsOf` are prelude-only, fuel-bounded
list fixpoints; the queries built on them prune perturbation studies, assemble assumption
ledgers, and scope re-validation. What licenses those uses is proved here: the closures
compute exactly reachability in the **value-flow digraph** — one vertex per node, one edge
per (operand position, result) pair of an occurrence — so

  * `Provenance.mem_influencedFrom_iff` / `Provenance.mem_ancestorsOf_iff`: membership in
    the executable closure is reachability (forward, respectively backward);
  * `Provenance.mayInfluence_iff` and its contrapositive
    `Provenance.not_reachable_of_mayInfluence_eq_false`: the sound direction of
    sensitivity scoping — a `false` from the probe is a *theorem* that no path exists,
    so excluding the input from a perturbation study drops no real influence;
  * `Provenance.acyclic_iff_isAcyclic`: the executable acyclicity check decides
    `Digraph.IsAcyclic` of the value flow, the hypothesis under which `ForMathlib`'s
    topological sorts, reachability partial orders, and condensations apply to a
    provenance graph.

The saturation argument mirrors `Relation.reachSet`'s, on lists: one sweep only appends,
appended nodes are pairwise-distinct occurrence results, so with one sweep per occurrence
plus one the closure either observed a fixpoint or would have outgrown its own bound.
-/

namespace PropertyKindCalculus

namespace Provenance

variable {ν κ : Type}

/-- One influence hop over an occurrence list: some occurrence takes `a` at some operand
position and produces `b`. -/
def stepRel (occs : List (Occurrence ν κ)) (a b : ν) : Prop :=
  ∃ o ∈ occs, o.result = b ∧ ∃ oc ∈ o.operands, oc.1 = a

/-- The value-flow digraph of a provenance graph: nodes, wired operand-to-result through
the occurrences. The binary shadow of the ordered hyperedge incidence — enough for every
reachability-shaped query; the hyperedge structure itself stays on the `Provenance`. -/
def flowDigraph (g : Provenance ν κ) : Digraph ν where
  Adj := stepRel g.occurrences

@[simp]
theorem flowDigraph_adj {g : Provenance ν κ} {a b : ν} :
    (g.flowDigraph).Adj a b ↔ stepRel g.occurrences a b := Iff.rfl

variable [BEq ν] [LawfulBEq ν]

/-! ### The sweep appends a fresh, duplicate-free batch of results -/

omit [LawfulBEq ν] in
private theorem influenceSweep_cons (o : Occurrence ν κ) (rest : List (Occurrence ν κ))
    (ks : List ν) :
    influenceSweep (o :: rest) ks = influenceSweep rest (influenceSweep [o] ks) := rfl

omit [LawfulBEq ν] in
private theorem influenceSweep_singleton (o : Occurrence ν κ) (ks : List ν) :
    influenceSweep [o] ks =
      if o.operands.any (fun oc => ks.contains oc.1) && !ks.contains o.result then
        ks ++ [o.result]
      else ks := rfl

private theorem influenceSweep_shape (occs : List (Occurrence ν κ)) :
    ∀ ks : List ν, ∃ l, influenceSweep occs ks = ks ++ l ∧ l.Nodup ∧
      ∀ x ∈ l, x ∉ ks ∧ x ∈ occs.map (·.result) := by
  induction occs with
  | nil => exact fun ks => ⟨[], by simp [influenceSweep]⟩
  | cons o rest ih =>
    intro ks
    rw [influenceSweep_cons]
    by_cases hc : (o.operands.any (fun oc => ks.contains oc.1) && !ks.contains o.result) = true
    · have hstep : influenceSweep [o] ks = ks ++ [o.result] := by
        rw [influenceSweep_singleton, ite_eq_left hc]
      have hfresh : o.result ∉ ks := by
        have := (Bool.and_eq_true .. ▸ hc).2
        simpa [List.contains_iff_mem] using this
      obtain ⟨l, hl, hnd, hmem⟩ := ih (ks ++ [o.result])
      refine ⟨o.result :: l, ?_, ?_, ?_⟩
      · rw [hstep, hl, List.append_assoc, List.singleton_append]
      · exact List.nodup_cons.mpr
          ⟨fun h => (hmem _ h).1 (List.mem_append_right _ (List.mem_singleton_self _)), hnd⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨hfresh, List.mem_map.mpr ⟨o, List.mem_cons_self .., rfl⟩⟩
        · refine ⟨fun h => (hmem x hx).1 (List.mem_append_left _ h), ?_⟩
          rcases List.mem_map.mp (hmem x hx).2 with ⟨o', ho', rfl⟩
          exact List.mem_map.mpr ⟨o', List.mem_cons_of_mem _ ho', rfl⟩
    · have hstep : influenceSweep [o] ks = ks := by
        rw [influenceSweep_singleton, ite_eq_right hc]
      obtain ⟨l, hl, hnd, hmem⟩ := ih ks
      refine ⟨l, by rw [hstep, hl], hnd, fun x hx => ⟨(hmem x hx).1, ?_⟩⟩
      rcases List.mem_map.mp (hmem x hx).2 with ⟨o', ho', rfl⟩
      exact List.mem_map.mpr ⟨o', List.mem_cons_of_mem _ ho', rfl⟩

private theorem influenceSweeps_shape (occs : List (Occurrence ν κ)) :
    ∀ (fuel : Nat) (ks : List ν), ∃ l, influenceSweeps occs fuel ks = ks ++ l ∧ l.Nodup ∧
      ∀ x ∈ l, x ∉ ks ∧ x ∈ occs.map (·.result)
  | 0, ks => ⟨[], by simp [influenceSweeps]⟩
  | fuel + 1, ks => by
    rw [influenceSweeps]
    by_cases h : ((influenceSweep occs ks).length == ks.length) = true
    · rw [ite_eq_left h]
      exact ⟨[], by simp⟩
    · rw [ite_eq_right h]
      obtain ⟨l₁, hl₁, hnd₁, hmem₁⟩ := influenceSweep_shape occs ks
      obtain ⟨l₂, hl₂, hnd₂, hmem₂⟩ := influenceSweeps_shape occs fuel (influenceSweep occs ks)
      refine ⟨l₁ ++ l₂, ?_, ?_, ?_⟩
      · rw [hl₂, hl₁, List.append_assoc]
      · refine List.nodup_append.mpr ⟨hnd₁, hnd₂, fun a ha b hb hab => ?_⟩
        exact (hmem₂ b hb).1 (hl₁ ▸ List.mem_append_right _ (hab ▸ ha))
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hmem₁ x hx
        · exact ⟨fun h => (hmem₂ x hx).1 (hl₁ ▸ List.mem_append_left _ h), (hmem₂ x hx).2⟩

/-! ### Saturation: the chosen fuel observes a fixpoint -/

private theorem influenceSweeps_fix_or_grow (occs : List (Occurrence ν κ)) :
    ∀ (fuel : Nat) (ks : List ν),
      influenceSweep occs (influenceSweeps occs fuel ks) = influenceSweeps occs fuel ks ∨
        ks.length + fuel ≤ (influenceSweeps occs fuel ks).length
  | 0, ks => Or.inr (by simp [influenceSweeps])
  | fuel + 1, ks => by
    rw [influenceSweeps]
    by_cases h : ((influenceSweep occs ks).length == ks.length) = true
    · rw [ite_eq_left h]
      left
      obtain ⟨l, hl, -, -⟩ := influenceSweep_shape occs ks
      have heq : (influenceSweep occs ks).length = ks.length := by simpa using h
      have hlen : l.length = 0 := by
        rw [hl, List.length_append] at heq
        omega
      rw [hl, List.length_eq_zero_iff.mp hlen, List.append_nil]
    · rw [ite_eq_right h]
      rcases influenceSweeps_fix_or_grow occs fuel (influenceSweep occs ks) with hfix | hgrow
      · exact Or.inl hfix
      · right
        obtain ⟨l, hl, -, -⟩ := influenceSweep_shape occs ks
        have hne : l.length ≠ 0 := fun h0 =>
          h (by simp [hl, List.length_eq_zero_iff.mp h0])
        have hlen : (influenceSweep occs ks).length = ks.length + l.length := by
          rw [hl, List.length_append]
        omega

private theorem influenceSweeps_saturated (occs : List (Occurrence ν κ)) (ks : List ν) :
    influenceSweep occs (influenceSweeps occs (occs.length + 1) ks) =
      influenceSweeps occs (occs.length + 1) ks := by
  rcases influenceSweeps_fix_or_grow occs (occs.length + 1) ks with hfix | hgrow
  · exact hfix
  · exfalso
    obtain ⟨l, hl, hnd, hmem⟩ := influenceSweeps_shape occs (occs.length + 1) ks
    have hle : l.length ≤ occs.length := by
      have hsub : l ⊆ occs.map (·.result) := fun x hx => (hmem x hx).2
      simpa using (hnd.subperm hsub).length_le
    rw [hl, List.length_append] at hgrow
    omega

/-! ### The closure is closed under hops, and everything in it is reached by hops -/

private theorem influenceSweep_mem (occs : List (Occurrence ν κ)) :
    ∀ ks : List ν, (∀ x ∈ ks, x ∈ influenceSweep occs ks) ∧
      ∀ o ∈ occs, (∃ oc ∈ o.operands, oc.1 ∈ ks) → o.result ∈ influenceSweep occs ks := by
  induction occs with
  | nil => exact fun ks => ⟨fun x hx => by simpa [influenceSweep] using hx, by simp⟩
  | cons o' rest ih =>
    intro ks
    have hstep : ∀ x ∈ ks, x ∈ influenceSweep [o'] ks := by
      intro x hx
      rw [influenceSweep_singleton]
      split
      · exact List.mem_append_left _ hx
      · exact hx
    constructor
    · intro x hx
      rw [influenceSweep_cons]
      exact (ih (influenceSweep [o'] ks)).1 x (hstep x hx)
    · intro o ho hop
      rw [influenceSweep_cons]
      rcases List.mem_cons.mp ho with rfl | ho
      · have hres : o.result ∈ influenceSweep [o] ks := by
          rw [influenceSweep_singleton]
          obtain ⟨oc, hoc, hmem⟩ := hop
          have hany : o.operands.any (fun oc => ks.contains oc.1) = true :=
            List.any_eq_true.mpr ⟨oc, hoc, List.contains_iff_mem.mpr hmem⟩
          by_cases hr : ks.contains o.result = true
          · have : o.result ∈ ks := List.contains_iff_mem.mp hr
            split
            · exact List.mem_append_left _ this
            · exact this
          · have hf : ks.contains o.result = false := by
              revert hr; cases ks.contains o.result <;> simp
            rw [ite_eq_left (by rw [hany, hf]; rfl)]
            exact List.mem_append_right _ (List.mem_singleton_self _)
        exact (ih (influenceSweep [o] ks)).1 _ hres
      · obtain ⟨oc, hoc, hmem⟩ := hop
        exact (ih (influenceSweep [o'] ks)).2 o ho ⟨oc, hoc, hstep _ hmem⟩

private theorem influenceSweep_sound (occs : List (Occurrence ν κ)) {P : ν → Prop}
    (hstep : ∀ o ∈ occs, (∃ oc ∈ o.operands, P oc.1) → P o.result) :
    ∀ ks : List ν, (∀ x ∈ ks, P x) → ∀ x ∈ influenceSweep occs ks, P x := by
  induction occs with
  | nil => intro ks hks x hx; exact hks x (by simpa [influenceSweep] using hx)
  | cons o rest ih =>
    intro ks hks x hx
    rw [influenceSweep_cons] at hx
    refine ih (fun o' ho' => hstep o' (List.mem_cons_of_mem _ ho')) _ ?_ x hx
    intro y hy
    rw [influenceSweep_singleton] at hy
    by_cases hc : (o.operands.any (fun oc => ks.contains oc.1) && !ks.contains o.result) = true
    · rw [ite_eq_left hc] at hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hks y hy
      · obtain rfl := List.mem_singleton.mp hy
        obtain ⟨oc, hoc, hmem⟩ := List.any_eq_true.mp (Bool.and_eq_true .. ▸ hc).1
        exact hstep o (List.mem_cons_self ..) ⟨oc, hoc, hks _ (List.contains_iff_mem.mp hmem)⟩
    · rw [ite_eq_right hc] at hy
      exact hks y hy

private theorem influenceSweeps_sound (occs : List (Occurrence ν κ)) {P : ν → Prop}
    (hstep : ∀ o ∈ occs, (∃ oc ∈ o.operands, P oc.1) → P o.result) :
    ∀ (fuel : Nat) (ks : List ν), (∀ x ∈ ks, P x) →
      ∀ x ∈ influenceSweeps occs fuel ks, P x
  | 0, ks, hks => fun x hx => hks x (by simpa [influenceSweeps] using hx)
  | fuel + 1, ks, hks => by
    rw [influenceSweeps]
    split
    · exact hks
    · exact influenceSweeps_sound occs hstep fuel _
        (influenceSweep_sound occs hstep ks hks)

/-! ### The saturated closure is exactly reflexive-transitive reachability -/

private theorem mem_influenceSweeps_iff (occs : List (Occurrence ν κ)) (start : List ν)
    (b : ν) :
    b ∈ influenceSweeps occs (occs.length + 1) start ↔
      ∃ a ∈ start, Relation.ReflTransGen (stepRel occs) a b := by
  constructor
  · have hstep : ∀ o ∈ occs,
        (∃ oc ∈ o.operands, ∃ a ∈ start, Relation.ReflTransGen (stepRel occs) a oc.1) →
          ∃ a ∈ start, Relation.ReflTransGen (stepRel occs) a o.result := by
      rintro o ho ⟨oc, hoc, a, ha, hreach⟩
      exact ⟨a, ha, hreach.tail ⟨o, ho, rfl, oc, hoc, rfl⟩⟩
    exact fun hb => influenceSweeps_sound
      (P := fun x => ∃ a ∈ start, Relation.ReflTransGen (stepRel occs) a x)
      occs hstep (occs.length + 1) start (fun x hx => ⟨x, hx, .refl⟩) b hb
  · rintro ⟨a, ha, hreach⟩
    induction hreach with
    | refl =>
      obtain ⟨l, hl, -, -⟩ := influenceSweeps_shape occs (occs.length + 1) start
      exact hl ▸ List.mem_append_left _ ha
    | tail _ hstep ih =>
      obtain ⟨o, ho, rfl, oc, hoc, rfl⟩ := hstep
      have := (influenceSweep_mem occs (influenceSweeps occs (occs.length + 1) start)).2
        o ho ⟨oc, hoc, ih⟩
      rwa [influenceSweeps_saturated] at this

theorem mem_influencedFrom_iff {g : Provenance ν κ} {start : List ν} {b : ν} :
    b ∈ g.influencedFrom start ↔ ∃ a ∈ start, (g.flowDigraph).Reachable a b := by
  rw [influencedFrom, mem_influenceSweeps_iff]
  simp only [Digraph.reachable_iff_reflTransGen]
  exact Iff.rfl

omit [BEq ν] [LawfulBEq ν] in
/-- Reversing the incidence swaps the hop relation. -/
private theorem stepRel_reverseOccurrences {g : Provenance ν κ} {a b : ν} :
    stepRel g.reverseOccurrences a b ↔ stepRel g.occurrences b a := by
  simp only [stepRel, reverseOccurrences, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨o', ⟨o, ho, oc, hoc, rfl⟩, hres, oc', hoc', hop⟩
    obtain rfl := List.mem_singleton.mp hoc'
    exact ⟨o, ho, hop, oc, hoc, hres⟩
  · rintro ⟨o, ho, hres, oc, hoc, hop⟩
    exact ⟨_, ⟨o, ho, oc, hoc, rfl⟩, hop, (o.result, o.resultKind),
      List.mem_singleton_self _, hres⟩

theorem mem_ancestorsOf_iff {g : Provenance ν κ} {of : List ν} {a : ν} :
    a ∈ g.ancestorsOf of ↔ ∃ b ∈ of, (g.flowDigraph).Reachable a b := by
  rw [ancestorsOf, mem_influenceSweeps_iff]
  have hswap : stepRel g.reverseOccurrences = Function.swap (stepRel g.occurrences) :=
    funext fun _ => funext fun _ => propext stepRel_reverseOccurrences
  rw [hswap]
  simp only [Digraph.reachable_iff_reflTransGen]
  constructor
  · rintro ⟨b, hb, hreach⟩
    exact ⟨b, hb, Relation.reflTransGen_swap.mp hreach⟩
  · rintro ⟨b, hb, hreach⟩
    exact ⟨b, hb, Relation.reflTransGen_swap.mpr hreach⟩

/-! ### The query readings, licensed -/

theorem mayInfluence_iff {g : Provenance ν κ} {a b : ν} :
    g.mayInfluence a b = true ↔ (g.flowDigraph).Reachable a b := by
  rw [mayInfluence, List.contains_iff_mem, mem_influencedFrom_iff]
  simp

/-- The sound direction of sensitivity scoping: a `false` from the executable probe is a
theorem that no path carries the input to the output, so a perturbation study that
excludes it drops no real influence. -/
theorem not_reachable_of_mayInfluence_eq_false {g : Provenance ν κ} {a b : ν}
    (h : g.mayInfluence a b = false) : ¬(g.flowDigraph).Reachable a b := by
  rw [← mayInfluence_iff]
  simp [h]

theorem mem_successors_iff {g : Provenance ν κ} {a b : ν} :
    b ∈ g.successors a ↔ (g.flowDigraph).Adj a b := by
  simp only [successors, List.mem_map, List.mem_filter, flowDigraph_adj, stepRel,
    List.any_eq_true]
  constructor
  · rintro ⟨o, ⟨ho, oc, hoc, hbeq⟩, rfl⟩
    exact ⟨o, ho, rfl, oc, hoc, by simpa using hbeq⟩
  · rintro ⟨o, ho, rfl, oc, hoc, rfl⟩
    exact ⟨o, ⟨ho, oc, hoc, by simp⟩, rfl⟩

/-- The executable acyclicity check decides acyclicity of the value flow — the
hypothesis under which topological sorts, reachability partial orders, and condensations
apply to a provenance graph. -/
theorem acyclic_iff_isAcyclic {g : Provenance ν κ} :
    g.Acyclic ↔ (g.flowDigraph).IsAcyclic := by
  constructor
  · intro h a hcycle
    obtain ⟨c, hac, hca⟩ := Relation.TransGen.tail'_iff.mp hcycle
    obtain ⟨o, ho, rfl, -⟩ := hca
    obtain ⟨b, hab, hba⟩ := Relation.TransGen.head'_iff.mp hcycle
    have hmem : o.result ∈ g.influencedFrom (g.successors o.result) :=
      mem_influencedFrom_iff.mpr
        ⟨b, mem_successors_iff.mpr hab, Digraph.reachable_iff_reflTransGen.mpr hba⟩
    have := List.all_eq_true.mp h o ho
    simp [hmem] at this
  · intro h
    refine List.all_eq_true.mpr fun o ho => ?_
    by_cases hmem : o.result ∈ g.influencedFrom (g.successors o.result)
    · obtain ⟨b, hb, hreach⟩ := mem_influencedFrom_iff.mp hmem
      exact absurd
        (Relation.TransGen.head' (mem_successors_iff.mp hb)
          (Digraph.reachable_iff_reflTransGen.mp hreach))
        (h o.result)
    · simp [hmem]

/-- Under acyclicity, influence is a partial order on the nodes: the value-flow
hierarchy. -/
theorem Acyclic.isPartialOrder {g : Provenance ν κ} (h : g.Acyclic) :
    IsPartialOrder ν (g.flowDigraph).Reachable :=
  (acyclic_iff_isAcyclic.mp h).isPartialOrder

end Provenance

end PropertyKindCalculus
