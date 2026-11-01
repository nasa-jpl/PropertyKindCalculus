/-
`paradigm.tape_seal` — **the seal of the computation**: the cone lemma for `evalTape`, and the
second capstone theorem on the tape a carrier-generic module records.

The cone lemma (`evalTape_cone`) says that re-evaluating a well-formed tape from an environment of
leaf values gives, at every node, a value that depends only on the named leaves in that node's
backward cone in the computational tape graph: two environments agreeing on those leaves give the
same value at the node. The tape-side counterpart of the pedigree reading
(`Provenance.mem_ancestorsOf_iff`).

The seal of the computation (`semantic_seal`) composes it with the kind-transporting weak
bisimulation (`Graph.Bisimulation`): for a well-formed provenance hypergraph `g` and an accepted
match `m` between `g` and the graph of a well-formed tape `t`, at every node `o` of `g` realized by
a tape vertex `r`,

  * two environments that agree on the leaves realizing the *influencers* of `o` — the sources the
    hypergraph names for it — give the same value at `r`;
  * every leaf in the cone of `r`, a named input or a baked constant, realizes an influencer of
    `o` — so every constant the computation uses at `o` is one the hypergraph lists in `o`'s
    assumption ledger;
  * every tape edge between two observable vertices realizes one hop of one occurrence of `g`, so
    the kinds transported along the relation change only where an occurrence states the change.

`semantic_seal_of_denotes` is the carrier-generic reading: any function of the environment that
denotes as the tape's value at `r` — which is what the denotation bridge (`paradigm.tape_parity`)
establishes per carrier — depends on its inputs only through the influencers of `o`. The
hypergraph's absence claims become semantic: an input the harvest says cannot reach `o` provably
does not, in the computation.

A `module` file: imports the tape evaluator and the graph library's bisimulation and seal.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeEval
public import PropertyKindCalculus.Torch.Paradigm.TapeStraightLine
public import PropertyKindCalculus.Graph.Bisimulation
public import PropertyKindCalculus.Graph.Seal

@[expose] public section Blanket

open Spec TorchLean
open Runtime.Autograd (Tape Node)
open PropertyKindCalculus.Paradigm (TapeGraph Match)
open PropertyKindCalculus.Paradigm.TapeCodegen

namespace PropertyKindCalculus.Paradigm.TapeSeal

/-- An edge of a computational tape graph, as a relation. -/
abbrev Edge (T : TapeGraph) (x y : Nat) : Prop := T.edge x y = true

/-- A path of a computational tape graph: the reflexive-transitive closure of its edges. `u`
reaches `v` exactly when `u` is in the backward cone of `v`. -/
abbrev Reaches (T : TapeGraph) : Nat → Nat → Prop := Relation.ReflTransGen (Edge T)

lemma edge_of_mem_parents (t : Tape Float) {v : Nat} {n : Node Float} (h : t.getNode? v = some n)
    {p : Nat} (hp : p ∈ n.parents) : Edge (ofTape t) p v := by
  show (ofTape t).edge p v = true
  unfold TapeGraph.edge
  rw [ofTape_parents t v n h]
  exact List.contains_iff_mem.mpr (Array.mem_def.mp hp)

lemma isLeaf_of_node (t : Tape Float) {v : Nat} {n : Node Float} (h : t.getNode? v = some n)
    (hne : n.parents.isEmpty = true) : (ofTape t).isLeaf v = true := by
  have hlt : v < t.size := by
    rw [Tape.getNode?] at h
    exact (Array.getElem?_eq_some_iff.mp h).1
  simp only [TapeGraph.isLeaf, Bool.and_eq_true, decide_eq_true_eq, ofTape_size, ofTape_parents t v n h]
  exact ⟨hlt, by simpa using hne⟩

/-! ## The cone lemma -/

/-- **Evaluation reads only the cone.** On a well-formed tape, two environments that agree on every
named leaf in the backward cone of a vertex give the same value at that vertex. -/
lemma evalTape_cone (t : Tape Float) (hwf : WF t) {env₁ env₂ : String → Float}
    {vals₁ vals₂ : Array Float} (h₁ : evalTape env₁ t = .ok vals₁)
    (h₂ : evalTape env₂ t = .ok vals₂) (v : Nat)
    (hagree : ∀ u, Reaches (ofTape t) u v → ∀ n, t.getNode? u = some n →
      n.parents.isEmpty = true → ∀ nm, n.name = some nm → env₁ nm = env₂ nm) :
    vals₁.getD v 0.0 = vals₂.getD v 0.0 := by
  obtain ⟨hsz₁, hval₁⟩ := evalTape_node_value env₁ t hwf vals₁ h₁
  obtain ⟨hsz₂, hval₂⟩ := evalTape_node_value env₂ t hwf vals₂ h₂
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    cases hn : t.getNode? v with
    | none =>
      have hge : t.size ≤ v := by
        rw [Tape.getNode?] at hn
        exact Nat.le_of_not_lt fun hlt => by simp [Array.getElem?_eq_getElem hlt] at hn
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none (by rw [hsz₁]; exact hge),
        Array.getElem?_eq_none (by rw [hsz₂]; exact hge)]
    | some n =>
      have hs₁ := hval₁ v n hn
      have hs₂ := hval₂ v n hn
      by_cases hne : n.parents.isEmpty = true
      · cases hnm : n.name with
        | none =>
          simp only [stepVal, hne, ↓reduceIte, hnm] at hs₁ hs₂
          rw [← Except.ok.inj hs₁, ← Except.ok.inj hs₂]
        | some nm =>
          simp only [stepVal, hne, ↓reduceIte, hnm] at hs₁ hs₂
          rw [← Except.ok.inj hs₁, ← Except.ok.inj hs₂]
          exact hagree v Relation.ReflTransGen.refl n hn hne nm hnm
      · cases hnm : n.name with
        | none => simp [stepVal, hne, hnm] at hs₁
        | some nm =>
          simp only [stepVal, hne, Bool.false_eq_true, ↓reduceIte, hnm] at hs₁ hs₂
          have hargs : (n.parents.map fun p => vals₁.getD p 0.0).toList
              = (n.parents.map fun p => vals₂.getD p 0.0).toList := by
            congr 1
            refine Array.map_congr_left fun p hp => ?_
            have hedge : Edge (ofTape t) p v := edge_of_mem_parents t hn hp
            exact ih p (hwf v n hn p hp) fun u hu => hagree u (hu.tail hedge)
          rw [hargs] at hs₁
          rw [hs₁] at hs₂
          exact Except.ok.inj hs₂

/-! ## The seal of the computation -/

variable {ν κ : Type} [BEq ν] [LawfulBEq ν] [BEq κ]

/-- Every leaf in the cone of a vertex realizing `o` realizes an influencer of `o`: a source in
`o`'s pedigree. The constant clause of the seal, and what the cone lemma's agreement hypothesis
is discharged from. -/
lemma influencer_of_cone_leaf {g : Provenance ν κ} (hwf : g.WellFormed) (t : Tape Float)
    {m : Match ν} (hacc : m.accepts g (ofTape t) = true) {o : ν} {r : Nat} (hr : r ∈ m.comps o)
    {u : Nat} (hu : Reaches (ofTape t) u r) (hleaf : (ofTape t).isLeaf u = true) :
    ∃ s ∈ g.influencers o, u ∈ m.comps s := by
  have hA := Match.Acc.of_accepts hacc
  obtain ⟨s, hs, hus⟩ := hA.leaf_comps hleaf
  refine ⟨s, Provenance.mem_influencers_iff.mpr ⟨hs, ?_⟩, hus⟩
  exact Provenance.mem_ancestorsOf_iff.mpr ⟨o, List.mem_singleton_self _,
    Match.reachable_of_tape_path_comps hwf hA hu hus hr⟩

/-- **The seal of the computation** (the second capstone). Let `g` be a well-formed provenance
hypergraph, `t` a well-formed tape, and `m` a match between `g` and the graph of `t` that the
matcher accepts — the kind-transporting weak bisimulation. Then at every node `o` of `g` and
every tape vertex `r` realizing it: two environments that agree on the leaves realizing the
influencers of `o` give the same value at `r`; every leaf in the cone of `r` — a named input or a
baked constant — realizes an influencer of `o`; and every tape edge between observable vertices
realizes one hop of one occurrence of `g`, with the kinds the occurrence names. -/
theorem semantic_seal {g : Provenance ν κ} (hwf : g.WellFormed) (t : Tape Float) (hwft : WF t)
    {m : Match ν} (hacc : m.accepts g (ofTape t) = true) {o : ν} {r : Nat} (hr : r ∈ m.comps o) :
    (∀ (env₁ env₂ : String → Float) (vals₁ vals₂ : Array Float),
      (∀ s ∈ g.influencers o, ∀ u ∈ m.comps s, ∀ nm, (ofTape t).name? u = some nm →
        env₁ nm = env₂ nm) →
      evalTape env₁ t = .ok vals₁ → evalTape env₂ t = .ok vals₂ →
      vals₁.getD r 0.0 = vals₂.getD r 0.0) ∧
    (∀ u, Reaches (ofTape t) u r → (ofTape t).isLeaf u = true →
      ∃ s ∈ g.influencers o, u ∈ m.comps s) ∧
    (∀ u w, (ofTape t).edge u w = true → ∀ a b, u ∈ m.comps a → w ∈ m.comps b →
      ∃ oc ∈ g.occurrences, oc.result = b ∧
        ∃ (i : Nat) (k : κ), oc.operands[i]? = some (a, k) ∧
          (g.kindOf? a == some k) = true ∧ (g.kindOf? b == some oc.resultKind) = true) := by
  have hA := Match.Acc.of_accepts hacc
  refine ⟨?_, fun u hu hleaf => influencer_of_cone_leaf hwf t hacc hr hu hleaf,
    fun u w he a b hu hw => Match.occurrence_of_edge hwf hA he hu hw⟩
  intro env₁ env₂ vals₁ vals₂ hagree h₁ h₂
  refine evalTape_cone t hwft h₁ h₂ r ?_
  intro u hu n hn hne nm hnm
  obtain ⟨s, hs, hus⟩ := influencer_of_cone_leaf hwf t hacc hr hu (isLeaf_of_node t hn hne)
  exact hagree s hs u hus nm (by rw [ofTape_name? t u n hn]; exact hnm)

/-- **The seal of the computation, stated about the emitted program.** The program `genSL` reads
off a well-formed tape has the tape's graph (`SL.ofProg_eq_ofTape`) and runs as the tape
(`SL.genSL_denotes_noTables`), so the seal holds of the program alone: with the match accepted
against the *program's* graph, at every node `o` realized by a slot `r`, two environments agreeing
on the input reads realizing `o`'s influencers give the same value at slot `r` of `SL.run`; every
leaf in `r`'s cone of the program's graph realizes an influencer of `o`; every edge of the program's
graph between observable slots realizes one hop of one occurrence, with its kinds. The tape appears
only in the hypothesis that the program came from it — what a host receives is sealed as such. -/
theorem semantic_seal_program {g : Provenance ν κ} (hwf : g.WellFormed) (t : Tape Float)
    (hwft : WF t) {prog : SL.SLProg} (hg : SL.genSL t #[] = .ok prog)
    {m : Match ν} (hacc : m.accepts g (SL.ofProg prog) = true) {o : ν} {r : Nat}
    (hr : r ∈ m.comps o) :
    (∀ (env₁ env₂ : String → Float),
      (∀ s ∈ g.influencers o, ∀ u ∈ m.comps s, ∀ nm, (SL.ofProg prog).name? u = some nm →
        env₁ nm = env₂ nm) →
      (SL.run env₁ prog).getD r 0.0 = (SL.run env₂ prog).getD r 0.0) ∧
    (∀ u, Reaches (SL.ofProg prog) u r → (SL.ofProg prog).isLeaf u = true →
      ∃ s ∈ g.influencers o, u ∈ m.comps s) ∧
    (∀ u w, (SL.ofProg prog).edge u w = true → ∀ a b, u ∈ m.comps a → w ∈ m.comps b →
      ∃ oc ∈ g.occurrences, oc.result = b ∧
        ∃ (i : Nat) (k : κ), oc.operands[i]? = some (a, k) ∧
          (g.kindOf? a == some k) = true ∧ (g.kindOf? b == some oc.resultKind) = true) := by
  have hT := SL.ofProg_eq_ofTape hg
  rw [hT] at hacc ⊢
  obtain ⟨h1, h2, h3⟩ := semantic_seal hwf t hwft hacc hr
  refine ⟨?_, h2, h3⟩
  intro env₁ env₂ hagree
  exact h1 env₁ env₂ _ _ hagree (SL.genSL_denotes_noTables env₁ hg)
    (SL.genSL_denotes_noTables env₂ hg)

/-- **The seal at every carrier.** Any function of the environment that denotes as the tape's
value at a vertex realizing `o` — what the denotation bridge establishes per carrier — depends on
its inputs only through the influencers of `o`: two environments agreeing on the leaves realizing
them give the same value. An input the hypergraph says cannot reach `o` provably does not. -/
lemma semantic_seal_of_denotes {g : Provenance ν κ} (hwf : g.WellFormed) (t : Tape Float)
    (hwft : WF t) {m : Match ν} (hacc : m.accepts g (ofTape t) = true) {o : ν} {r : Nat}
    (hr : r ∈ m.comps o) (val : (String → Float) → Float)
    (hden : ∀ env, ∃ vals, evalTape env t = .ok vals ∧ val env = vals.getD r 0.0)
    {env₁ env₂ : String → Float}
    (hagree : ∀ s ∈ g.influencers o, ∀ u ∈ m.comps s, ∀ nm, (ofTape t).name? u = some nm →
      env₁ nm = env₂ nm) :
    val env₁ = val env₂ := by
  obtain ⟨vals₁, h₁, hv₁⟩ := hden env₁
  obtain ⟨vals₂, h₂, hv₂⟩ := hden env₂
  rw [hv₁, hv₂]
  exact (semantic_seal hwf t hwft hacc hr).1 env₁ env₂ vals₁ vals₂ hagree h₁ h₂

end PropertyKindCalculus.Paradigm.TapeSeal

end Blanket
