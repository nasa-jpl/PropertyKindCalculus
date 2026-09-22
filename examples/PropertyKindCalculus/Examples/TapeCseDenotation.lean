/-
`examples.tape_cse_denotation` — **`cseCompact` preserves the `evalTape` denotation node-for-node**, for
an *arbitrary* well-formed tape. This is the `evalTape`-fold wrapper the megakernel-codegen story asked
for: it turns `examples.tape_cse_structural`'s per-node *structural* correspondence into the pointwise
*value* equality the deployed kernel actually needs.

The megakernel emits — and `evalTape` (`paradigm.tape_codegen`) re-interprets — the CSE'd tape
(`paradigm.tape_cse.cseCompact`). `examples.tape_cse_structural.cseCompact_structural` proved that for
every original id, the CSE-remapped node carries the **same op name**, its **parents remapped by the
same remap**, and a **bit-identical stored value**. Here we run the interpreter on both tapes and show
their value arrays agree pointwise under the remap:

  **for a well-formed tape `t`, if `evalTape env t = .ok vals` and `evalTape env (cseCompact t).1 =
  .ok valsC`, then `valsC.getD (remap id) 0 = vals.getD id 0` for every original id.**

The engine is `evalTape_node_value`: a `foldlM` invariant (there is no `Array.foldlM_induction` in core,
so it is proved by list induction with an offset, `foldlM_stepVal_spec`) characterising each slot of a
successful `evalTape` run as exactly what `stepVal` computes there — the local recurrence a strong
induction on `id` then consumes. At each id, `cseCompact_structural` supplies the matching remapped node
and the induction hypothesis rewrites its remapped-parent reads to the original reads.

**Where `Float.toBits` injectivity would be needed, and why it is not assumed.** `stepVal`/`cOp` reads an
op node's value only through its op name and remapped parents — so op nodes are handled with **no**
`toBits` injectivity, purely from the structural correspondence and the induction hypothesis. A **const
leaf** is the sole exception: `stepVal` reads its *stored* scalar via `nodeScalar`, and the structural
correspondence only gives equal value-*bits*, which imply equal `nodeScalar` only under `toBits`
injectivity — a fact **absent in core** (`Float.toBits` has no round-trip/injectivity lemma). So the
main theorem `cseCompact_denotation` takes that one const-leaf fact as an explicit, per-tape-checkable
hypothesis `hleaf`, isolating exactly the gap. Two consequences discharge it in practice:

* `cseCompact_denotation_of_named` — for a tape whose every leaf is *named* (a graph input), `hleaf` is
  vacuous, so the pointwise equality holds **unconditionally, with no `toBits`**;
* the `#guard cseDenotationHolds …` at the end checks the pointwise equality *computationally*, on the
  deployed AVS `resJac` tape (which does merge const leaves) at a sample environment — the empirical
  discharge the codegen relies on, mirroring `examples.tape_codegen_end_to_end`'s `cse_preserves_resJac`.

Plain leaf module (nothing imports it). Builds under the `Examples` glob, so CI checks it, and the axiom
audit at the end certifies it sorry-free.
-/

module

public import PropertyKindCalculus.Examples.TapeCseStructural
meta import PropertyKindCalculus.Examples.TapeCseStructural
public import PropertyKindCalculus.Examples.TapeCodegenEndToEnd
meta import PropertyKindCalculus.Examples.TapeCodegenEndToEnd

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open Spec TorchLean TorchLean.Tensor
open Runtime.Autograd (Tape Node)
open PropertyKindCalculus.Paradigm.TapeCodegen (evalTape nodeScalar cOp)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)
open PropertyKindCalculus.Examples.TapeCseStructural
  (WF cseCompact_structural cseCompact_wellFormed demoTape demoTape_size demoTape_wf)
open PropertyKindCalculus.Examples.TapeCodegenEndToEnd
  (stepVal evalTape_eq_foldlM getD_push_lt getD_push_size recordRaw)

namespace PropertyKindCalculus.Examples.TapeCseDenotation

/-! ## The `evalTape` value-characterisation (a `foldlM` invariant) -/

/-- Pushing a fresh value onto the value array does not change `stepVal` of a node whose parents are all
already in range — the interpreter reads `vals.getD p 0` only at parent indices, and `getD` below the
array size is push-invariant. -/
theorem stepVal_push_stable (env : String → Float) (acc : Array Float) (v : Float) (nd : Node Float)
    (hp : ∀ p ∈ nd.parents, p < acc.size) :
    stepVal env (acc.push v) nd = stepVal env acc nd := by
  unfold stepVal
  by_cases he : nd.parents.isEmpty = true
  · simp only [he, ite_true]
  · simp only [ite_eq_right he]
    cases hn : nd.name with
    | none => rfl
    | some nm =>
      simp only
      congr 1
      exact congrArg Array.toList (Array.map_congr_left (fun p hp' => getD_push_lt acc v p (hp p hp')))

/-- **The `foldlM` invariant, over a node sublist with an id offset `s`.** If the fold over `l` (the
nodes at ids `s, s+1, …`) succeeds, then every processed id's value is exactly what `stepVal` computes
there against the final array — the local recurrence strong induction consumes. Well-formedness (parents
precede children) is what makes each slot's `stepVal` stable as later slots are appended. Proved by list
induction because core has no `Array.foldlM_induction`. -/
theorem foldlM_stepVal_spec (env : String → Float) (t : Tape Float) (hwf : WF t) :
    ∀ (l : List (Node Float)) (s : Nat) (acc out : Array Float),
      acc.size = s →
      (∀ i (hi : i < l.length), t.getNode? (s + i) = some l[i]) →
      (∀ id, id < s → ∀ nd, t.getNode? id = some nd → stepVal env acc nd = .ok (acc.getD id 0.0)) →
      List.foldlM (fun vals n => (stepVal env vals n).map (fun v => vals.push v)) acc l = .ok out →
      out.size = s + l.length ∧
      (∀ id, id < s + l.length → ∀ nd, t.getNode? id = some nd →
        stepVal env out nd = .ok (out.getD id 0.0)) := by
  intro l
  induction l with
  | nil =>
    intro s acc out hsz _ hproc hrun
    rw [List.foldlM_nil] at hrun
    have hout : out = acc := by injection hrun with h; exact h.symm
    subst hout
    exact ⟨by simpa using hsz, by simpa using hproc⟩
  | cons hd tl ih =>
    intro s acc out hsz hget hproc hrun
    rw [List.foldlM_cons] at hrun
    have hhd : t.getNode? s = some hd := by have := hget 0 (by simp); simpa using this
    have hhd_par : ∀ p ∈ hd.parents, p < s := hwf s hd hhd
    cases hsv : stepVal env acc hd with
    | error e =>
        rw [hsv] at hrun
        simp [Except.map, bind, Except.bind] at hrun
    | ok v =>
        rw [hsv] at hrun
        simp only [Except.map, bind, Except.bind] at hrun
        have hsz' : (acc.push v).size = s + 1 := by rw [Array.size_push, hsz]
        have hproc' : ∀ id, id < s + 1 → ∀ nd, t.getNode? id = some nd →
            stepVal env (acc.push v) nd = .ok ((acc.push v).getD id 0.0) := by
          intro id hid nd hnd
          rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hlt | heq
          · have hnd_par : ∀ p ∈ nd.parents, p < acc.size := by
              intro p hp; have := hwf id nd hnd p hp; omega
            rw [stepVal_push_stable env acc v nd hnd_par, hproc id hlt nd hnd,
              getD_push_lt acc v id (by rw [hsz]; exact hlt)]
          · subst heq
            have hnne : nd = hd := by
              have h2 : some nd = some hd := hnd.symm.trans hhd
              rwa [Option.some.injEq] at h2
            subst hnne
            have hnd_par : ∀ p ∈ nd.parents, p < acc.size := by
              intro p hp; rw [hsz]; exact hhd_par p hp
            rw [stepVal_push_stable env acc v nd hnd_par, hsv, ← hsz, getD_push_size]
        have hget' : ∀ i (hi : i < tl.length), t.getNode? ((s + 1) + i) = some tl[i] := by
          intro i hi
          have hlt1 : i + 1 < (hd :: tl).length := by simp only [List.length_cons]; omega
          have hidx : s + (i + 1) = (s + 1) + i := by omega
          have key := hget (i + 1) hlt1
          rw [List.getElem_cons_succ] at key
          exact hidx ▸ key
        obtain ⟨ho1, ho2⟩ := ih (s + 1) (acc.push v) out hsz' hget' hproc' hrun
        refine ⟨?_, ?_⟩
        · simp only [List.length_cons]; omega
        · intro id hid nd hnd
          simp only [List.length_cons] at hid
          exact ho2 id (by omega) nd hnd

/-- **`evalTape` node-value characterisation.** A successful `evalTape` run assigns to slot `id` exactly
the value `stepVal` computes for node `id` against the final array (specialisation of the invariant at
offset `0`). -/
theorem evalTape_node_value (env : String → Float) (t : Tape Float) (hwf : WF t)
    (vals : Array Float) (hv : evalTape env t = .ok vals) :
    vals.size = t.size ∧
    ∀ id nd, t.getNode? id = some nd → stepVal env vals nd = .ok (vals.getD id 0.0) := by
  rw [evalTape_eq_foldlM, ← Array.foldlM_toList] at hv
  have hget0 : ∀ i (hi : i < t.nodes.toList.length), t.getNode? (0 + i) = some t.nodes.toList[i] := by
    intro i hi
    rw [Nat.zero_add]
    have hi' : i < t.nodes.size := by rw [← Array.length_toList]; exact hi
    simp only [Tape.getNode?]
    rw [Array.getElem_toList hi']
    exact Array.getElem?_eq_getElem hi'
  obtain ⟨hsz, hproc⟩ := foldlM_stepVal_spec env t hwf t.nodes.toList 0 #[] vals
    (by simp) hget0 (by intro id hid; exact absurd hid (Nat.not_lt_zero id)) hv
  rw [Nat.zero_add, Array.length_toList] at hsz hproc
  refine ⟨hsz, ?_⟩
  intro id nd hnd
  have hid : id < t.nodes.size := by
    have hnd' := hnd
    rw [Tape.getNode?] at hnd'
    obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnd'
    exact hlt
  exact hproc id hid nd hnd

/-! ## The pointwise `evalTape`-denotation equality -/

/-- **`cseCompact` preserves the `evalTape` denotation node-for-node.** For a well-formed tape `t`, the
interpreter's value at every original id equals its value at the CSE-remapped id. Op nodes are settled by
the structural correspondence plus the induction hypothesis (no `Float.toBits` injectivity — the
interpreter never reads an op node's stored bits). **Const leaves** are the sole place stored bits are
read (`nodeScalar`): the one fact `hleaf` supplies — that the compacted value at a const leaf's remap
equals its stored scalar — is exactly the `toBits`-injectivity content core lacks, isolated here as an
explicit, per-tape-checkable hypothesis. -/
theorem cseCompact_denotation (t : Tape Float) (hwf : WF t) (env : String → Float)
    (vals valsC : Array Float)
    (hv : evalTape env t = .ok vals)
    (hvC : evalTape env (cseCompact t).1 = .ok valsC)
    (hleaf : ∀ id nOld, t.getNode? id = some nOld →
        nOld.parents.isEmpty = true → nOld.name = none →
        valsC.getD ((cseCompact t).2.getD id id) 0.0 = nodeScalar nOld) :
    ∀ id, id < t.size → valsC.getD ((cseCompact t).2.getD id id) 0.0 = vals.getD id 0.0 := by
  obtain ⟨_, hvals⟩ := evalTape_node_value env t hwf vals hv
  obtain ⟨_, hvalsC⟩ :=
    evalTape_node_value env (cseCompact t).1 (cseCompact_wellFormed t hwf) valsC hvC
  intro id
  induction id using Nat.strong_induction_on with
  | _ id IH =>
    intro h
    obtain ⟨hlt, nNew, nOld, hNew, hOld, hname, hpar, _hbits⟩ := cseCompact_structural t hwf id h
    have hstepOld : stepVal env vals nOld = .ok (vals.getD id 0.0) := hvals id nOld hOld
    have hstepNew : stepVal env valsC nNew = .ok (valsC.getD ((cseCompact t).2.getD id id) 0.0) :=
      hvalsC _ nNew hNew
    by_cases he : nOld.parents.isEmpty = true
    · -- leaf node
      cases hn : nOld.name with
      | none =>
        -- const leaf: the only place the interpreter reads stored bits — supplied by `hleaf`
        have hval_eq : vals.getD id 0.0 = nodeScalar nOld := by
          have hred : stepVal env vals nOld = .ok (nodeScalar nOld) := by
            unfold stepVal; rw [ite_eq_left he, hn]; rfl
          rw [hred] at hstepOld; exact (Except.ok.injEq _ _ ▸ hstepOld).symm
        rw [hval_eq]; exact hleaf id nOld hOld he hn
      | some nm =>
        -- named leaf: both interpreters read `env nm`
        -- `parents` is an `Array`, which has no nil/cons alternatives: emptiness comes
        -- straight from `he` instead of a case split on the constructor.
        have hpe : nOld.parents = #[] := by
          simpa using he
        have hNewEmpty : nNew.parents.isEmpty = true := by rw [hpar, hpe]; simp
        have hNewName : nNew.name = some nm := by rw [hname, hn]
        have e1 : vals.getD id 0.0 = env nm := by
          have hred : stepVal env vals nOld = .ok (env nm) := by
            unfold stepVal; rw [ite_eq_left he, hn]; rfl
          rw [hred] at hstepOld; exact (Except.ok.injEq _ _ ▸ hstepOld).symm
        have e2 : valsC.getD ((cseCompact t).2.getD id id) 0.0 = env nm := by
          have hred : stepVal env valsC nNew = .ok (env nm) := by
            unfold stepVal; rw [ite_eq_left hNewEmpty, hNewName]; rfl
          rw [hred] at hstepNew; exact (Except.ok.injEq _ _ ▸ hstepNew).symm
        rw [e1, e2]
    · -- op node: settled from op name + remapped parents (no stored-bit read, no `toBits`)
      have heF : nOld.parents.isEmpty = false := by
        cases hh : nOld.parents.isEmpty with
        | true => exact absurd hh he
        | false => rfl
      have hpar_lt : ∀ p ∈ nOld.parents, p < id := hwf id nOld hOld
      have hNewEmpty : nNew.parents.isEmpty = false := by
        rw [hpar]; simpa using heF
      cases hn : nOld.name with
      | none =>
        -- a nameless op node cannot occur in a successfully-evaluated tape
        exfalso
        have hred : stepVal env vals nOld = .error "tape_codegen: op node with no op name" := by
          unfold stepVal; rw [ite_eq_right (show ¬ nOld.parents.isEmpty = true by simp [heF]), hn]
        rw [hred] at hstepOld
        simp at hstepOld
      | some nm =>
        have hNewName : nNew.name = some nm := by rw [hname, hn]
        have hkey : stepVal env valsC nNew = stepVal env vals nOld := by
          unfold stepVal
          simp only [ite_eq_right (show ¬ nNew.parents.isEmpty = true by simp [hNewEmpty]),
            ite_eq_right (show ¬ nOld.parents.isEmpty = true by simp [heF]), hn, hNewName]
          congr 1
          rw [hpar, Array.map_map]
          apply congrArg Array.toList
          apply Array.map_congr_left
          intro p hp
          show valsC.getD ((cseCompact t).2.getD p p) 0.0 = vals.getD p 0.0
          exact IH p (hpar_lt p hp) (Nat.lt_trans (hpar_lt p hp) h)
        rw [hstepNew, hstepOld] at hkey
        exact (Except.ok.injEq _ _ ▸ hkey)

/-- **Unconditional corollary for named-leaf tapes — no `Float.toBits` needed.** If every leaf of `t` is
named (a graph input, never a bare `TapeBuilder.const`), the const-leaf hypothesis of
`cseCompact_denotation` is vacuous, so the pointwise `evalTape`-denotation equality holds outright. This
is the "op nodes and named leaves need no `toBits`" statement in full. -/
theorem cseCompact_denotation_of_named (t : Tape Float) (hwf : WF t) (env : String → Float)
    (vals valsC : Array Float)
    (hv : evalTape env t = .ok vals)
    (hvC : evalTape env (cseCompact t).1 = .ok valsC)
    (hnamed : ∀ id nd, t.getNode? id = some nd → nd.parents.isEmpty = true → nd.name ≠ none) :
    ∀ id, id < t.size → valsC.getD ((cseCompact t).2.getD id id) 0.0 = vals.getD id 0.0 :=
  cseCompact_denotation t hwf env vals valsC hv hvC
    (fun id nOld hOld he hnone => absurd hnone (hnamed id nOld hOld he))

/-! ## Inhabitation — the theorems are non-vacuous

`cseCompact_denotation_of_named` is hypothetical (`WF t`, all leaves named, both `evalTape` runs
succeed). A witness confirms those hypotheses are jointly satisfiable by a real tape *with an op node*,
and a computational `#guard` confirms the conclusion genuinely holds (including on the deployed AVS
kernel, whose merged const leaves exercise the path `hleaf` covers). -/

/-- Named-leaf-ness of a concrete tape reduces to a decidable bounded check (companion of
`examples.tape_cse_structural.wf_of_bounded`). -/
theorem named_of_bounded (t : Tape Float)
    (h : ∀ id (hid : id < t.size),
      (t.nodes[id]'hid).parents.isEmpty = true → (t.nodes[id]'hid).name ≠ none) :
    ∀ id nd, t.getNode? id = some nd → nd.parents.isEmpty = true → nd.name ≠ none := by
  intro id nd hnd hemp
  rw [Tape.getNode?] at hnd
  obtain ⟨hid, heq⟩ := Array.getElem?_eq_some_iff.mp hnd
  rw [← heq] at hemp ⊢
  exact h id hid hemp

/-- `demoTape` (two named input leaves `"a"`,`"b"` and one `"add"` op) has every leaf named. -/
theorem demoTape_named :
    ∀ id nd, demoTape.getNode? id = some nd → nd.parents.isEmpty = true → nd.name ≠ none :=
  named_of_bounded demoTape (by decide)

/-- The unconditional corollary applies non-vacuously: `demoTape` is a real well-formed named-leaf tape
carrying an op node, so `demoTape_wf` and `demoTape_named` are jointly constructible. -/
example (env : String → Float) (vals valsC : Array Float)
    (hv : evalTape env demoTape = .ok vals)
    (hvC : evalTape env (cseCompact demoTape).1 = .ok valsC) :
    ∀ id, id < demoTape.size →
      valsC.getD ((cseCompact demoTape).2.getD id id) 0.0 = vals.getD id 0.0 :=
  cseCompact_denotation_of_named demoTape demoTape_wf env vals valsC hv hvC demoTape_named

/-- Executable pointwise check: `evalTape` of the compacted tape agrees with `evalTape` of the original
at every original id (bit-for-bit via `Float.toBits`, so exact even at non-finite values). -/
def cseDenotationHolds (env : String → Float) (t : Tape Float) : Bool :=
  match evalTape env t, evalTape env (cseCompact t).1 with
  | .ok vals, .ok valsC =>
      let remap := (cseCompact t).2
      (List.range t.size).all (fun id =>
        (valsC.getD (remap.getD id id) 0.0).toBits == (vals.getD id 0.0).toBits)
  | _, _ => false

/-- A concrete environment for the executable checks. -/
def demoEnv : String → Float := fun s => if s = "a" then 2.0 else if s = "b" then 3.0 else 0.5

-- Non-vacuity of the conclusion on the simple named-leaf tape …
#guard cseDenotationHolds demoEnv demoTape

-- … and on the deployed AVS `resJac` tape, whose merged const leaves are the `hleaf` case discharged
-- empirically (the codegen's real guarantee, cf. `cse_preserves_resJac`).
#guard (match recordRaw with
        | .ok (t, _) => cseDenotationHolds demoEnv t
        | .error _ => false)

/-! ## Axiom audit — these rest only on the standard axioms (no `sorryAx`). -/

/-- info: 'PropertyKindCalculus.Examples.TapeCseDenotation.cseCompact_denotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cseCompact_denotation

/-- info: 'PropertyKindCalculus.Examples.TapeCseDenotation.cseCompact_denotation_of_named' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cseCompact_denotation_of_named

/-- info: 'PropertyKindCalculus.Examples.TapeCseDenotation.evalTape_node_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalTape_node_value

end PropertyKindCalculus.Examples.TapeCseDenotation

end -- pkc-blanket-expose
end -- pkc-blanket
