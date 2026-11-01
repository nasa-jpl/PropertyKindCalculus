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
public import Batteries.Data.Float.Lemmas

@[expose] public section Blanket

open Spec TorchLean TorchLean.Tensor
open Runtime.Autograd (Tape Node)
open PropertyKindCalculus.Paradigm.TapeCodegen (evalTape nodeScalar cOp stepVal WF evalTape_node_value)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)
open PropertyKindCalculus.Examples.TapeCseStructural
  (cseCompact_structural cseCompact_wellFormed demoTape demoTape_size demoTape_wf)
open PropertyKindCalculus.Examples.TapeCodegenEndToEnd (recordRaw)

namespace PropertyKindCalculus.Examples.TapeCseDenotation

/-! The `foldlM` invariant and the node-value characterisation `evalTape_node_value` are library
facts now (`paradigm.tape_eval`, opened above). -/

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

/-! ## The const-leaf fact, discharged — `hleaf` is a theorem

`Float.toBits_inj` (Batteries, proved from `Float`'s bit-vector model) is exactly the injectivity the
structural correspondence was one step short of: bit-identical stored buffers have equal heads, so the
remapped const leaf stores the same scalar `nodeScalar` reads. -/

private theorem headD_map_toBits (l : List Float) (d : Float) :
    (l.map Float.toBits).headD d.toBits = (l.headD d).toBits := by
  cases l <;> rfl

/-- The CSE-remapped node of any node carries the same name, the remapped parents, and the **same
stored scalar**. -/
theorem cseCompact_leaf_scalar (t : Tape Float) (hwf : WF t) (id : Nat) (nOld : Node Float)
    (hOld : t.getNode? id = some nOld) :
    ∃ nNew, (cseCompact t).1.getNode? ((cseCompact t).2.getD id id) = some nNew ∧
      nNew.name = nOld.name ∧
      nNew.parents = nOld.parents.map (fun p => (cseCompact t).2.getD p p) ∧
      nodeScalar nNew = nodeScalar nOld := by
  have hid : id < t.size := by
    rw [Tape.getNode?] at hOld
    exact (Array.getElem?_eq_some_iff.mp hOld).1
  obtain ⟨_, nNew, nOld', hNew, hOld', hname, hpar, hbits⟩ := cseCompact_structural t hwf id hid
  have heq : nOld' = nOld := Option.some.inj (hOld'.symm.trans hOld)
  subst heq
  refine ⟨nNew, hNew, hname, hpar, ?_⟩
  have h2 := congrArg (fun l : List UInt64 => l.headD (0.0 : Float).toBits) hbits
  simp only [headD_map_toBits] at h2
  exact Float.toBits_inj.mp h2

/-- **`cseCompact` preserves the `evalTape` denotation node-for-node, for every well-formed tape** —
const leaves included, no per-tape hypothesis: `hleaf` discharged by `cseCompact_leaf_scalar`. -/
theorem cseCompact_denotation_unconditional (t : Tape Float) (hwf : WF t) (env : String → Float)
    (vals valsC : Array Float)
    (hv : evalTape env t = .ok vals)
    (hvC : evalTape env (cseCompact t).1 = .ok valsC) :
    ∀ id, id < t.size → valsC.getD ((cseCompact t).2.getD id id) 0.0 = vals.getD id 0.0 :=
  cseCompact_denotation t hwf env vals valsC hv hvC (fun id nOld hOld he hnone => by
    obtain ⟨nNew, hNew, hname, hpar, hsc⟩ := cseCompact_leaf_scalar t hwf id nOld hOld
    have hstep := (evalTape_node_value env _ (cseCompact_wellFormed t hwf) valsC hvC).2 _ nNew hNew
    have hempty : nNew.parents.isEmpty = true := by
      rw [hpar, Array.isEmpty_iff.mp he]; simp
    have hred : stepVal env valsC nNew = .ok (nodeScalar nNew) := by
      unfold stepVal; rw [ite_eq_left hempty, hname, hnone]; rfl
    rw [hred] at hstep
    exact (Except.ok.inj hstep).symm.trans hsc)

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

/-- info: 'PropertyKindCalculus.Examples.TapeCseDenotation.cseCompact_denotation_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cseCompact_denotation_unconditional

/-- info: 'PropertyKindCalculus.Paradigm.TapeCodegen.evalTape_node_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalTape_node_value

end PropertyKindCalculus.Examples.TapeCseDenotation

end Blanket
