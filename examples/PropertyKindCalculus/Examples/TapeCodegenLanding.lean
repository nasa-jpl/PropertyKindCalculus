/-
`examples.tape_codegen_landing` — **FFI-landing well-formedness for the megakernel backend.**

`paradigm.tape_codegen` now emits, from one `Codegen`, the full artifact set needed to *land* a
generated kernel through a Lake `extern_lib` (`buildNativeBackendLib`) slot and call it from Lean: the
device `.cu`, an `extern "C"` host launcher (`<name>_launch`), a portable `.c` stub twin behind the
same symbol, the Lean `@[extern]` binding, and a `{stem, cudaSrc, stubSrc}` spec.

Landing native code introduces exactly one *new* risk the earlier `evalTape`-denotation proofs do not
cover — not the arithmetic (that is the same `cExpr`/`cOp` alphabet, proven faithful in
`examples.tape_codegen_end_to_end`), but the **ABI**: the host launcher must forward exactly the
parameters the `__global__` kernel declares, in order, with no dropped or duplicated input pointer, or
the FFI call silently corrupts memory on the device. This module certifies that structurally:

* `landing_abi_consistent` — the launcher forwards exactly one argument per kernel parameter
  (`(launchArgList cg).length = (kernelParamList cg).length`), so the generated call is arity-correct
  by construction;
* `gen_inputs_eq` / `gen_numOutputs` — the generated ABI's input list and output arity are pure
  functions of the tape / caller (they do not depend on the fallible node walk);
* `collectInputs_nodup` — the generated input parameter list is duplicate-free, so no two kernel
  parameters collide (`in_x` declared twice) and every packed input slot maps to a distinct name.

Inhabitation (`demo_landing_wf`, `resjac_landing_wf`, and the `#guard`s) discharges these on the
concrete `demoTape` and on the actually-recorded AVS Stage-2 `resJac` tape — the kernel that lands on
the GPU — so the hypotheses are non-vacuous on a real tape with op nodes and 7 named inputs.
-/
import PropertyKindCalculus.Torch.Paradigm.TapeCodegen
import PropertyKindCalculus.Examples.TapeCodegenEndToEnd
import PropertyKindCalculus.Examples.TapeCseStructural

open Runtime.Autograd (Tape Node)
open PropertyKindCalculus.Paradigm.TapeCodegen
open PropertyKindCalculus.Examples.TapeCodegenEndToEnd (recordRaw)
open PropertyKindCalculus.Examples.TapeCseStructural (demoTape)

namespace PropertyKindCalculus.Examples.TapeCodegenLanding

/-! ### ABI arity consistency (universal) -/

theorem kernelParamList_length (cg : Codegen) :
    (kernelParamList cg).length = cg.inputs.size + 2 := by
  simp [kernelParamList]

theorem launchArgList_length (cg : Codegen) :
    (launchArgList cg).length = cg.inputs.size + 2 := by
  simp [launchArgList]

/-- The host launcher forwards exactly one argument per kernel parameter — so the generated FFI call
is arity-correct by construction (a mismatch would read past the kernel's declared parameters). -/
theorem landing_abi_consistent (cg : Codegen) :
    (launchArgList cg).length = (kernelParamList cg).length := by
  rw [launchArgList_length, kernelParamList_length]

/-! ### `gen`'s ABI fields are pure functions of the tape (universal) -/

theorem gen_inputs_eq {t : Tape Float} {outIds : List Nat} {cg : Codegen}
    (h : gen t outIds = .ok cg) : cg.inputs = collectInputs t := by
  unfold gen at h
  cases hb : genBody t with
  | error e => rw [hb] at h; simp [Except.map] at h
  | ok body => rw [hb] at h; simp [Except.map] at h; subst h; rfl

theorem gen_numOutputs {t : Tape Float} {outIds : List Nat} {cg : Codegen}
    (h : gen t outIds = .ok cg) : cg.numOutputs = outIds.length := by
  unfold gen at h
  cases hb : genBody t with
  | error e => rw [hb] at h; simp [Except.map] at h
  | ok body => rw [hb] at h; simp [Except.map] at h; subst h; rfl

/-! ### The generated input ABI is duplicate-free (universal) -/

theorem collectInputs_nodup (t : Tape Float) : (collectInputs t).toList.Nodup := by
  unfold collectInputs
  refine Array.foldl_induction (motive := fun _ (acc : Array String) => acc.toList.Nodup) ?_ ?_
  · simp
  · intro i acc hacc
    split
    · split
      · split
        · exact hacc
        · rename_i nm _ hcon
          rw [Array.toList_push, List.nodup_append]
          refine ⟨hacc, List.nodup_singleton _, ?_⟩
          intro a ha b hb
          simp only [List.mem_singleton] at hb
          subst hb
          have hnm : b ∉ acc.toList := by simpa using hcon
          exact fun heqab => hnm (heqab ▸ ha)
      · exact hacc
    · exact hacc

/-! ### Inhabitation — the well-formedness hypotheses hold on real tapes with op nodes -/

/-- On the concrete `demoTape` the codegen succeeds and its generated launcher ABI is arity-consistent
and duplicate-free (non-vacuous: `demoTape` carries an op node). -/
theorem demo_landing_wf :
    ∀ cg, gen demoTape [2] = .ok cg →
      (launchArgList cg).length = (kernelParamList cg).length ∧ cg.inputs.toList.Nodup := by
  intro cg h
  refine ⟨landing_abi_consistent cg, ?_⟩
  rw [gen_inputs_eq h]; exact collectInputs_nodup demoTape

/-- Same, on the actually-recorded AVS Stage-2 `resJac` tape (7 named inputs, 5 outputs) — the kernel
the megakernel backend lands on the GPU. -/
theorem resjac_landing_wf :
    ∀ t outIds cg, recordRaw = .ok (t, outIds) → gen t outIds = .ok cg →
      (launchArgList cg).length = (kernelParamList cg).length ∧ cg.inputs.toList.Nodup := by
  intro t outIds cg _ h
  exact ⟨landing_abi_consistent cg, by rw [gen_inputs_eq h]; exact collectInputs_nodup t⟩

/-- `sub` occurs in `s` (splitting yields ≥ 2 pieces). -/
def hasSub (s sub : String) : Bool := decide (1 < (s.splitOn sub).length)

/-- The generated `.cu` and `.c` stub both define the same launcher symbol, the ABI is arity-consistent,
and the input list is duplicate-free — all checked computationally on the deployed AVS `resJac` tape. -/
def resjacLandingHolds : Bool :=
  match recordRaw with
  | .error _ => false
  | .ok (t, outIds) =>
    match gen t outIds with
    | .error _ => false
    | .ok cg =>
      let cu   := emitCudaLanding "avs_resjac" cg
      let stub := emitStubLanding "avs_resjac" cg
      (launchArgList cg).length == (kernelParamList cg).length
        && (launchArgList cg).length == cg.inputs.size + 2
        && decide cg.inputs.toList.Nodup
        && cg.numOutputs == outIds.length
        && hasSub cu "avs_resjac_launch"
        && hasSub stub "avs_resjac_launch"
        && hasSub cu "__global__ void avs_resjac"

#guard resjacLandingHolds

/-- The demo tape lands too (a small, fully-decidable witness). -/
def demoLandingHolds : Bool :=
  match gen demoTape [2] with
  | .error _ => false
  | .ok cg =>
    (launchArgList cg).length == (kernelParamList cg).length
      && decide cg.inputs.toList.Nodup
      && hasSub (emitStubLanding "demo" cg) "demo_launch"

#guard demoLandingHolds

/-! ## Axiom audit — these rest only on the standard axioms (no `sorryAx`). -/

/-- info: 'PropertyKindCalculus.Examples.TapeCodegenLanding.landing_abi_consistent' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms landing_abi_consistent

/-- info: 'PropertyKindCalculus.Examples.TapeCodegenLanding.collectInputs_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms collectInputs_nodup

/-- info: 'PropertyKindCalculus.Examples.TapeCodegenLanding.gen_inputs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gen_inputs_eq

/-- info: 'PropertyKindCalculus.Examples.TapeCodegenLanding.resjac_landing_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resjac_landing_wf

end PropertyKindCalculus.Examples.TapeCodegenLanding
