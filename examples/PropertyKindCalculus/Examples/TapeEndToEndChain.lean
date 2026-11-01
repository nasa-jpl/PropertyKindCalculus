/-
`examples.tape_end_to_end_chain` — **the chain, composed**: from the tape a `[NumCarrier α]` kernel
records, through the compaction pass, to the program every backend prints — one theorem.

The pieces existed separately: `evalTape` re-evaluates the recorded tape at any inputs
(`paradigm.tape_eval`); `cseCompact_denotation_of_named` (`examples.tape_cse_denotation`) says the
compacted tape has the same value at every original node, read through the remap; `SL.genSL_denotes`
(`paradigm.tape_straight_line`) says the program `genSL` reads off a tape runs as the tape. Composed:
for every well-formed tape — const leaves included, the AVS recording among them — the emitted program
of its CSE'd form, run at any environment, holds at the remapped slot of every original node exactly
the value the original tape computes there (`pipeline_denotes`). Neither the compacted tape's
evaluation nor a leaf condition is assumed: the program's existence supplies the former
(`genSL_denotes_noTables`), `cseCompact_denotation_unconditional` the latter.

The computational companion (`#guard chainHolds`) runs the chain from the *raw* AVS recording
(`recordRaw`, before any compaction): `checkWF` accepts it, `genSL` succeeds on its CSE'd form, and
`SL.run` of the program agrees bit for bit with `evalTape` of the raw tape at the remapped slot of
*every* original node — the theorem's conclusion, exercised through the remap. Builds under the
`Examples` glob; axioms pinned.
-/

module

public import PropertyKindCalculus.Examples.TapeCseDenotation
public import PropertyKindCalculus.Torch.Paradigm.TapeStraightLine
public import PropertyKindCalculus.Torch.Paradigm.TapeCodegen
meta import PropertyKindCalculus.Examples.TapeCseDenotation
meta import PropertyKindCalculus.Torch.Paradigm.TapeStraightLine
meta import PropertyKindCalculus.Torch.Paradigm.TapeCodegen

@[expose] public section Blanket

open Runtime.Autograd (Tape TapeM)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)
open PropertyKindCalculus.Paradigm.TapeCodegen
open PropertyKindCalculus.Paradigm.TapeCodegen.SL (genSL run genSL_denotes_noTables)
open PropertyKindCalculus.Examples.TapeCseDenotation (cseCompact_denotation_unconditional)
open PropertyKindCalculus.Examples.TapeCodegenEndToEnd (recordRaw)

namespace PropertyKindCalculus.Examples.TapeEndToEndChain

/-- **The chain.** For any well-formed tape, if `genSL` produces a program for the CSE'd tape, then at
every environment the program's run holds, at the remapped slot of every original node, the value
`evalTape` computes for that node on the original tape. No leaf condition: merged const leaves are
covered by `cseCompact_denotation_unconditional`. The source kernel's value at `Float` is `vals.getD id`
by the per-kernel faithfulness theorems (`examples.tape_codegen_end_to_end`), so this closes
source → tape → compacted tape → program. -/
theorem pipeline_denotes (t : Tape Float) (hwf : WF t)
    {prog : SL.SLProg} (hg : genSL (cseCompact t).1 #[] = .ok prog)
    (env : String → Float) (vals : Array Float) (hv : evalTape env t = .ok vals) :
    ∀ id, id < t.size →
      (run env prog).getD ((cseCompact t).2.getD id id) 0.0 = vals.getD id 0.0 :=
  cseCompact_denotation_unconditional t hwf env vals (run env prog) hv
    (genSL_denotes_noTables env hg)

/-- The chain, run from the raw AVS recording: `checkWF` accepts the raw tape, `genSL` succeeds on its
CSE'd form, and `SL.run` of that program agrees with `evalTape` of the raw tape bit for bit at the
remapped slot of every original node (the remap is exercised, not bypassed). -/
def chainHolds (env : String → Float) : Bool :=
  match recordRaw with
  | .error _ => false
  | .ok (t, _) =>
    let (t', remap) := cseCompact t
    match checkWF t, genSL t' #[], evalTape env t with
    | .ok (), .ok prog, .ok vals =>
        (List.range t.size).all fun id =>
          ((run env prog).getD (remap.getD id id) 0.0).toBits == (vals.getD id 0.0).toBits
    | _, _, _ => false

def demoEnv : String → Float := fun s =>
  if s = "a" then 0.3 else if s = "b" then 1.2 else if s = "c" then 0.8 else if s = "d" then 0.1
  else if s = "ndvi" then 0.55 else if s = "r" then 0.7 else 0.25

#guard chainHolds demoEnv

/-- info: 'PropertyKindCalculus.Examples.TapeEndToEndChain.pipeline_denotes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pipeline_denotes

end PropertyKindCalculus.Examples.TapeEndToEndChain

end Blanket
