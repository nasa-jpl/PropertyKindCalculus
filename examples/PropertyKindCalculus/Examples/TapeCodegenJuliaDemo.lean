/-
`examples.tape_codegen_julia_demo` — **the AVS Stage-2 residual + Jacobian, emitted as Julia.**

The same recorded, CSE'd tape `examples.tape_codegen_demo` lowers to the CUDA megakernel is
lowered here by `paradigm.tape_codegen_julia` to a plain-Julia host kernel and its
KernelAbstractions.jl twin. Two things are checked at build, with no Julia toolchain:

  * **alphabet coverage** — on this concrete DAG, every op node that has a C rendering has a Julia
    rendering and conversely (`juliaCoversTape`), the runtime instance of the rendering-table
    theorems;
  * **the ABI is the C kernel's** — `genJulia` and `gen` agree on the input list, name for name and
    in order (`sameAbi`), so a Julia host and a CUDA host are handed the same argument list.

The *numbers* the emitted Julia computes are checked by `apps.julia_parity`, which runs the
emitted file under `julia` at `Float64` against `evalTape` — bit-exact on the IEEE-exact alphabet,
ulp-reported on the `exp`/`log` cones — because a `#guard` cannot run Julia.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeCodegenJulia
meta import PropertyKindCalculus.Torch.Paradigm.TapeCodegenJulia
public import PropertyKindCalculus.Examples.TapeCodegenDemo
meta import PropertyKindCalculus.Examples.TapeCodegenDemo

@[expose] public section Blanket

open Runtime.Autograd (Tape)
open PropertyKindCalculus.Paradigm (lutNodeName?)
open PropertyKindCalculus.Paradigm.TapeCodegen
open PropertyKindCalculus.Paradigm.TapeCodegen.Julia
open PropertyKindCalculus.Paradigm.TapeCodegen.Demo (recordResJac)

namespace PropertyKindCalculus.Paradigm.TapeCodegen.JuliaDemo

/-- On a concrete tape, the Julia rendering is defined on exactly the op nodes the C rendering is
defined on (`lutfetch` nodes are rendered by both helpers and excluded here). -/
def juliaCoversTape (t : Tape Float) : Bool :=
  t.nodes.all fun n =>
    if n.parents.isEmpty then true else
    match n.name with
    | none => true
    | some nm =>
      match lutNodeName? nm with
      | some _ => true
      | none => (jlExpr nm n.parents.toList).isOk == (cExpr nm n.parents.toList).isOk
                && (cExpr nm n.parents.toList).isOk

/-- Both lowerings of the recorded AVS tape succeed and expose the same input ABI. -/
def sameAbi : Bool :=
  match recordResJac with
  | .error _ => false
  | .ok (t, outIds) =>
    match gen t outIds, genJulia t outIds with
    | .ok c, .ok j => c.inputs == j.inputs && c.numOutputs == j.numOutputs
                      && c.body.size == j.body.size && c.outLines.size == j.outLines.size
    | _, _ => false

def coverage : Bool :=
  match recordResJac with
  | .error _ => false
  | .ok (t, _) => juliaCoversTape t

#guard coverage
#guard sameAbi

/-- The two emitted surfaces, printed. -/
def report : IO Unit := do
  match recordResJac with
  | .error e => IO.println s!"[tape_codegen_julia] record failed: {e}"
  | .ok (t, outIds) =>
    match genJulia t outIds with
    | .error e => IO.println s!"[tape_codegen_julia] codegen failed: {e}"
    | .ok cg =>
      IO.println "--- generated Julia host kernel ---"
      IO.println (emitJulia "avs_resjac" cg)
      IO.println "--- generated KernelAbstractions.jl kernel ---"
      IO.println (emitJuliaKA "avs_resjac" cg)

#eval report

end PropertyKindCalculus.Paradigm.TapeCodegen.JuliaDemo

end Blanket
