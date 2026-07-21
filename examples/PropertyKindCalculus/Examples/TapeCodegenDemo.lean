/-
`paradigm.tape_codegen_demo` — **end-to-end megakernel codegen on the real AVS Stage-2 kernel**,
entirely inside PKC. Records the soil-moisture forward residual + its four analytic Jacobian columns
(written once over `[NumCarrier α]`, the exact op-structure of `kernel.avs_batch`) at the tape
carrier, hash-conses to the distinct-op DAG, emits the fused CUDA megakernel + C-stub twin, and
`#guard`s that the generated kernel is **bit-identical** to the source kernel at `Float` (CPU-side,
no CUDA toolchain).

The kernel is reproduced here self-contained (not imported from `soil-moisture-model`, which depends
on PKC, not the reverse) — it is the AVS residual/Jacobian verbatim, the codegen demo's fixture.
-/
import PropertyKindCalculus.Torch.Paradigm.TapeCodegen

open Spec
open Runtime.Autograd (Tape TapeM)
open PropertyKindCalculus (MathCarrier)
open PropertyKindCalculus.Paradigm (TapeBuilder NumCarrier)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)
open PropertyKindCalculus.Paradigm.TapeCodegen

namespace PropertyKindCalculus.Paradigm.TapeCodegen.Demo

/-! ### The AVS Stage-2 kernel — written once over `[NumCarrier α]` (verbatim `kernel.avs_batch`) -/

variable {α : Type} [NumCarrier α]

/-- `Nat → α` embedding (the `dielectric.core.ofN`). -/
def ofN (n : Nat) : α := (n : α)

/-- `exp(−2·b·ndvi)` — the vegetation attenuation, shared by the residual and the b/c Jacobians. -/
@[inline] def attenuation (b ndvi : α) : α :=
  MathCarrier.exp (((0 : α) - ofN 2) * b * ndvi)

/-- Residual `s0 − σ⁰` and the four Jacobian columns `∂residual/∂(a,b,c,d)`, sharing one `att` (the
Layer-2 CSE the codegen recovers automatically). Op-structure identical to `avs_batch.lavsResidual`
+ `lavsJacResidual`. -/
def resJac (a b c d ndvi r s0 : α) : α × α × α × α × α :=
  let att := attenuation b ndvi
  ( s0 - (a * ndvi + att * c * r + d)   -- residual
  , (0 : α) - ndvi                       -- ∂/∂a
  , ofN 2 * ndvi * c * r * att           -- ∂/∂b
  , (0 : α) - (att * r)                  -- ∂/∂c
  , (0 : α) - (1 : α) )                  -- ∂/∂d

/-! ### Record at the tape carrier -/

abbrev TB := TapeBuilder Shape.scalar

/-- A named input leaf (marks a kernel input pointer; placeholder value `0`). -/
def inLeaf (nm : String) : TB := ⟨TapeM.leaf (fill (0.0 : Float) Shape.scalar) (name := some nm)⟩

/-- Record `resJac`'s five outputs on one shared tape and hash-cons to the distinct-op DAG. -/
def recordResJac : Except String (Tape Float × List Nat) := do
  let a := inLeaf "a"; let b := inLeaf "b"; let c := inLeaf "c"; let d := inLeaf "d"
  let ndvi := inLeaf "ndvi"; let r := inLeaf "r"; let s0 := inLeaf "s0"
  let (res, ja, jb, jc, jd) := resJac (α := TB) a b c d ndvi r s0
  let (ids, t) ← TapeM.run Tape.empty (do
    let i0 ← res.run
    let i1 ← ja.run
    let i2 ← jb.run
    let i3 ← jc.run
    let i4 ← jd.run
    pure [i0, i1, i2, i3, i4])
  let (t', remap) := cseCompact t
  pure (t', ids.map (fun i => remap.getD i i))

/-! ### CPU-side bit-exact faithfulness (no CUDA toolchain) -/

/-- One concrete pixel of inputs. -/
def env0 : String → Float := fun nm =>
  match nm with
  | "a"    => 0.12  | "b"    => 0.34  | "c"  => 0.08 | "d" => -0.02
  | "ndvi" => 0.55  | "r"    => 0.21  | "s0" => -0.13
  | _      => 0.0

/-- The source kernel evaluated at `Float` on `env0` — the ground truth. -/
def ref0 : List Float :=
  let (res, ja, jb, jc, jd) := resJac (α := Float) 0.12 0.34 0.08 (-0.02) 0.55 0.21 (-0.13)
  [res, ja, jb, jc, jd]

/-- The generated kernel's semantics on `env0` (via `evalTape`, the C-op Float interpreter). -/
def gen0 : Except String (List Float) := do
  let (t, outIds) ← recordResJac
  let vals ← evalTape env0 t
  pure (outIds.map (fun i => vals.getD i 0.0))

/-- **Codegen faithfulness on a concrete pixel**: the generated kernel is bit-identical to the
source kernel at `Float`. -/
def demoFaithful : Bool :=
  match gen0 with
  | .error _  => false
  | .ok got   => got.length == ref0.length && (got.zip ref0).all (fun (x, y) => x == y)

#guard demoFaithful

/-! ### Report: AI number + the generated CUDA megakernel -/

def report : IO Unit := do
  match recordResJac with
  | .error e => IO.println s!"[tape_codegen] record failed: {e}"
  | .ok (t, outIds) =>
    let rep := aiReport t outIds.length
    let I := intensity rep 60
    IO.println "=== tape_codegen demo: AVS residual + 4 Jacobian columns (1 pixel / scalar) ==="
    IO.println s!"CSE'd DAG nodes : {rep.nNodes}  (inputs {rep.nInputs}, consts {rep.nConsts}, ops {rep.nOps}, outputs {rep.nOut})"
    IO.println s!"op histogram    : {rep.hist}"
    IO.println s!"weighted FLOPs  : {rep.flops}   fused bytes (in+out): {I.fusedBytes}   eager bytes (ops round-trip): {I.eagerBytes}"
    IO.println s!"AI eager (elementwise carrier; flat in iters): {I.aiEager}"
    IO.println s!"AI fused (this kernel)                       : {I.aiStep}"
    IO.println s!"AI fused (× 60-iter fit, inputs/outputs fixed): {I.aiFit}   (eager computed above, not cited)"
    IO.println s!"CPU bit-exact vs Float source : {demoFaithful}"
    IO.println "--- generated CUDA megakernel ---"
    match gen t outIds with
    | .error e => IO.println s!"[tape_codegen] codegen failed: {e}"
    | .ok cg   => IO.println (emitCuda "avs_resjac" cg)

#eval report

end PropertyKindCalculus.Paradigm.TapeCodegen.Demo
