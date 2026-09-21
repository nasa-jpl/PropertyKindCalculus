/-
`examples.lm_step_codegen_demo` — **the whole trust-region step through the megakernel backend**,
not just the residual/Jacobian fragment of `examples.tape_codegen_demo`.

One projected Levenberg–Marquardt iteration (`lmStepLavs`) is far more than an elementwise map: it
*folds* the residual + four Jacobian columns over all `K` observation rows into the 4×4 normal
equations (`JᵀJ`, `Jᵀr`) — a **reduction** — Marquardt-damps the diagonal, solves the 4×4 SPD system
by unrolled Cholesky (`solveSPD4`, the `sqrt`/`div` tail), updates θ, and box-clips (`min`/`max`).
This module reproduces that step verbatim over `[NumCarrier α]` (the exact op-structure of
`soil-moisture-model`'s `kernel.fit_tile` + `kernel.spd_solve` + `kernel.avs_batch`, reproduced
self-contained because SMM depends on PKC, not the reverse), records ONE step at the tape carrier,
hash-conses to the distinct-op DAG, emits the fused CUDA megakernel, and `#guard`s it **bit-identical**
to the `Float` source (CPU-side, no CUDA toolchain). It is the artifact that produces the *honest*
whole-step op-count and arithmetic intensity — the earlier demo's numbers came from a 28-node
*fragment* and undercount both the `O(K)` normal-equations reduction and the fixed Cholesky tail.

WHY ONE STEP, NOT THE WHOLE FIT. The thunk carrier re-emits shared sub-expressions, so recording all
`iters` iterations (each referencing the previous θ) blows up exponentially. Record ONE step's DAG;
the megakernel wraps it in a fixed device-side λ-schedule loop that keeps θ in registers across
iterations — the whole-fit-in-registers, compute-bound win.

LOOP CONSTANTS. The step's arbitrary-`Float` loop constants (the `λ` value and the box bounds
`lb`/`ub`) cannot be expressed by `NumCarrier` alone, which offers only `0`/`1`/`Nat` literals; they
enter the tape as baked constant leaves via `BatchCarrier.const (C := TapeBuilder)`
(`paradigm.tape_batch_carrier`) — the app-level constant-lifting instantiated at the recording
carrier, which delegates to `TapeBuilder.const` (an unnamed `fill`-leaf). Recording the step is thus
the same app code a `[BatchCarrier C]` deployment runs, only at `C := TapeBuilder`.
-/
import PropertyKindCalculus.Torch.Paradigm.TapeCodegen
import PropertyKindCalculus.Torch.Paradigm.TapeBatchCarrier
import PropertyKindCalculus.Examples.AvsForward

open Spec TorchLean
open Runtime.Autograd (Tape TapeM)
open PropertyKindCalculus (MathCarrier)
open PropertyKindCalculus.Paradigm (TapeBuilder NumCarrier BatchCarrier)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)
open PropertyKindCalculus.Paradigm.TapeCodegen
open PropertyKindCalculus.Examples.AvsForward (lavsResidual lavsJacResidual)

namespace PropertyKindCalculus.Examples.LmStepCodegenDemo

-- Several Jacobian columns don't depend on every parameter, so the reproduced kernel leaves some
-- binders unused — that is the AVS structure, not a defect.
set_option linter.unusedVariables false

variable {α : Type} [NumCarrier α]

/-! ### The AVS Stage-2 residual + Jacobian

The AVS forward physics is authored once, **kinded**, in `examples.avs_forward`
(`PropertyKindCalculus.Examples.AvsForward`); this demo folds its `.magnitude` emission boundary
(`lavsResidual`/`lavsJacResidual`) into the normal equations below, so the recorded tape is
byte-identical to the bare kernel while the model stays in the rigorous quantity discipline. -/

/-! ### The 4×4 SPD Cholesky solve (verbatim `kernel.spd_solve`) -/

structure Sym4 (α : Type) where
  a00 : α
  a10 : α
  a11 : α
  a20 : α
  a21 : α
  a22 : α
  a30 : α
  a31 : α
  a32 : α
  a33 : α

structure Vec4 (α : Type) where
  x0 : α
  x1 : α
  x2 : α
  x3 : α

structure Lower4 (α : Type) where
  l00 : α
  l10 : α
  l11 : α
  l20 : α
  l21 : α
  l22 : α
  l30 : α
  l31 : α
  l32 : α
  l33 : α

/-- Cholesky factorisation `A = L·Lᵀ`, unrolled — a finite `+ − × ÷ √` chain, no branch. -/
def cholesky4 (A : Sym4 α) : Lower4 α :=
  let l00 := MathCarrier.sqrt A.a00
  let l10 := A.a10 / l00
  let l20 := A.a20 / l00
  let l30 := A.a30 / l00
  let l11 := MathCarrier.sqrt (A.a11 - l10 * l10)
  let l21 := (A.a21 - l20 * l10) / l11
  let l31 := (A.a31 - l30 * l10) / l11
  let l22 := MathCarrier.sqrt (A.a22 - l20 * l20 - l21 * l21)
  let l32 := (A.a32 - l30 * l20 - l31 * l21) / l22
  let l33 := MathCarrier.sqrt (A.a33 - l30 * l30 - l31 * l31 - l32 * l32)
  { l00, l10, l11, l20, l21, l22, l30, l31, l32, l33 }

/-- Forward substitution `L·y = b`. -/
def forwardSubst (L : Lower4 α) (b : Vec4 α) : Vec4 α :=
  let y0 := b.x0 / L.l00
  let y1 := (b.x1 - L.l10 * y0) / L.l11
  let y2 := (b.x2 - L.l20 * y0 - L.l21 * y1) / L.l22
  let y3 := (b.x3 - L.l30 * y0 - L.l31 * y1 - L.l32 * y2) / L.l33
  { x0 := y0, x1 := y1, x2 := y2, x3 := y3 }

/-- Back substitution `Lᵀ·x = y`. -/
def backSubst (L : Lower4 α) (y : Vec4 α) : Vec4 α :=
  let x3 := y.x3 / L.l33
  let x2 := (y.x2 - L.l32 * x3) / L.l22
  let x1 := (y.x1 - L.l21 * x2 - L.l31 * x3) / L.l11
  let x0 := (y.x0 - L.l10 * x1 - L.l20 * x2 - L.l30 * x3) / L.l00
  { x0, x1, x2, x3 }

/-- The 4×4 SPD solve `A·x = b`: Cholesky once, then forward then back substitution. -/
def solveSPD4 (A : Sym4 α) (b : Vec4 α) : Vec4 α :=
  let L := cholesky4 A
  backSubst L (forwardSubst L b)

/-! ### The projected-LM step (verbatim `kernel.fit_tile`) -/

structure Theta (α : Type) where
  a : α
  b : α
  c : α
  d : α

structure Obs (α : Type) where
  ndvi : α
  r : α
  s0 : α

structure Normal (α : Type) where
  JtJ : Sym4 α
  g   : Vec4 α
  sse : α

/-- Reduce the `K` observations into the normal equations at `θ`: accumulate the rank-1 updates
`Jₖ Jₖᵀ` into the ten distinct entries of `JtJ`, `Jₖ rₖ` into `g`, and `rₖ²` into `sse`. -/
def normalEqsLavs (θ : Theta α) (obs : List (Obs α)) : Normal α :=
  obs.foldl
    (fun N o =>
      let r := lavsResidual θ.a θ.b θ.c θ.d o.ndvi o.r o.s0
      let (ja, jb, jc, jd) := lavsJacResidual θ.b θ.c o.ndvi o.r
      { JtJ :=
          { a00 := N.JtJ.a00 + ja * ja
          , a10 := N.JtJ.a10 + jb * ja
          , a11 := N.JtJ.a11 + jb * jb
          , a20 := N.JtJ.a20 + jc * ja
          , a21 := N.JtJ.a21 + jc * jb
          , a22 := N.JtJ.a22 + jc * jc
          , a30 := N.JtJ.a30 + jd * ja
          , a31 := N.JtJ.a31 + jd * jb
          , a32 := N.JtJ.a32 + jd * jc
          , a33 := N.JtJ.a33 + jd * jd }
      , g :=
          { x0 := N.g.x0 + ja * r
          , x1 := N.g.x1 + jb * r
          , x2 := N.g.x2 + jc * r
          , x3 := N.g.x3 + jd * r }
      , sse := N.sse + r * r })
    { JtJ := { a00 := 0, a10 := 0, a11 := 0, a20 := 0, a21 := 0
             , a22 := 0, a30 := 0, a31 := 0, a32 := 0, a33 := 0 }
    , g := { x0 := 0, x1 := 0, x2 := 0, x3 := 0 }
    , sse := 0 }

/-- Marquardt damping `JtJᵢᵢ·(1+λ)` — scale each diagonal entry by `1+λ`, off-diagonals untouched. -/
def dampDiag (lam : α) (A : Sym4 α) : Sym4 α :=
  { A with a00 := A.a00 * (1 + lam), a11 := A.a11 * (1 + lam)
         , a22 := A.a22 * (1 + lam), a33 := A.a33 * (1 + lam) }

/-- Branchless box clip `min(max x lo) hi`. -/
def clip (lo hi x : α) : α := Min.min (Max.max x lo) hi

/-- Project a parameter vector onto the box `[lb, ub]` component-wise. -/
def clipTheta (lb ub θ : Theta α) : Theta α :=
  { a := clip lb.a ub.a θ.a
  , b := clip lb.b ub.b θ.b
  , c := clip lb.c ub.c θ.c
  , d := clip lb.d ub.d θ.d }

/-- **One projected-LM iteration.** Reduce to the normal equations, Marquardt-damp the diagonal,
solve `(JtJ_damp)·δ = −g`, step `θ + δ`, and project back into the box. Branch-free end to end. -/
def lmStepLavs (lam : α) (lb ub : Theta α) (obs : List (Obs α)) (θ : Theta α) : Theta α :=
  let N := normalEqsLavs θ obs
  let A := dampDiag lam N.JtJ
  let rhs : Vec4 α :=
    { x0 := (0 : α) - N.g.x0, x1 := (0 : α) - N.g.x1
    , x2 := (0 : α) - N.g.x2, x3 := (0 : α) - N.g.x3 }
  let δ := solveSPD4 A rhs
  clipTheta lb ub
    { a := θ.a + δ.x0, b := θ.b + δ.x1, c := θ.c + δ.x2, d := θ.d + δ.x3 }

/-! ### Record one step at the tape carrier -/

abbrev TB := TapeBuilder Shape.scalar

/-- A named input leaf (a kernel input pointer; placeholder value `0`). -/
def inLeaf (nm : String) : TB := ⟨TapeM.leaf (Tensor.full Shape.scalar (0.0 : Float)) (name := some nm)⟩

/-- A baked host constant on the tape, via the `BatchCarrier (TapeBuilder)` `const` instance (an
unnamed `fill`-leaf). This is the arbitrary-`Float` constant-injection `NumCarrier` cannot express —
the `λ` schedule and box bounds enter here. -/
def kconst (x : Float) : TB := BatchCarrier.const (C := TapeBuilder) (s := Shape.scalar) x

/-- Number of observation rows folded into the normal equations (fixed for the demo; ≥ 4 so `JᵀJ`
is full-rank and the Cholesky solve stays finite). -/
def K : Nat := 5

/-- The fit's loop constants (identical `Float` values on both carriers). -/
def lamV : Float := 0.03
def lbV : Theta Float := { a := -2.0, b := 0.0, c := -2.0, d := -2.0 }
def ubV : Theta Float := { a := 2.0, b := 5.0, c := 2.0, d := 2.0 }

/-- One concrete pixel: θ₀ and `K` observation rows. The leaf *names* are the kernel's input
pointers; these values are the ground truth for the bit-exact check. -/
def inputVals : List (String × Float) :=
  [ ("a", 0.10), ("b", 0.50), ("c", 0.30), ("d", -0.05)
  , ("ndvi0", 0.20), ("r0", 0.15), ("s00", -0.10)
  , ("ndvi1", 0.40), ("r1", 0.22), ("s01", -0.14)
  , ("ndvi2", 0.55), ("r2", 0.30), ("s02", -0.20)
  , ("ndvi3", 0.70), ("r3", 0.18), ("s03", -0.12)
  , ("ndvi4", 0.85), ("r4", 0.25), ("s04", -0.18) ]

def env0 : String → Float := fun nm => (List.lookup nm inputVals).getD 0.0

/-- θ₀ / observations as named leaves (tape carrier). -/
def theta0TB : Theta TB := { a := inLeaf "a", b := inLeaf "b", c := inLeaf "c", d := inLeaf "d" }
def obsTB : List (Obs TB) :=
  (List.range K).map (fun k => { ndvi := inLeaf s!"ndvi{k}", r := inLeaf s!"r{k}", s0 := inLeaf s!"s0{k}" })
def lamTB : TB := kconst lamV
def lbTB : Theta TB := { a := kconst lbV.a, b := kconst lbV.b, c := kconst lbV.c, d := kconst lbV.d }
def ubTB : Theta TB := { a := kconst ubV.a, b := kconst ubV.b, c := kconst ubV.c, d := kconst ubV.d }

/-- Record `lmStepLavs`'s four outputs (θ') on one shared tape, then hash-cons to the distinct-op DAG. -/
def recordStep : Except String (Tape Float × List Nat) := do
  let θ' := lmStepLavs (α := TB) lamTB lbTB ubTB obsTB theta0TB
  let (ids, t) ← TapeM.run Tape.empty (do
    let i0 ← θ'.a.run
    let i1 ← θ'.b.run
    let i2 ← θ'.c.run
    let i3 ← θ'.d.run
    pure [i0, i1, i2, i3])
  let (t', remap) := cseCompact t
  pure (t', ids.map (fun i => remap.getD i i))

/-! ### CPU-side bit-exact faithfulness (no CUDA toolchain) -/

def obsF : List (Obs Float) :=
  (List.range K).map (fun k => { ndvi := env0 s!"ndvi{k}", r := env0 s!"r{k}", s0 := env0 s!"s0{k}" })
def theta0F : Theta Float := { a := env0 "a", b := env0 "b", c := env0 "c", d := env0 "d" }

/-- The source step evaluated at `Float` on `env0` — the ground-truth θ'. -/
def ref0 : List Float :=
  let θ' := lmStepLavs (α := Float) lamV lbV ubV obsF theta0F
  [θ'.a, θ'.b, θ'.c, θ'.d]

/-- The generated kernel's semantics on `env0` (via `evalTape`, the C-op `Float` interpreter). -/
def gen0 : Except String (List Float) := do
  let (t, outIds) ← recordStep
  let vals ← evalTape env0 t
  pure (outIds.map (fun i => vals.getD i 0.0))

/-- **Codegen faithfulness on a concrete pixel**: the generated whole-step kernel is bit-identical to
the `Float` source (residual + Jacobian reduction *and* the Cholesky solve). -/
def demoFaithful : Bool :=
  match gen0 with
  | .error _ => false
  | .ok got  => got.length == ref0.length && (got.zip ref0).all (fun (x, y) => x == y)

#guard demoFaithful

/-! ### Report: the real whole-step AI number + the generated CUDA megakernel -/

def report : IO Unit := do
  match recordStep with
  | .error e => IO.println s!"[lm_step_codegen] record failed: {e}"
  | .ok (t, outIds) =>
    let rep := aiReport t outIds.length
    let I := intensity rep 60
    IO.println s!"=== lm_step_codegen demo: one full projected-LM step, K={K} obs (scalar / 1 pixel) ==="
    IO.println s!"CSE'd DAG nodes : {rep.nNodes}  (inputs {rep.nInputs}, consts {rep.nConsts}, ops {rep.nOps}, outputs {rep.nOut})"
    IO.println s!"op histogram    : {rep.hist}"
    IO.println s!"weighted FLOPs  : {rep.flops}   fused bytes (in+out): {I.fusedBytes}   eager bytes (ops round-trip): {I.eagerBytes}"
    IO.println s!"AI eager (elementwise carrier; flat in iters): {I.aiEager}"
    IO.println s!"AI fused (one step)                          : {I.aiStep}"
    IO.println s!"AI fused (×60-iter fit, θ resident)          : {I.aiFit}"
    IO.println s!"roofline gap (fused ×60-fit / eager)         : {I.aiFit / I.aiEager}   (per-step: {I.aiStep / I.aiEager})"
    IO.println s!"CPU bit-exact vs Float source : {demoFaithful}"
    IO.println "--- generated CUDA megakernel ---"
    match gen t outIds with
    | .error e => IO.println s!"[lm_step_codegen] codegen failed: {e}"
    | .ok cg   => IO.println (emitCuda "avs_lmstep" cg)

#eval report

end PropertyKindCalculus.Examples.LmStepCodegenDemo
