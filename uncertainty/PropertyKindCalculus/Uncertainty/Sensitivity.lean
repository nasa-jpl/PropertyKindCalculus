/-
`PropertyKindCalculus.Uncertainty.Sensitivity` — the autograd bridge that sources the GUM/Willink
sensitivity coefficients `cᵢ = ∂f/∂Xᵢ` from a write-once model, via TorchLean's reverse-mode tape.

`UNCERTAINTY.md` §3.2 pins autograd's role precisely: it is *not* the SSPRC engine (SSPRC is
derivative-free). Its first and primary job is the linearized methods' `extract` step — one
reverse pass over the model at the input means yields every `cᵢ` at once, which `Combine.lean`'s
`gumStdUnc`/`willinkCombine` then combine.

The mechanism is the WO1 discipline (P1): the *same* carrier-polymorphic kernel
`f {α} [NumCarrier α] (x₁ … : α) : α` — the one run at `Float` for Monte Carlo — is instantiated
here at `α := TapeBuilder .scalar` (`Torch/Paradigm/TapeCarrier.lean`), with each input presented
as a differentiable tape leaf. No model rewrite. Running the kernel *builds* a scalar tape;
`TapeM.backwardScalar` then back-propagates from the output, and each input leaf's accumulated
gradient is its sensitivity coefficient.

Op coverage (UNCERTAINTY.md §7): the tape's VJP surface is `add/sub/mul/div/min/max` and unary
`abs/sqrt/exp/log` — the exp/log/sqrt model class. A model that names `sin/cos/tanh/…` can be
*evaluated* but not differentiated on the tape (those `MathFunctions` fields error if run), until
their VJP nodes are added upstream. This bridge therefore targets that op class; the Degenhardt
fictive model `(a + b·b)·c` — pure `+`/`·` — is squarely inside it.

This is the one Stage-1 module that depends on TorchLean (it lives in the `UncertaintyRigor`
library alongside the Mathlib-backed `Ladder`, keeping Stage 0 toolchain-only).
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeCarrier
public import PropertyKindCalculus.Uncertainty.InputDist
public import NN.Tensor
public import Std.Data.HashMap

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open Spec TorchLean
open TorchLean TorchLean.Tensor
open Runtime.Autograd
open PropertyKindCalculus.Paradigm (TapeBuilder)

namespace PropertyKindCalculus.Uncertainty.Sensitivity

open PropertyKindCalculus.Uncertainty

/-- A **write-once scalar model** presented to the autograd bridge: a kernel already applied to a
positional list of carrier inputs. A genuine WO1 kernel `f {α} [NumCarrier α] (x₁ … xₙ : α) : α`
becomes a `ScalarModel` by `fun xs => f xs[0]! … xs[n-1]!` — no rewrite; the same source that runs
at `α := Float` runs here at `α := TapeBuilder .scalar`. -/
abbrev ScalarModel := List (TapeBuilder Shape.scalar) → TapeBuilder Shape.scalar

/-- **Reverse-mode gradient of a scalar model at a point.** Instantiates the write-once kernel at
the tape carrier `TapeBuilder .scalar`, creating one differentiable input leaf per coordinate of
`point`, records the forward tape, runs a single reverse pass from the scalar output, and reads
back `∂f/∂xᵢ` at `point` in input order. These are the sensitivity coefficients `cᵢ` the
linearized GUM/Willink methods consume (UNCERTAINTY.md §3.2 item 1).

**Stage 3.5 retarget.** The reverse pass is the *total dense* engine entry
`Tape.backwardDenseFrom` — the very function TorchLean's soundness theorem
`backwardDenseFrom_lowerGraphToTape_adjoint_fderiv` (`NN/Proofs/Autograd/Runtime/Link/FDeriv.lean`)
characterizes: on a compiled graph at the `ℝ` carrier, its input-prefix output is the adjoint of
the Fréchet derivative of the forward evaluation. The seed is `1` at the scalar output and `0`
everywhere else, which on a topologically-ordered tape computes the same accumulation as the
previous reachability-pruned `backwardScalar` path (a dead subexpression now contributes an exact
`0` instead of being skipped). The two honest gaps that remain are recorded in UNCERTAINTY.md
§3.2/§6: this tape is built eagerly rather than by `lowerGraphToTape` (provenance), and it runs at
`Float` while the theorem speaks at `ℝ` (the deviation is this workstream's own Adequacy claim). -/
def gradient (model : ScalarModel) (point : List Float) : Except String (List Float) := do
  let ((ids, outId), t) ← TapeM.run Tape.empty do
    let ids ← point.mapM fun x => TapeM.leaf (α := Float) (Tensor.full Shape.scalar x)
    let out : TapeBuilder Shape.scalar := model (ids.map fun i => (⟨pure i⟩ : TapeBuilder Shape.scalar))
    let outId ← out.run
    pure (ids, outId)
  if h : outId < t.nodes.size then
    let grads0 : Array (SomeTensor Float) :=
      (t.nodes.map fun node => SomeTensor.ofTensor (Tensor.full node.value.shape (0 : Float))).set outId
        (SomeTensor.ofTensor (Tensor.scalar (1 : Float))) (h := by simpa using h)
    let grads ← Tape.backwardDenseFrom (t := t) grads0
    ids.mapM fun i =>
      match grads[i]? with
      | some g => do
          let tg ← Tape.requireGrad (α := Float) (τ := Shape.scalar) g
          pure tg.item
      | none => .error s!"sensitivity: no gradient recorded for input leaf id {i}"
  else
    .error "sensitivity: output node id out of tape bounds"

/-- **Sensitivity coefficients paired with input moments** — the `(cᵢ, MomentData)` term list the
linearized `Combine` methods (`gumStdUnc`, `willinkCombine`) consume. Differentiates `model` at
the inputs' means (the GUM/Willink reference point `E(X)`) and zips each `cᵢ` with its input's
moment data. -/
def coefficients (model : ScalarModel) (inputs : List (InputDist Float)) :
    Except String (List (Float × MomentData Float)) := do
  let point := inputs.map fun d => d.moments.mean
  let cs ← gradient model point
  pure (cs.zip (inputs.map fun d => d.moments))

end PropertyKindCalculus.Uncertainty.Sensitivity

end -- pkc-blanket-expose
end -- pkc-blanket
