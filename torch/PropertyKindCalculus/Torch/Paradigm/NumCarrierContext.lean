/-
`PropertyKindCalculus.Torch.Paradigm.NumCarrierContext` — the TorchLean coupling of the
branchless `NumCarrier` capability.

The core `NumCarrier` (`PropertyKindCalculus.Paradigm.NumCarrier`) extends PKC's `MathCarrier`,
which is — by construction — field-identical to TorchLean's `MathFunctions`. This module
supplies the two forwarding instances that connect TorchLean's numeric carriers to that core
class:

  * `instMathCarrierOfMathFunctions` — every `[MathFunctions α]` carrier is a `MathCarrier α`,
    forwarding each transcendental field to its `MathFunctions` twin. This is the former
    `algorithm.carrier_bridge`, now keyed on `MathFunctions` rather than `NumCarrier`: with
    `NumCarrier` extending `MathCarrier`, the `[NumCarrier α] ⇒ MathCarrier α` direction is a
    free parent projection, so the only forwarding still needed is *into* a `MathCarrier`.
  * `instNumCarrierOfContext` — every `[Context α]` is a `NumCarrier α`. `NumCarrier` bundles a
    strict subset of `Context`'s operations (everything except the ordering decision
    procedure), so each parent is inherited verbatim — the `MathCarrier` parent via the bridge
    above. This makes `ℝ`, binary32, and `Float` `NumCarrier`s with no new instance work.

Both are `scoped`. The concrete carriers (`ℝ`, `Float`, `FP32`, `IEEE32Exec`) keep their *own*
`MathCarrier` instances (`instMathCarrierFloat`, …), which agree with these on every operation
but are syntactically distinct; scoping keeps the two from overlapping in global instance
resolution. A module writing a `[NumCarrier α]`-generic kernel — or instantiating one at a
`Context` carrier — opts in with `open scoped PropertyKindCalculus.Paradigm`, and nothing else
is perturbed. (The carriers defined in this library — `TapeBuilder`, `CudaT` — are *not*
`Context`s, so their own `NumCarrier` instances do not collide with `instNumCarrierOfContext`.)

A `module` file: imports the core `NumCarrier` and TorchLean's `Context`.
-/

module

public import PropertyKindCalculus.Paradigm.NumCarrier
public import NN.Spec.Core.Context
-- `Context ℝ` lives in its own module upstream (it needs `MathFunctions ℝ`); it is imported here
-- so every consumer of this bridge sees `NumCarrier ℝ`, which the real-number floors of the
-- correctness proofs downstream instantiate.
public import NN.Spec.Core.Context.Real

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Paradigm

/-- **The transcendental bridge.** Every `MathFunctions α` (TorchLean) supplies a `MathCarrier α`
(PKC) by forwarding each field to its `MathFunctions` twin — the surfaces are identical by
construction, so the forward is definitional and `Quantity.sqrt`/`exp` over the carrier erase to
the bare `MathFunctions` op (`rfl`). Given **low priority** so a carrier's *own* `MathCarrier`
instance (`instMathCarrierFloat`, `instMathCarrierReal`, …) wins by default — the bridge only
fires for carriers without one (`TapeBuilder`, `CudaT`, abstract `Context` carriers), which
avoids any `MathCarrier` diamond while staying globally available. -/
instance (priority := low) instMathCarrierOfMathFunctions {α : Type} [MathFunctions α] :
    MathCarrier α where
  exp := MathFunctions.exp
  log := MathFunctions.log
  sin := MathFunctions.sin
  cos := MathFunctions.cos
  sinh := MathFunctions.sinh
  cosh := MathFunctions.cosh
  tanh := MathFunctions.tanh
  sqrt := MathFunctions.sqrt
  abs := MathFunctions.abs
  pi := MathFunctions.pi

/-- **Every `Context` is a `NumCarrier`.** `NumCarrier` bundles a strict subset of `Context`'s
operations (everything except the ordering decision procedure), so each parent is inherited —
the `MathCarrier` parent via `instMathCarrierOfMathFunctions` (or the carrier's own, when it has
one). Global: a `[Context α]` carrier is a `NumCarrier α` everywhere, no opt-in needed. -/
instance instNumCarrierOfContext {α : Type} [Context α] : NumCarrier α where
  toZero := inferInstance
  toOne := inferInstance
  toAdd := inferInstance
  toSub := inferInstance
  toMul := inferInstance
  toDiv := inferInstance
  toMin := inferInstance
  toMax := inferInstance
  toMathCarrier := inferInstance
  toCoe := ⟨fun n => (n : α)⟩

end PropertyKindCalculus.Paradigm

end -- pkc-blanket-expose
end -- pkc-blanket
