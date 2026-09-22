/-
`PropertyKindCalculus.Uncertainty.Carriers` — the `NumCarrier Float` instance the
Stage-0 uncertainty layer needs.

The core spine leaves `Float` a `MathCarrier` (`QuantityFunction.lean`) but stops short
of `NumCarrier`, because `NumCarrier` additionally requires `Coe Nat α` and the whole
branchless arithmetic bundle — and the only in-tree route to `NumCarrier Float` today runs
through TorchLean's `Context` bridge (`Torch.Paradigm.NumCarrierContext`), which pulls in
TorchLean. Stage 0 is deliberately Mathlib- and TorchLean-free, so we assemble the instance
locally: `Float` already supplies every parent of `NumCarrier` (`Zero One Add Sub Mul Div
Min Max` natively, `MathCarrier` from the core) — the sole gap is `Coe Nat Float`, filled by
`Float.ofNat`. With that, the empty-bundle instance closes.

This lets a **write-once** kernel over `[NumCarrier α]` (the WO1 discipline) instantiate at
`Float` for Monte Carlo evaluation, exactly as it will later instantiate at `ℝ` (proofs),
`FP32` (rounding), and `CudaT`/`TapeBuilder` (GPU/autograd). See `UNCERTAINTY.md`.
-/

module

public import PropertyKindCalculus.Paradigm.NumCarrier

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Uncertainty

open PropertyKindCalculus.Paradigm

/-- `Nat → Float` coercion — the one parent of `NumCarrier` that core `Float` lacks. -/
instance instCoeNatFloat : Coe Nat Float := ⟨Float.ofNat⟩

/-- **`Float` as a branchless numeric carrier.** All arithmetic/lattice parents are native and
`MathCarrier Float` is in the core; with `Coe Nat Float` above, the `NumCarrier` bundle closes
with no new fields. This is the executable leaf a WO1 `[NumCarrier α]` kernel runs at. -/
instance instNumCarrierFloat : NumCarrier Float := {}

end PropertyKindCalculus.Uncertainty

end -- pkc-blanket-expose
end -- pkc-blanket
