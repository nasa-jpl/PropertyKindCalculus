/-
# PropertyKindCalculus.Torch

The TorchLean-backed instance of the R10 exec/spec refinement bridge: the concrete
IEEE-754 binary32 carriers realizing `CarrierRefinement` over `ℝ`.

  * `PropertyKindCalculus.Torch.Fp32` — the `FP32` (rounding spec) and `IEEE32Exec`
    (executable) carriers, the unconditional `CarrierRefinement FP32 ℝ`, and the
    conditional executable refinement.

This is the only PropertyKindCalculus library that depends on TorchLean.
-/

import PropertyKindCalculus.Torch.Fp32
