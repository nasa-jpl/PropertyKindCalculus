/-
# PropertyKindCalculus.DimensionExamples

Aggregator for the worked examples that depend on PhysLib + Mathlib: the
dimension functor, the interaction algebra, and the `ℝ` quantity carrier.

These live in a **separate library** (`DimensionExamples`, in the `examples/`
source tree) so that no *library* module carries example code — the Mathlib-free
`Examples` library separates examples from the core spine, and this library does
the same for the Mathlib-backed `Dimension` library. All `example`/`#eval`/`#guard`
checks live under `examples/`.
-/

import PropertyKindCalculus.DimensionExamples.Dimension
import PropertyKindCalculus.DimensionExamples.Interaction
import PropertyKindCalculus.DimensionExamples.QuantityReal
import PropertyKindCalculus.DimensionExamples.Frames
import PropertyKindCalculus.DimensionExamples.UnitConversion
import PropertyKindCalculus.DimensionExamples.Iso80000
