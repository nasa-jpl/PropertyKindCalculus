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

module

public import PropertyKindCalculus.DimensionExamples.Dimension
public import PropertyKindCalculus.DimensionExamples.Interaction
public import PropertyKindCalculus.DimensionExamples.QuantityReal
public import PropertyKindCalculus.DimensionExamples.Frames
public import PropertyKindCalculus.DimensionExamples.UnitConversion
public import PropertyKindCalculus.DimensionExamples.RoverExtensivity
public import PropertyKindCalculus.DimensionExamples.Iso80000

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose



end -- pkc-blanket-expose
end -- pkc-blanket
