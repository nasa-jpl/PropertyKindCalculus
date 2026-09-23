/-
# PropertyKindCalculus.DimensionExamples.Iso80000

Aggregator for the ISO/IEC 80000 worked examples, organized **by part** to mirror the
`Iso80000` library's own layout (`Iso80000/References`, `Iso80000/Part3`, …): the
series-wide references catalogue plus one module per covered part. Each further part's
examples land as a sibling `Iso80000/PartN.lean` module as its coverage is built.

These live in the Mathlib-backed `DimensionExamples` library (the quantity-kinds carry
PhysLib `Dimension`s, and the §18 / area examples use `ℝ`-valued carriers).
-/

module

public import PropertyKindCalculus.DimensionExamples.Iso80000.References
public import PropertyKindCalculus.DimensionExamples.Iso80000.Part3
public import PropertyKindCalculus.DimensionExamples.Iso80000.Part4
public import PropertyKindCalculus.DimensionExamples.Iso80000.Part5
public import PropertyKindCalculus.DimensionExamples.Iso80000.Part6
public import PropertyKindCalculus.DimensionExamples.Iso80000.Part7
public import PropertyKindCalculus.DimensionExamples.Iso80000.Part8
public import PropertyKindCalculus.DimensionExamples.Iso80000.Part9
public import PropertyKindCalculus.DimensionExamples.Iso80000.Part10
public import PropertyKindCalculus.DimensionExamples.Iso80000.Part11
public import PropertyKindCalculus.DimensionExamples.Iso80000.Part12
public import PropertyKindCalculus.DimensionExamples.Iso80000.Part13

@[expose] public section Blanket



end Blanket
