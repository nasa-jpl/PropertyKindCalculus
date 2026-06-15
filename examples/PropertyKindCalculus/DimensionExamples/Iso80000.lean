/-
# PropertyKindCalculus.DimensionExamples.Iso80000

Aggregator for the ISO/IEC 80000 worked examples, organized **by part** to mirror the
`Iso80000` library's own layout (`Iso80000/References`, `Iso80000/Part3`, …): the
series-wide references catalogue plus one module per covered part. Each further part's
examples land as a sibling `Iso80000/PartN.lean` module as its coverage is built.

These live in the Mathlib-backed `DimensionExamples` library (the quantity-kinds carry
PhysLib `Dimension`s, and the §18 / area examples use `ℝ`-valued carriers).
-/

import PropertyKindCalculus.DimensionExamples.Iso80000.References
import PropertyKindCalculus.DimensionExamples.Iso80000.Part3
import PropertyKindCalculus.DimensionExamples.Iso80000.Part4
import PropertyKindCalculus.DimensionExamples.Iso80000.Part5
import PropertyKindCalculus.DimensionExamples.Iso80000.Part6
import PropertyKindCalculus.DimensionExamples.Iso80000.Part7
import PropertyKindCalculus.DimensionExamples.Iso80000.Part11
