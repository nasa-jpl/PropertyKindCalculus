/-
# Dimension-tier validation probes — index

Validation probes for the verifiable requirements whose theorems live in the PhysLib/Mathlib-backed
`Dimension` layer (R1, R5, R7, R13, R17's ℝ companion, and R20's frame/variance laws). Building
this tier is what brings those theorems — previously never compiled by CI — under regression.
-/

import PropertyKindCalculus.Tests.Dimension.DimensionBridges
import PropertyKindCalculus.Tests.Dimension.AngleReform
import PropertyKindCalculus.Tests.Dimension.IsqBase
import PropertyKindCalculus.Tests.Dimension.BoundsReal
import PropertyKindCalculus.Tests.Dimension.DimensionalCoverage
import PropertyKindCalculus.Tests.Dimension.Frames
