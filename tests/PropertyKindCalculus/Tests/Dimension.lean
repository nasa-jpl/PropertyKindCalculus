/-
# Dimension-tier validation probes — index

Validation probes for the verifiable requirements whose theorems live in the PhysLib/Mathlib-backed
`Dimension` layer (R1, R5, R7, R13, and R17's ℝ companion). Building this tier is what brings those
seven theorems — previously never compiled by CI — under regression.
-/

import PropertyKindCalculus.Tests.Dimension.DimensionBridges
import PropertyKindCalculus.Tests.Dimension.AngleReform
