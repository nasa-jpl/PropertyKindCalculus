/-
# Dimension-tier validation probes — index

Validation probes for the verifiable requirements whose theorems live in the PhysLib/Mathlib-backed
`Dimension` layer (R1, R5, R7, R13, R17's ℝ companion, and R20's frame/variance laws). Building
this tier is what brings those theorems — previously never compiled by CI — under regression.
-/

module

public import PropertyKindCalculus.Tests.Dimension.DimensionBridges
public import PropertyKindCalculus.Tests.Dimension.AngleReform
public import PropertyKindCalculus.Tests.Dimension.IsqBase
public import PropertyKindCalculus.Tests.Dimension.BoundsReal
public import PropertyKindCalculus.Tests.Dimension.DimensionalCoverage
public import PropertyKindCalculus.Tests.Dimension.ExaminationCoverage
public import PropertyKindCalculus.Tests.Dimension.Frames
public import PropertyKindCalculus.Tests.Dimension.AggregationLaws
public import PropertyKindCalculus.Tests.Dimension.UnitReal

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose



end -- pkc-blanket-expose
end -- pkc-blanket
