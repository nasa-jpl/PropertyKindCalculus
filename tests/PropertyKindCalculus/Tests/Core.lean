/-
# Core-tier validation probes — index

The Mathlib-free validation probes: every verifiable requirement whose discharging theorem lives
in the core spine, grouped by the requirement catalogue's `RequirementGroup`. Importing this pulls
in the whole core tier; the `Tests` library's `.andSubmodules` glob also builds each file directly,
so a probe cannot silently go unbuilt.
-/

module

public import PropertyKindCalculus.Tests.Core.Level
public import PropertyKindCalculus.Tests.Core.KindStructure
public import PropertyKindCalculus.Tests.Core.OperationGating
public import PropertyKindCalculus.Tests.Core.SoundnessBridges
public import PropertyKindCalculus.Tests.Core.Aggregation
public import PropertyKindCalculus.Tests.Core.Recarving
public import PropertyKindCalculus.Tests.Core.Representation
public import PropertyKindCalculus.Tests.Core.Classification
public import PropertyKindCalculus.Tests.Core.Complex
public import PropertyKindCalculus.Tests.Core.OperatorTable
public import PropertyKindCalculus.Tests.Core.SpecializationLift
public import PropertyKindCalculus.Tests.Core.Bounds
public import PropertyKindCalculus.Tests.Core.Axis
public import PropertyKindCalculus.Tests.Core.PartWhole
public import PropertyKindCalculus.Tests.Core.Composite
public import PropertyKindCalculus.Tests.Core.Decimal
public import PropertyKindCalculus.Tests.Core.KindEdges
public import PropertyKindCalculus.Tests.Core.KindIncidence
public import PropertyKindCalculus.Tests.Core.KindGraphD2
public import PropertyKindCalculus.Tests.Core.ModuleCard
public import PropertyKindCalculus.Tests.Core.IngestCard
public import PropertyKindCalculus.Tests.Core.KindLedger
public import PropertyKindCalculus.Tests.Core.KindRelation
public import PropertyKindCalculus.Tests.Core.KindContracts
public import PropertyKindCalculus.Tests.Core.ContractCoverage
public import PropertyKindCalculus.Tests.Core.PortNameScopes
public import PropertyKindCalculus.Tests.Core.PortReferences
public import PropertyKindCalculus.Tests.Core.CertifiedIngest
public import PropertyKindCalculus.Tests.Core.BoundaryAudit
public import PropertyKindCalculus.Tests.Core.Provenance
public import PropertyKindCalculus.Tests.Core.Influence
public import PropertyKindCalculus.Tests.Core.Index
public import PropertyKindCalculus.Tests.Core.Rubrics

@[expose] public section Blanket



end Blanket
