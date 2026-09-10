/-
# Core-tier validation probes — index

The Mathlib-free validation probes: every verifiable requirement whose discharging theorem lives
in the core spine, grouped by the requirement catalogue's `RequirementGroup`. Importing this pulls
in the whole core tier; the `Tests` library's `.andSubmodules` glob also builds each file directly,
so a probe cannot silently go unbuilt.
-/

import PropertyKindCalculus.Tests.Core.Level
import PropertyKindCalculus.Tests.Core.KindStructure
import PropertyKindCalculus.Tests.Core.OperationGating
import PropertyKindCalculus.Tests.Core.SoundnessBridges
import PropertyKindCalculus.Tests.Core.Aggregation
import PropertyKindCalculus.Tests.Core.Recarving
import PropertyKindCalculus.Tests.Core.Representation
import PropertyKindCalculus.Tests.Core.Classification
import PropertyKindCalculus.Tests.Core.Complex
import PropertyKindCalculus.Tests.Core.OperatorTable
import PropertyKindCalculus.Tests.Core.SpecializationLift
import PropertyKindCalculus.Tests.Core.Bounds
import PropertyKindCalculus.Tests.Core.Axis
import PropertyKindCalculus.Tests.Core.PartWhole
import PropertyKindCalculus.Tests.Core.Composite
import PropertyKindCalculus.Tests.Core.Decimal
import PropertyKindCalculus.Tests.Core.KindEdges
import PropertyKindCalculus.Tests.Core.KindIncidence
import PropertyKindCalculus.Tests.Core.KindGraphD2
import PropertyKindCalculus.Tests.Core.ModuleCard
import PropertyKindCalculus.Tests.Core.IngestCard
import PropertyKindCalculus.Tests.Core.KindLedger
import PropertyKindCalculus.Tests.Core.KindRelation
import PropertyKindCalculus.Tests.Core.KindContracts
import PropertyKindCalculus.Tests.Core.ContractCoverage
import PropertyKindCalculus.Tests.Core.PortNameScopes
import PropertyKindCalculus.Tests.Core.PortReferences
import PropertyKindCalculus.Tests.Core.CertifiedIngest
import PropertyKindCalculus.Tests.Core.BoundaryAudit
import PropertyKindCalculus.Tests.Core.Provenance
import PropertyKindCalculus.Tests.Core.Influence
import PropertyKindCalculus.Tests.Core.Index
import PropertyKindCalculus.Tests.Core.Rubrics
