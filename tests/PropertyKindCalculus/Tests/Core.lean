/-
# Core-tier validation probes — index

The Mathlib-free validation probes: every verifiable requirement whose discharging theorem lives
in the core spine, grouped by the requirement catalogue's `RequirementGroup`. Importing this pulls
in the whole core tier; the `Tests` library's `.andSubmodules` glob also builds each file directly,
so a probe cannot silently go unbuilt.
-/

import PropertyKindCalculus.Tests.Core.KindStructure
import PropertyKindCalculus.Tests.Core.OperationGating
import PropertyKindCalculus.Tests.Core.SoundnessBridges
import PropertyKindCalculus.Tests.Core.Aggregation
import PropertyKindCalculus.Tests.Core.Representation
import PropertyKindCalculus.Tests.Core.Classification
import PropertyKindCalculus.Tests.Core.OperatorTable
import PropertyKindCalculus.Tests.Core.Bounds
