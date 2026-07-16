/-
# PropertyKindCalculus.Requirements

The **requirement-traceability** layer: typed, decl-indexed annotations that map
each of the blueprint's fifteen requirements (R1–R15) to the declarations that
*specify*, *prove*, *implement*, or *exemplify* it. From these annotations a
traceability matrix — *given a requirement, where is it formalized, proved, and
implemented?* — is generated at blueprint-build time, so it cannot drift from the
Lean source: a renamed declaration is a compile error, not a stale table cell.

Mirrors the design of `PropertyKindCalculus.CrossRefs`:

  * `PropertyKindCalculus.Requirements.Attributes`   — the `@[requirement …]`
    parametric attribute, its env extension, and the harvest API.
  * `PropertyKindCalculus.Requirements.Catalogue`    — the canonical identity of the
    fifteen requirements (the matrix's rows).
  * `PropertyKindCalculus.Requirements.Annotations`  — the annotations on the
    Mathlib-free core spine (R1–R12).
  * `PropertyKindCalculus.Requirements.DimensionAnnotations` /
    `PropertyKindCalculus.Requirements.UncertaintyAnnotations` — the annotations that
    reach into the PhysLib/Mathlib-backed Dimension (R1, R5, R7, R13) and
    Uncertainty (R14, R15) layers.
  * `PropertyKindCalculus.Requirements.ExampleAnnotations` — the `exemplifies`
    annotations tagging the worked, checked examples that exercise each requirement
    (the checked successors of the blueprint's old "Concrete test" column).
-/

import PropertyKindCalculus.Requirements.Attributes
import PropertyKindCalculus.Requirements.Catalogue
import PropertyKindCalculus.Requirements.Annotations
import PropertyKindCalculus.Requirements.DimensionAnnotations
import PropertyKindCalculus.Requirements.UncertaintyAnnotations
import PropertyKindCalculus.Requirements.ExampleAnnotations
