/-
# PropertyKindCalculus.Requirements

The **requirement-traceability** layer: typed, decl-indexed annotations that map
each of the blueprint's twenty-seven requirements (R1–R27) to the declarations that
*specify*, *prove*, *implement*, or *exemplify* it. From these annotations a
traceability matrix — *given a requirement, where is it formalized, proved, and
implemented?* — is generated at blueprint-build time, so it cannot drift from the
Lean source: a renamed declaration is a compile error, not a stale table cell.

Mirrors the design of `PropertyKindCalculus.CrossRefs`:

  * `PropertyKindCalculus.Requirements.Attributes`   — the `@[requirement …]`
    parametric attribute, its env extension, and the harvest API.
  * `PropertyKindCalculus.Requirements.Catalogue`    — the canonical identity of the
    twenty-seven requirements (the matrix's rows).
  * `PropertyKindCalculus.Requirements.Annotations`  — the annotations on the
    Mathlib-free core spine (R1–R12; R16 unit-reference faithfulness; R17 the
    exact-exponent conversion round-trip; R21–R24, minted from the ForPhysLib
    benchmark).
  * `PropertyKindCalculus.Requirements.DimensionAnnotations` /
    `PropertyKindCalculus.Requirements.UncertaintyAnnotations` — the annotations that
    reach into the PhysLib/Mathlib-backed Dimension (R1, R5, R7, R13, and R17's
    ℝ conversion round-trip) and Uncertainty (R14, R15) layers.
  * `PropertyKindCalculus.Requirements.ExampleAnnotations` — the `exemplifies`
    annotations tagging the worked, checked examples that exercise each requirement
    (the checked successors of the blueprint's old "Concrete test" column).
-/

module

public import PropertyKindCalculus.Requirements.Attributes
public import PropertyKindCalculus.Requirements.Catalogue
public import PropertyKindCalculus.Requirements.Annotations
public import PropertyKindCalculus.Requirements.DimensionAnnotations
public import PropertyKindCalculus.Requirements.UncertaintyAnnotations
public import PropertyKindCalculus.Requirements.ExampleAnnotations
public import PropertyKindCalculus.Requirements.RenderingAnnotations
public import PropertyKindCalculus.Requirements.ForPhysLibAnnotations

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose



end -- pkc-blanket-expose
end -- pkc-blanket
