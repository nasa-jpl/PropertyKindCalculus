/-
# Validation probes — the requirement-traceability attribute

`@[requirement "<id>" <role>]` is the only way evidence enters the traceability matrix, and
the matrix only ever loops over the catalogue's rows. So an annotation carrying an id that
is not in the catalogue has exactly one possible fate — to be stored and never rendered —
which is the silent drift the layer exists to prevent. This probe pins that such an id is
refused where it is written, the same way `@[rubric]` refuses an unknown rubric, and that a
catalogued id with a bad role is still refused for the role.

The probes:

  * a catalogued id in a valid role is harvested, and its status is derived from the role;
  * an id outside the catalogue is an error at the annotation site;
  * a catalogued id with an unrecognised role is an error at the annotation site.
-/

module

public import PropertyKindCalculus.Requirements.Attributes
meta import PropertyKindCalculus.Requirements.Attributes

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.Requirements

open Lean Elab Command
open PropertyKindCalculus.Requirements

/-- Stands in for a theorem discharging a verifiable requirement. -/
theorem probeProof : 1 + 1 = 2 := rfl

attribute [requirement "R4" proves "the probe's discharging theorem"] probeProof

/-- The links this probe contributed, as `id:role` pairs — scoped to the probe's own
declarations, because the harvest is environment-wide. -/
def probeLinks (env : Environment) : String :=
  String.intercalate ", " <|
    ((requirementRefs env).filter fun r =>
      (`PropertyKindCalculus.Tests.Requirements).isPrefixOf r.decl).toList.map fun r =>
        s!"{r.req}:{r.role.label}"

/-- info: R4:proves -/
#guard_msgs in
#eval show CommandElabM Unit from do logInfo (probeLinks (← getEnv))

/-! An id outside the catalogue is refused where it is written, not where it is read. -/

/--
error: unknown requirement 'R99'; it is not in `PropertyKindCalculus.Requirements.catalogue`
-/
#guard_msgs in
attribute [requirement "R99" proves] probeProof

/-- error: invalid requirement role 'refutes'; expected one of specifies, proves, implements, exemplifies -/
#guard_msgs in
attribute [requirement "R4" refutes] probeProof

/-- info: R4:proves -/
#guard_msgs in
#eval show CommandElabM Unit from do logInfo (probeLinks (← getEnv))

end PropertyKindCalculus.Tests.Requirements

end Blanket
