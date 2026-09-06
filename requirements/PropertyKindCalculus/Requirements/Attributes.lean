/-
# Requirement-traceability attributes — `@[requirement …]`

The blueprint fixes a set of *requirements* (R1 … R27) the calculus is specified
to meet. Each requirement is discharged by real declarations — the type that
*states* it, the theorem that *proves* it, the definition that *implements* it, or
the worked example that *exercises* it. Those correspondences were, until now,
recorded only as free text in the blueprint's `requirementsTable` ("Specified as"
column), where they drift silently when a declaration is renamed.

This module makes them **typed, decl-indexed metadata**: a single parametric
attribute,

```
@[requirement "R4" proves]
@[requirement "R5" specifies "the partial ternary product KMul"]
```

backed by an environment extension that collects every tagged declaration.
Because an attribute attaches to a *real* declaration, a requirement can never
name a declaration that does not exist — a rename is a compile error, not silent
drift. The attribute is applied **from a separate module** (`Annotations`) via the
standalone `attribute [..] decl` command, so the Mathlib-free core spine never
imports this machinery and stays prelude-only. This mirrors the discipline of the
`@[dybkaer …]` / `@[vim4 …]` cross-reference attributes in
`PropertyKindCalculus.CrossRefs`.

Any consumer — the blueprint's traceability matrix, or a future query tool — can
ask, for a given requirement, *where it is formalized, proved, and implemented*.
-/

import Lean
import PropertyKindCalculus.Requirements.Catalogue

open Lean

namespace PropertyKindCalculus.Requirements

/-- How a declaration relates to the requirement it is tagged with. -/
inductive RequirementRole where
  /-- The type/structure/definition that *states* the requirement. -/
  | specifies
  /-- The theorem that *discharges* (proves) the requirement. -/
  | proves
  /-- The definition/instance that *implements* it (e.g. an executable carrier). -/
  | implements
  /-- The worked example that *exercises* it. -/
  | exemplifies
  deriving Repr, Inhabited, DecidableEq, BEq

namespace RequirementRole

/-- Parse a role keyword; `none` if unrecognized. -/
def ofString? : String → Option RequirementRole
  | "specifies"   => some .specifies
  | "proves"      => some .proves
  | "implements"  => some .implements
  | "exemplifies" => some .exemplifies
  | _             => none

/-- The role as printed in the traceability matrix. -/
def label : RequirementRole → String
  | .specifies   => "specifies"
  | .proves      => "proves"
  | .implements  => "implements"
  | .exemplifies => "exemplifies"

/-- A stable ordering key so the matrix lists specification, then proof, then
implementation, then example. -/
def order : RequirementRole → Nat
  | .specifies   => 0
  | .proves      => 1
  | .implements  => 2
  | .exemplifies => 3

end RequirementRole

/-- One requirement-traceability link: the Lean declaration it annotates, the
requirement identifier it discharges (e.g. `"R4"`), the *role* the declaration
plays, and an optional note in this work's own words. -/
structure RequirementRef where
  /-- The annotated Lean declaration (resolved, so it cannot dangle). -/
  decl : Name
  /-- The requirement identifier, as printed — `"R1"` … `"R27"`. -/
  req : String
  /-- The role the declaration plays for the requirement. -/
  role : RequirementRole
  /-- A short note on the correspondence, in this work's own words. -/
  note : String := ""
  deriving Repr, Inhabited, DecidableEq

/-- Environment extension collecting every `@[requirement …]`-annotated declaration. -/
initialize requirementExt :
    SimplePersistentEnvExtension RequirementRef (Array RequirementRef) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-- `@[requirement "<id>" <role> ("<note>")?]` — record that a declaration
discharges part of a blueprint requirement, in the given role. `<role>` is one of
`specifies`, `proves`, `implements`, `exemplifies`. -/
syntax (name := requirementAttr) "requirement " str ident (str)? : attr

initialize registerBuiltinAttribute {
  name  := `requirementAttr
  descr := "Traceability link from a declaration to a blueprint requirement (R1–R27)."
  add   := fun decl stx _kind => do
    match stx with
    | `(attr| requirement $req:str $role:ident $[$note:str]?) =>
        let some role := RequirementRole.ofString? role.getId.toString
          | throwError "invalid requirement role '{role.getId}'; expected one of \
              specifies, proves, implements, exemplifies"
        let note := (note.map (·.getString)).getD ""
        modifyEnv fun env =>
          requirementExt.addEntry env
            { decl := decl, req := req.getString, role := role, note := note }
    | _ => throwError "invalid `requirement` attribute; expected \
        `requirement \"<id>\" <role> [\"<note>\"]`"
}

/-- Every requirement-traceability link harvested into `env`, in registration order. -/
def requirementRefs (env : Environment) : Array RequirementRef :=
  requirementExt.getState env

/-- The links discharging a single requirement `id` (e.g. `"R7"`). -/
def refsForRequirement (env : Environment) (id : String) : Array RequirementRef :=
  (requirementRefs env).filter (·.req == id)

/-- Whether requirement `id` has at least one declaration annotated in the given role. -/
def requirementHasRole (env : Environment) (id : String) (role : RequirementRole) : Bool :=
  (refsForRequirement env id).any (·.role == role)

/-- The role whose presence *discharges* a requirement of the given kind: a
`verifiable` requirement is discharged by a `proves` theorem, an `expressiveness`
requirement by an `exemplifies` construction. -/
def RequirementKind.dischargeRole : RequirementKind → RequirementRole
  | .verifiable     => .proves
  | .expressiveness => .exemplifies

/-- The kind of a requirement `id` from the catalogue (defaulting to `verifiable`
for any id not in the catalogue). -/
def requirementKind (id : String) : RequirementKind :=
  ((requirementById? id).map (·.kind)).getD .verifiable

/-- Whether requirement `id` is *discharged* — has evidence in its discharging
role (`proves` for verifiable, `exemplifies` for expressiveness). -/
def requirementDischarged (env : Environment) (id : String) : Bool :=
  requirementHasRole env id (requirementKind id).dischargeRole

/-- The **evidence-derived status** of a requirement — a *computed* fact about the
annotations, never a hand-typed assertion — reported in the vocabulary of the
requirement's *kind*:

  * a **verifiable** requirement is `"proved"` once some declaration is annotated
    `proves`; an **expressiveness** requirement is `"demonstrated"` once some
    declaration is annotated `exemplifies` (a construction that typechecks);
  * `"specified"`   when it is addressed but not yet discharged in its kind's role;
  * `"unaddressed"` when no declaration references it at all.

Because this is a function of the harvested metadata and the requirement's kind,
the status can never disagree with the source: adding the discharging annotation is
what flips a requirement to `"proved"`/`"demonstrated"`, and there is no other
switch to forget to flip. -/
def requirementStatus (env : Environment) (id : String) : String :=
  if (refsForRequirement env id).isEmpty then "unaddressed"
  else if requirementDischarged env id then
    match requirementKind id with
    | .verifiable     => "proved"
    | .expressiveness => "demonstrated"
  else "specified"

/-- A count of how the catalogue's requirements stand, split by kind — the raw
material for the matrix's headline claim. -/
structure RequirementTally where
  /-- Total verifiable requirements. -/
  verifiableTotal : Nat
  /-- Verifiable requirements with a `proves` theorem. -/
  verifiableProved : Nat
  /-- Total expressiveness requirements. -/
  expressivenessTotal : Nat
  /-- Expressiveness requirements with an `exemplifies` construction. -/
  expressivenessDemonstrated : Nat
  deriving Repr, Inhabited

/-- Tally the catalogue against the harvested annotations, split by kind. -/
def requirementTally (env : Environment) : RequirementTally :=
  catalogue.foldl (init := ⟨0, 0, 0, 0⟩) fun t r =>
    match r.kind with
    | .verifiable =>
      { t with verifiableTotal := t.verifiableTotal + 1,
               verifiableProved := t.verifiableProved
                 + (if requirementDischarged env r.id then 1 else 0) }
    | .expressiveness =>
      { t with expressivenessTotal := t.expressivenessTotal + 1,
               expressivenessDemonstrated := t.expressivenessDemonstrated
                 + (if requirementDischarged env r.id then 1 else 0) }

end PropertyKindCalculus.Requirements
