/-
# KindRequirement — the marks, the check and the censuses over requirements

`Requirement` is prelude-only data: what a boundary's quantities must satisfy and by what
evidence. This module is everything that reads it — in the shape `KindIncidence` set for
the theorem edge (`#kind_relation` checks one, `#kind_relations` surveys a scope) and
`ContractCoverage` set for the censuses (a record command whose sorted `info` message is
pinned, a gate that throws and pins nothing, a declared exception where the population has
honest negatives, an `AuditReceipt` at each success point).

  * **Two marks.** `@[kindReferent "where it comes from"]` on a kinded quantity enrolls it
    as a **referent**: something the model does not define — a datasheet value, a prior, a
    reference measurement — and the only thing an empirical requirement may be decided
    against. `@[kindRequirementFree "reason"]` on a model boundary says it legitimately has
    no requirement, in the author's words where the census reads them.
  * **`#kind_requirement r`** checks one requirement and throws on every failure, so the
    command is the report and the gate at once: the governed boundary is a model's; the
    port is one it declares; the scope names a sort, sorted objects, or a decider; a
    provable requirement's witness is a theorem edge from the governed boundary to a
    *specification boundary* (or a sorry-free theorem) whose statement names no referent;
    a claimed absence is a license the environment holds no instance of; an empirical
    requirement names marked referents and a gate that mentions one, and no theorem; every
    spot check is a `Bool` that evaluates to `true`; an attestation stands in for a
    discharge and never beside one.
  * **`#kind_requirements ns …`** surveys every `Requirement` under the namespaces, each
    re-checked exactly as above, one line per requirement, violations as `✗` rows.
  * **`#kind_requirement_coverage ns …`** is the census: every produced port of every
    *model* boundary in scope is `[governed]` by a requirement naming it (a requirement
    with no port governs everything its boundary produces), `⊘ exempted` by a
    `@[kindRequirementFree]` mark, or `⚠ UNGOVERNED`; a specification boundary is listed as
    the subject of no requirement. The summary counts the requirements by category and the
    attested ones — the ratchet. Whether a named requirement is *valid* is
    `#kind_requirements`' question; this census asks only whether one exists.
  * **`#kind_requirement_clean ns …`** is the gate: throws while any produced port of a
    model boundary in scope is `⚠ UNGOVERNED`.

Requirements are walked *unscoped* by the census, as theorem edges are: a requirement may
live beside a deployment rather than beside the boundary it governs. A
`@[kindCounterexample]` requirement is a subject of nothing. Import-closure sensitive like
every environment walk.
-/

module

public import Lean
public import PropertyKindCalculus.ContractCoverage
public meta import PropertyKindCalculus.ContractCoverage
public import PropertyKindCalculus.Requirement
public meta import PropertyKindCalculus.Requirement

-- Same-module helpers serve both the command elaborators below and runtime callers, so the
-- phase check is relaxed for this file (the module system's mixed-use escape; imports are
-- still checked and take `public meta import`).
set_option compiler.relaxedMetaCheck true

public section Interface

namespace PropertyKindCalculus.KindRequirement

open Lean Meta
open PropertyKindCalculus.Provenance (NodeId KindRef)
open PropertyKindCalculus.KindIncidence (contractValueOf checkRelation)
open PropertyKindCalculus.ContractCoverage (ContractMark Subject subjects Row Verdict count body
  violations indented names)

/-! ## The two marks -/

/-- `@[kindReferent …]`-marked declarations: the kinded quantities a model does not define. -/
initialize kindReferentExt :
    SimplePersistentEnvExtension ContractMark (Array ContractMark) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-- `@[kindRequirementFree …]`-marked contracts. -/
initialize kindRequirementFreeExt :
    SimplePersistentEnvExtension ContractMark (Array ContractMark) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-- `@[kindReferent "<where it comes from>"]` — declare a kinded quantity to be a referent:
something the model does not define, with its provenance in the author's words. The mark
is what the demarcation reads: a provable requirement's statement may name no referent,
and an empirical requirement's gate must name one. -/
syntax (name := kindReferentAttr) "kindReferent " str : attr

/-- `@[kindRequirementFree "<reason>"]` — declare that a model boundary legitimately has no
requirement: nothing is demanded of what it produces. -/
syntax (name := kindRequirementFreeAttr) "kindRequirementFree " str : attr

initialize registerBuiltinAttribute {
  name  := `kindReferentAttr
  descr := "A kinded quantity the model does not define — a datasheet value, a prior, a \
    reference measurement — with where it comes from: the referent an empirical requirement \
    is decided against."
  add   := fun decl stx _kind => do
    match stx with
    | `(attr| kindReferent $source:str) => do
        let env ← getEnv
        let some info := env.find? decl
          | throwError "`@[kindReferent]` could not find '{decl}' in the environment"
        let head := info.type.getAppFn
        let kinded := head.isConstOf ``PropertyKindCalculus.Quantity
          || head.isConstOf ``PropertyKindCalculus.IndividualQuantity
        unless kinded do
          throwError "`@[kindReferent]` expects a kinded quantity — a 'Quantity' or an \
            'IndividualQuantity' — and '{decl}' is neither. A referent is a number about \
            the world, and the kind is what says which number; a bare carrier value is \
            invisible to every census."
        if source.getString.all Char.isWhitespace then
          throwError "`@[kindReferent]` on '{decl}' needs to say where the referent comes \
            from: a threshold with no provenance is the docstring problem in a new place"
        modifyEnv fun env =>
          kindReferentExt.addEntry env { decl, reason := source.getString }
    | _ => throwError "invalid `kindReferent` attribute; expected \
        `kindReferent \"<where it comes from>\"`"
}

initialize registerBuiltinAttribute {
  name  := `kindRequirementFreeAttr
  descr := "A model boundary declared requirement-free on purpose: \
    `#kind_requirement_coverage` lists it as exempted instead of gating on it."
  add   := fun decl stx _kind => do
    match stx with
    | `(attr| kindRequirementFree $reason:str) => do
        let env ← getEnv
        let some info := env.find? decl
          | throwError "`@[kindRequirementFree]` could not find '{decl}' in the environment"
        unless info.type.getAppFn.isConstOf ``PropertyKindCalculus.Provenance.Contract do
          throwError "`@[kindRequirementFree]` expects a 'Provenance.Contract' — '{decl}' \
            is not one. The mark exempts a declared boundary from a census over declared \
            boundaries, so that is where it goes."
        if reason.getString.all Char.isWhitespace then
          throwError "`@[kindRequirementFree]` on '{decl}' needs a reason: an exemption \
            without one is the docstring problem in a new place"
        modifyEnv fun env =>
          kindRequirementFreeExt.addEntry env { decl, reason := reason.getString }
    | _ => throwError "invalid `kindRequirementFree` attribute; expected \
        `kindRequirementFree \"<reason>\"`"
}

/-- Every `@[kindReferent]` mark in the environment. -/
def kindReferents (env : Environment) : Array ContractMark :=
  kindReferentExt.getState env

/-- Every `@[kindRequirementFree]` mark in the environment. -/
def kindRequirementFreeMarks (env : Environment) : Array ContractMark :=
  kindRequirementFreeExt.getState env

/-! ## Reading a requirement -/

private unsafe def evalRequirementUnsafe (e : Expr) : MetaM Provenance.Requirement :=
  Meta.evalExpr Provenance.Requirement (mkConst ``Provenance.Requirement) e

/-- The declared requirement's value. Replaced at run time by the evaluator; the safe body
stands only where no evaluator is available. -/
@[implemented_by evalRequirementUnsafe]
def evalRequirement (_e : Expr) : MetaM Provenance.Requirement :=
  throwError "requirement values cannot be read in this environment"

/-- The declared requirement's value, with the type check that gives a legible error before
the evaluator is asked for one. -/
def requirementValueOf (rname : Name) : MetaM Provenance.Requirement := do
  unless ← Meta.isDefEq (← Meta.inferType (mkConst rname))
      (mkConst ``Provenance.Requirement) do
    throwError "'{rname}' is not a 'Provenance.Requirement'"
  evalRequirement (mkConst rname)

private unsafe def evalSpotCheckUnsafe (e : Expr) : MetaM Bool :=
  -- as `#guard` evaluates its term
  Meta.evalExpr (checkMeta := false) Bool (mkConst ``Bool) e

/-- A spot check's value. Replaced at run time by the evaluator; the safe body stands only
where no evaluator is available. -/
@[implemented_by evalSpotCheckUnsafe]
def evalSpotCheck (_e : Expr) : MetaM Bool :=
  throwError "spot checks cannot be evaluated in this environment"

/-- The constants a declaration's statement mentions. -/
private def mentionsOf (e : Expr) : NameSet :=
  e.foldConsts ({} : NameSet) fun c s => s.insert c

/-- The result of checking one requirement: the evaluated requirement, the governed
boundary's name as its contract renders it, and the report body — everything below the
header line, one entry per rendered line. -/
structure CheckedRequirement where
  req : Provenance.Requirement
  boundaryName : String
  lines : List String

/-- The full check of one requirement — `#kind_requirement`'s body, named so the survey
command re-runs it per requirement. Throws on the first violation. -/
def checkRequirement (rname : Name) : MetaM CheckedRequirement := do
  let req ← requirementValueOf rname
  let env ← getEnv
  if req.name.all Char.isWhitespace then
    throwError "the requirement '{rname}' has no name — a requirement is cited by name, \
      so give it the one the document uses"
  if req.statement.all Char.isWhitespace then
    throwError "the requirement '{req.name}' states nothing — the statement in the \
      author's words is what the discharge is evidence for"
  -- the governed boundary: a model's
  let ctr ← contractValueOf req.governs
  unless ctr.role == .model do
    throwError "'{req.name}' governs '{ctr.name}', which is a specification boundary — a \
      requirement governs a model boundary; a specification is what it is checked against"
  -- the governed port: one the boundary declares, or everything it produces
  let governsLine ← match req.port with
    | some p =>
      unless ctr.ports.any (·.node == p) do
        throwError "'{req.name}' governs the port '{p.render}', which '{ctr.name}' does \
          not declare"
      pure s!"governs: '{ctr.name}' at {p.render}"
    | none => pure s!"governs: every produced port of '{ctr.name}'"
  -- the scope: a sort, sorted objects, or a decider, each a declaration
  match req.scope with
  | .all => pure ()
  | .sort s =>
    let some sinfo := env.find? s
      | throwError "the scope sort '{s}' is not a declaration"
    unless sinfo.type.isConstOf ``PropertyKindCalculus.SortOfSystem do
      throwError "the scope '{s}' is not a 'SortOfSystem' — a scope over a sort names \
        the sort, and the objects reach it through their 'Sorted' instance"
  | .objects os =>
    if os.isEmpty then
      throwError "'{req.name}' quantifies over no object — an empty object list is a \
        vacuous scope; use `.all` for every object the boundary is evaluated for"
    for o in os do
      let some oinfo := env.find? o
        | throwError "the scope object '{o}' is not a declaration"
      let O := oinfo.type
      let sorted ← try Meta.mkAppM ``PropertyKindCalculus.Sorted #[O]
        catch _ => throwError "the scope object '{o}' has type '{O}', which is not an \
          object type"
      match ← Meta.synthInstance? sorted with
      | some _ => pure ()
      | none => throwError "the scope object '{o}' is of type '{O}', which has no \
          'Sorted' instance — an object of no sort is a bare value, not a particular a \
          requirement can quantify over"
  | .decided d =>
    unless (env.find? d).isSome do
      throwError "the scope decider '{d}' is not a declaration"
  let attested := !(req.attested.all Char.isWhitespace)
  let referents := kindReferents env
  let mut lines : List String :=
    [s!"statement: {req.statement}", governsLine, s!"scope: {req.scope.label}"]
  match req.kind with
  | .provable =>
    unless req.referents.isEmpty do
      throwError "'{req.name}' is provable but lists referents — a statement that names \
        what the model does not define is empirical"
    unless req.gate.isAnonymous do
      throwError "'{req.name}' is provable but names a gate — a gate decides against a \
        referent; a provable requirement's runtime evidence is a spot check"
    if req.witness.isAnonymous && req.absent.isAnonymous && !attested then
      throwError "'{req.name}' is provable but names no witness and no absence — a \
        provable requirement is discharged by a theorem, or attested with a reason"
    if attested && (!req.witness.isAnonymous || !req.absent.isAnonymous) then
      throwError "'{req.name}' is attested and discharged at once — an attestation defers \
        a discharge, so drop it where the discharge exists"
    -- the witness: a theorem edge from the governed boundary to a specification boundary,
    -- or a bare sorry-free theorem; either way a statement that names no referent
    unless req.witness.isAnonymous do
      let wname := req.witness
      let some winfo := env.find? wname
        | throwError "the witness '{wname}' is not a declaration"
      let statement ←
        if winfo.type.isConstOf ``Provenance.Relation then do
          let c ← checkRelation wname
          unless c.rel.left == req.governs do
            throwError "the edge '{wname}' is between '{c.leftName}' and '{c.rightName}', \
              and its left side is not the governed boundary '{ctr.name}' — a requirement \
              is checked against a specification from the boundary it governs"
          let right ← contractValueOf c.rel.right
          unless right.role == .specification do
            throwError "the right side of the edge '{wname}' is '{right.name}', a model \
              boundary — the bound a requirement is checked against is a specification \
              boundary (`role := .specification`)"
          lines := lines ++
            [s!"edge: {wname} — '{c.leftName}' {c.rel.kind.label} '{c.rightName}'",
             s!"witness: {c.rel.witness}"]
          let some tinfo := env.find? c.rel.witness
            | throwError "the witness '{c.rel.witness}' is not a declaration"
          pure tinfo.type
        else do
          unless Lean.wasOriginallyTheorem env wname do
            throwError "the witness '{wname}' is neither a theorem nor a theorem edge — a \
              provable requirement is discharged by a proof, and a definition asserts \
              nothing"
          let axs ← Lean.collectAxioms wname
          if axs.contains ``sorryAx then
            throwError "the witness '{wname}' depends on 'sorryAx' — it proves nothing yet"
          lines := lines ++ [s!"witness: {wname}",
            s!"axioms: {String.intercalate ", " (axs.toList.map toString)}"]
          pure winfo.type
      -- the demarcation: the statement closes over the model
      let mentions := mentionsOf statement
      for r in referents do
        if mentions.contains r.decl then
          throwError "'{req.name}' is provable, but the statement of '{wname}' names the \
            referent '{r.decl}' — a statement that names what the model does not define \
            is empirical"
    -- the absence: a license the environment holds no instance of
    unless req.absent.isAnonymous do
      let aname := req.absent
      let some ainfo := env.find? aname
        | throwError "the absence '{aname}' is not a declaration"
      let some license := ainfo.value? (allowOpaque := true)
        | throwError "the absence '{aname}' has no body to read — it names the license \
            that must be absent, as a definition of the class application"
      let some cls ← Meta.isClass? license
        | throwError "the absence '{aname}' does not unfold to a class application — a \
          license is an instance, and what must be absent is the instance"
      let found ← try Meta.synthInstance? license catch _ => pure none
      if found.isSome then
        throwError "an instance of '{cls}' at '{aname}' is in the environment — the \
          license '{req.name}' requires absent is present"
      lines := lines ++ [s!"absent: no instance of {aname}"]
  | .empirical =>
    unless req.witness.isAnonymous do
      throwError "'{req.name}' is empirical but names a witness — a theorem about the \
        model cannot discharge a statement about what the model does not define; if the \
        statement closes over the model, the requirement is provable"
    unless req.absent.isAnonymous do
      throwError "'{req.name}' is empirical but claims an absence — a license's absence \
        is a provable requirement's discharge"
    if attested && !req.gate.isAnonymous then
      throwError "'{req.name}' is attested and gated at once — an attestation defers a \
        discharge, so drop it where the gate exists"
    if !attested then
      if req.referents.isEmpty then
        throwError "'{req.name}' is empirical but names no referent — what the model does \
          not define is named, and marked `@[kindReferent]` with where it comes from"
      if req.gate.isAnonymous then
        throwError "'{req.name}' is empirical but names no gate — an empirical requirement \
          is discharged by a decision against its referent, or attested with a reason"
    for r in req.referents do
      match referents.find? (·.decl == r) with
      | some m => lines := lines ++ [s!"referent: {r} — {m.reason}"]
      | none => throwError "the referent '{r}' is not marked `@[kindReferent]` — a \
          referent carries where it comes from, and the mark is what the demarcation reads"
    unless req.gate.isAnonymous do
      let gname := req.gate
      let some ginfo := env.find? gname
        | throwError "the gate '{gname}' is not a declaration"
      let mentions := match ginfo.value? (allowOpaque := true) with
        | some v => (mentionsOf ginfo.type).union (mentionsOf v)
        | none => mentionsOf ginfo.type
      unless req.referents.any mentions.contains do
        throwError "the gate '{gname}' names none of the referents — a decision whose \
          threshold is the model's own is not an observation"
      lines := lines ++ [s!"gate: {gname}"]
  -- the spot checks: each a `Bool` the command runs
  for s in req.spotChecks do
    let some sinfo := env.find? s
      | throwError "the spot check '{s}' is not a declaration"
    unless sinfo.type.isConstOf ``Bool do
      throwError "the spot check '{s}' is not a 'Bool' — a spot check is a decision the \
        command can run"
    unless ← evalSpotCheck (mkConst s) do
      throwError "the spot check '{s}' evaluated to false — the requirement fails where \
        the model runs"
    lines := lines ++ [s!"spot check: {s} = true"]
  if attested then
    lines := lines ++ [s!"attested: {req.attested}"]
  return { req, boundaryName := ctr.name, lines }

open Elab Command in
/-- `#kind_requirement r` checks the requirement `r` (`checkRequirement`) and prints it.
Every failure throws, so the command is the report and the gate at once — there is no
reading of it that states a violation. -/
elab "#kind_requirement " r:ident : command => liftTermElabM do
  let c ← checkRequirement (← realizeGlobalConstNoOverload r)
  logInfo m!"kind requirement '{c.req.name}' ({c.req.kind.label}) on '{c.boundaryName}'\n\
    {String.intercalate "\n" c.lines}"

/-- The requirements under the namespaces, split into the checked and the
`@[kindCounterexample]`-exempted, each sorted by name. -/
def requirementSweepSubjects (scopes : Array Name) : MetaM (Array Name × Array Name) := do
  let env ← getEnv
  let exempt : NameSet :=
    (BoundaryAudit.kindCounterexamples env).foldl (init := {}) (·.insert ·)
  let mut names : Array Name := #[]
  let mut exempted : Array Name := #[]
  for (n, info) in env.constants.toList do
    if n.isInternal then continue
    unless scopes.any (·.isPrefixOf n) do continue
    unless info.type.isConstOf ``Provenance.Requirement do continue
    if exempt.contains n then exempted := exempted.push n else names := names.push n
  return (names.qsort (fun a b => a.toString < b.toString),
          exempted.qsort (fun a b => a.toString < b.toString))

/-- How a requirement is discharged, in one phrase for a survey row. -/
def dischargeLabel (req : Provenance.Requirement) : String :=
  if !(req.attested.all Char.isWhitespace) then s!"attested: {req.attested}"
  else match req.kind with
    | .provable =>
      let w := if req.witness.isAnonymous then [] else [s!"by {req.witness}"]
      let a := if req.absent.isAnonymous then [] else [s!"absent {req.absent}"]
      String.intercalate ", " (w ++ a)
    | .empirical => s!"gated by {req.gate}"

open Elab Command in
/-- `#kind_requirements ns…` — the requirement survey: every `Provenance.Requirement`
declared under the given namespaces, re-checked exactly as `#kind_requirement` checks one,
rendered one line per requirement in declaration-name order as a single `info` message
suitable for `#guard_msgs` pinning. A requirement that fails its check renders as a `✗` row
carrying the refusal, so the pin is the gate; a `@[kindCounterexample]`-tagged requirement
renders as a `⊘` row and is not checked. The header counts the requirements, the violations,
the exemptions, and the categories — the attested count is the ratchet. -/
elab "#kind_requirements " nss:ident* : command => liftTermElabM do
  if nss.isEmpty then
    throwError "#kind_requirements expects at least one namespace"
  let scopes := nss.map (·.getId)
  let (sorted, exempt) ← requirementSweepSubjects scopes
  let mut lines : Array String := #[]
  let mut violated := 0
  let mut provable := 0
  let mut empirical := 0
  let mut attested := 0
  for n in sorted do
    try
      let c ← checkRequirement n
      match c.req.kind with
      | .provable => provable := provable + 1
      | .empirical => empirical := empirical + 1
      if !(c.req.attested.all Char.isWhitespace) then attested := attested + 1
      lines := lines.push
        s!"  {n}: '{c.req.name}' ({c.req.kind.label}) on '{c.boundaryName}' — \
          {dischargeLabel c.req}"
    catch e =>
      violated := violated + 1
      lines := lines.push s!"  ✗ {n}: {← e.toMessageData.toString}"
  for n in exempt do
    lines := lines.push s!"  ⊘ {n}: counterexample, exempted"
  let violations := if violated == 0 then "" else s!", {violated} violated"
  let exemptions := if exempt.isEmpty then "" else s!", {exempt.size} exempted"
  let summary := s!"kind requirements — {sorted.size} requirement(s){violations}\
    {exemptions}: {provable} provable, {empirical} empirical, {attested} attested"
  if lines.isEmpty then logInfo m!"{summary}"
  else logInfo m!"{summary}\n{String.intercalate "\n" lines.toList}"
  recordAuditReceipt "kind_requirements" scopes

/-! ## The census — requirement coverage -/

/-- Every requirement in the environment that is not a counterexample, with its value,
sorted by declaration. **Unscoped**, as `ContractCoverage.relationEntries` is: a
requirement may live beside a deployment rather than beside the boundary it governs, so
only the boundaries are scoped. -/
def requirementEntries : MetaM (Array (Name × Provenance.Requirement)) := do
  let env ← getEnv
  let exempt : NameSet :=
    (BoundaryAudit.kindCounterexamples env).foldl (init := {}) (·.insert ·)
  let mut out : Array (Name × Provenance.Requirement) := #[]
  for (n, info) in env.constants.toList do
    if n.isInternal || exempt.contains n then continue
    unless info.type.isConstOf ``Provenance.Requirement do continue
    out := out.push (n, ← requirementValueOf n)
  return out.qsort fun a b => a.1.toString < b.1.toString

/-- The governing join: contract declaration name → the requirements governing it. -/
def requirementsByBoundary : MetaM (Std.HashMap Name (Array (Name × Provenance.Requirement))) := do
  let mut acc : Std.HashMap Name (Array (Name × Provenance.Requirement)) := {}
  for (n, req) in ← requirementEntries do
    acc := acc.insert req.governs ((acc.getD req.governs #[]).push (n, req))
  return acc

/-- The census's tallies beside its rows: model boundaries in scope, and the requirements
governing one of them by category and by attestation. -/
structure Tally where
  boundaries : Nat := 0
  provable : Nat := 0
  empirical : Nat := 0
  attested : Nat := 0
  deriving Repr, Inhabited

/-- One row per produced port of every model boundary in scope: `[governed]` by the
requirements naming it (by port, or by the boundary as a whole), `⊘ exempted` by a mark,
or `⚠ UNGOVERNED`; one row per specification, counterexample or unreadable boundary. -/
def coverageRows (scope : Array Name) : Elab.TermElabM (Array Row × Tally) := do
  let subs ← subjects scope
  let byBoundary ← requirementsByBoundary
  let marks := kindRequirementFreeMarks (← getEnv)
  let mut out : Array Row := #[]
  let mut tally : Tally := {}
  for s in subs do
    if s.counterexample then
      out := out.push ⟨.exempted, s!"⊘ exempted {s.decl} — counterexample"⟩
      continue
    let some c := s.value?
      | out := out.push ⟨.violation,
          s!"⚠ UNREADABLE {s.decl} — not a `Contract NodeId KindRef`"⟩
        continue
    if c.role == .specification then
      out := out.push ⟨.exempted,
        s!"⊘ specification {s.decl} {s.tag} — the subject of no requirement"⟩
      continue
    tally := { tally with boundaries := tally.boundaries + 1 }
    let reqs := byBoundary.getD s.decl #[]
    for (_, req) in reqs do
      match req.kind with
      | .provable => tally := { tally with provable := tally.provable + 1 }
      | .empirical => tally := { tally with empirical := tally.empirical + 1 }
      if !(req.attested.all Char.isWhitespace) then
        tally := { tally with attested := tally.attested + 1 }
    for p in c.ports do
      unless p.dir.produced do continue
      let governing := reqs.filter fun (_, req) =>
        match req.port with
        | none => true
        | some q => q == p.node
      if !governing.isEmpty then
        out := out.push ⟨.ok, s!"[governed] {s.decl} {s.tag} {p.node.render} — by \
          {String.intercalate ", " (governing.map (fun (_, r) => s!"'{r.name}'")).toList}"⟩
      else match marks.find? (·.decl == s.decl) with
        | some m => out := out.push ⟨.exempted,
            s!"⊘ exempted {s.decl} {s.tag} {p.node.render} — {m.reason}"⟩
        | none => out := out.push ⟨.violation,
            s!"⚠ UNGOVERNED {s.decl} {s.tag} {p.node.render}"⟩
  return (out, tally)

/-- The summary lines: the port counts, `clean` exactly when no row is a violation, and the
requirement tallies — the attested count is the ratchet. -/
def coverageSummary (rows : Array Row) (t : Tally) : String :=
  let (nOk, nEx, nBad) := (count rows .ok, count rows .exempted, count rows .violation)
  let ex := if nEx > 0 then s!", {nEx} exempted" else ""
  let ports := if nBad == 0 then
      s!"{rows.size} row(s) over {t.boundaries} model boundary(ies): {nOk} governed{ex} — clean"
    else
      s!"{rows.size} row(s) over {t.boundaries} model boundary(ies): {nOk} governed{ex}, \
        {nBad} UNGOVERNED — requirement-coverage violation"
  s!"{ports}\nrequirements: {t.provable} provable, {t.empirical} empirical, {t.attested} attested"

open Elab Command in
/-- `#kind_requirement_coverage ns …` — the census: every produced port of every model
boundary under the namespaces, each `[governed]` by the requirements naming it,
`⊘ exempted` by a `@[kindRequirementFree]` mark (or as a counterexample), or
`⚠ UNGOVERNED`; specification boundaries listed as the subject of no requirement. One
sorted `info` message to pin, with the category tallies and the attested ratchet. Records an
`AuditReceipt` for `kind_requirement_coverage`. -/
elab "#kind_requirement_coverage" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let (rows, tally) ← coverageRows scope
  recordAuditReceipt "kind_requirement_coverage" scope
  if rows.isEmpty then
    logInfo m!"requirement coverage — no declared boundaries in the given namespaces"
    return
  logInfo m!"requirement coverage:\n{body rows}\n{coverageSummary rows tally}"

open Elab Command in
/-- `#kind_requirement_clean ns …` — **the invariant, stated apart from the record.** No
message; throws while any produced port of a model boundary in scope is `⚠ UNGOVERNED`.
Records an `AuditReceipt` for `kind_requirement_clean` exactly when it does not fire. -/
elab "#kind_requirement_clean" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let bad := violations (← coverageRows scope).1
  unless bad.isEmpty do
    throwError "requirement coverage: {bad.size} produced port(s) no requirement governs \
      — requirement-coverage violation\n{indented bad}\n\n\
      What a model's quantities must satisfy is stated as a `Provenance.Requirement` \
      governing the boundary that produces them, not as prose beside the module. Give each \
      port at issue a requirement — provable with its theorem edge or theorem, empirical \
      with its referents and gate, or attested with a reason — or, where nothing is \
      demanded of what the boundary produces, mark its declaration \
      `@[kindRequirementFree \"reason\"]` so the exemption is data the sweep can read. Do \
      NOT re-pin a `#kind_requirement_coverage` report whose summary says `violation` — \
      that turns the build green and the census off."
  recordAuditReceipt "kind_requirement_clean" scope

end PropertyKindCalculus.KindRequirement

end Interface
