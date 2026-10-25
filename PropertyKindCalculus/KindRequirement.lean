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
    `@[kindRequirementFree]` mark, `⚠ UNGOVERNED`, or `⚠ UNCHECKED`; a specification
    boundary is listed as the subject of no requirement. For object scopes, aliases in the
    member's result type are unfolded
    and only the `IndividualQuantity` bearer argument determines its domain: a matching
    index binder means all objects; closed T-typed subterms provide fixed objects (named
    constants are retained, other terms are reduced to constants). Other-type applications
    are searched through their arguments, and reducible projections, lets, and lambdas are
    followed. A missing object index is `.noIndex`; an irreducible bearer is `.unresolved`.
    Either is an unchecked violation unless the boundary is marked exempt. Objects match up
    to definitional equality. A `.sort` scope requires an indexed result and a `Sorted`
    instance for its object type. The census first reduces the actual result bearer's sort
    inside the member telescope: a definite match governs the port, while a definite
    mismatch falls back to object scopes or is ungoverned; a stuck sort uses the object-domain
    path and may be unchecked. A `.decided` scope governs only when its `deciderProof` proves
    that the decider holds for every result of the member; otherwise it is unchecked. The
    summary counts the requirements by category and the attested ones —
    the ratchet. Whether a named requirement is *valid*
    is `#kind_requirements`' question; this census asks only whether one exists.
  * **`#kind_requirement_clean ns …`** is the gate: throws while any produced port of a
    model boundary in scope is `⚠ UNGOVERNED` or `⚠ UNCHECKED`. An object scope must be
    checkable against the result's object index. A `.sort` scope requires that index and a
    `Sorted` instance, and checks the result object's sort. A `.decided` scope needs a
    `deciderProof` theorem for every produced result port or remains unchecked.

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
open PropertyKindCalculus.KindIncidence (contractValueOf checkRelation sweepSubjects runSurvey)
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

inductive PortDomain where
  | all
  | only (objs : List Name)
  | noIndex
  | unresolved
deriving Repr, Inhabited

/-- Collect closed T-typed bearer terms, following reducible non-object wrappers. -/
partial def fixedBearerObjects (bearer T : Expr) : MetaM (Array Name × Bool) := do
  match bearer with
  | .mdata _ inner => fixedBearerObjects inner T
  | _ =>
    if bearer.hasLooseBVars then return (#[], false)
    if (← Meta.isDefEq (← Meta.inferType bearer) T) then
      match bearer with
      | .const n _ => return (#[n], false)
      | _ =>
        let reduced ← withTransparency .default do Meta.whnf bearer
        match reduced with
        | .const n _ => return (#[n], false)
        | _ => return (#[], true)
    else
      match bearer with
      | .app .. =>
        let mut objects := #[]
        let mut unresolved := false
        for arg in bearer.getAppArgs do
          let (argObjects, argUnresolved) ← fixedBearerObjects arg T
          objects := objects ++ argObjects
          unresolved := unresolved || argUnresolved
        return (objects, unresolved)
      | _ =>
        let reduced ← withTransparency .default do Meta.whnf bearer
        if reduced != bearer then
          fixedBearerObjects reduced T
        else
          match bearer with
          | .proj .. | .letE .. | .lam .. => return (#[], true)
          | _ => return (#[], false)

/-- Infer the object domain of the reduced `IndividualQuantity` bearer. -/
def bearerDomain (binders : Array Expr) (bearer T : Expr) : MetaM PortDomain := do
  let carriesAll ← binders.anyM fun binder => do
    let binderType ← Meta.inferType binder
    return (← Meta.isDefEq binderType T) && bearer.containsFVar binder.fvarId!
  if carriesAll then return .all
  let (foundObjects, unresolved) ← fixedBearerObjects bearer T
  if unresolved then return .unresolved
  let mut objects := #[]
  for n in foundObjects do
    if !objects.contains n then objects := objects.push n
  return if objects.isEmpty then .noIndex else .only objects.toList

/-- Open a member's reduced `IndividualQuantity` result in its original telescope. -/
def withResultIndividualQuantity {α} (member : Name)
    (k : Array Expr → Array Expr → MetaM α) : MetaM (Option α) := do
  let env ← getEnv
  let some info := env.find? member | return none
  Meta.forallTelescopeReducing info.type fun binders result => do
    let result ← withTransparency .default do Meta.whnf result
    let (head, args) := result.getAppFnArgs
    unless head == ``PropertyKindCalculus.IndividualQuantity && args.size == 4 do
      return none
    return some (← k binders args)

def portDomain (member : Name) (T : Expr) : MetaM PortDomain := do
  match ← withResultIndividualQuantity member fun binders args =>
      bearerDomain binders args[1]! T with
  | some domain => return domain
  | none => return .noIndex

/-- The declaration whose result a result port belongs to, when it is a whole result. -/
def resultMember? (node : NodeId) : Option Name :=
  if node.root != .result none || !node.path.isEmpty then none else
    match node.level with
    | some (.inst member _) | some (.member member) => some member
    | none => none

/-- A result port's object type and domain, with the member telescope closed. -/
def portObjectInfoFor (node : NodeId) : MetaM (Option (Expr × PortDomain)) := do
  let some member := resultMember? node | return none
  let some info ← withResultIndividualQuantity member fun binders args => do
    let objectType := args[0]!
    let domain ← bearerDomain binders args[1]! objectType
    let objectType ← Meta.mkForallFVars binders objectType
    pure (objectType, domain)
    | return none
  return some info

/-- Group named objects by the declaration type of each object. -/
def objectsByType (objects : Array Name) : MetaM (Array (Expr × Array Name)) := do
  let env ← getEnv
  let mut groups : Array (Expr × Array Name) := #[]
  for object in objects do
    let some info := env.find? object | continue
    let mut groupIndex : Option Nat := none
    for i in [:groups.size] do
      if ← Meta.isDefEq groups[i]!.1 info.type then
        groupIndex := some i
        break
    if let some i := groupIndex then
      let (type, names) := groups[i]!
      if !names.contains object then groups := groups.set! i (type, names.push object)
    else
      groups := groups.push (info.type, #[object])
  return groups

/-- A result port's object domain, or `.noIndex` for every other produced port. -/
def portDomainFor (node : NodeId) (T : Expr) : MetaM PortDomain := do
  match resultMember? node with
  | some member => portDomain member T
  | none => return .noIndex

/-- Check a theorem's declaration kind and reject any dependency on `sorryAx`. -/
def checkTheoremEvidence (env : Environment) (name : Name) (subject rejection : String) :
    MetaM (Array Name) := do
  unless Lean.wasOriginallyTheorem env name do
    throwError "{subject} '{name}' {rejection}"
  let axioms ← Lean.collectAxioms name
  if axioms.contains ``sorryAx then
    throwError "{subject} '{name}' depends on 'sorryAx' — it proves nothing yet"
  return axioms

/-- Check that a decider theorem proves the predicate on every result of one member. -/
def checkDeciderProof (decider proof member : Name) : MetaM Unit := do
  let env ← getEnv
  let some proofInfo := env.find? proof
    | throwError "the decider proof '{proof}' is not a declaration"
  let _ ← checkTheoremEvidence env proof "the decider proof"
    "is not a theorem — a decider proof must be a theorem, not an axiom or definition"
  let some memberInfo := env.find? member
    | throwError "the result member '{member}' is not a declaration"
  let expected ← Meta.forallTelescopeReducing memberInfo.type fun xs _ => do
    let memberFn ← mkConstWithLevelParams member
    let memberValue := mkAppN memberFn xs
    let predicate ←
      try do
        let deciderValue ← Meta.mkAppM decider #[memberValue]
        Meta.mkEq deciderValue (toExpr true)
      catch _ =>
        throwError "'{decider}' does not apply to what '{member}' produces"
    Meta.mkForallFVars xs predicate
  let isMatch ← withTransparency .default do
    Meta.isDefEq proofInfo.type expected
  unless isMatch do
    throwError "'{proof}' does not prove that '{decider}' holds on everything \
      '{member}' produces — expected: {expected}"

/-- Whether a decided requirement carries a checked proof for this whole result port. -/
def deciderProofCoversPort (req : Provenance.Requirement) (port : NodeId) :
    MetaM Bool := do
  match req.scope, req.deciderProof, resultMember? port with
  | .decided decider, some proof, some member =>
    try
      checkDeciderProof decider proof member
      return true
    catch _ => return false
  | _, _, _ => return false

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
  if let some proof := req.deciderProof then
    unless req.scope matches .decided _ do
      throwError "'{req.name}' has a decider proof, but its scope is not `.decided`"
    unless (env.find? proof).isSome do
      throwError "the decider proof '{proof}' is not a declaration"
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
    if let some node := req.port then
      if let some port := ctr.ports.find? (·.node == node) then
        unless port.dir.produced do
          throwError "'{req.name}' is scoped to objects or a sort, but '{node.render}' of \
            '{ctr.name}' is an input — an object or sort scope quantifies over the objects \
            an output belongs to; govern a produced port"
    let ports := ctr.ports.filter fun p =>
      p.dir.produced &&
        match req.port with
        | some node => p.node == node
        | none => true
    for port in ports do
      let noIndexError := s!"'{req.name}' is scoped to sort '{s}', but \
        '{port.node.render}' of '{ctr.name}' carries no object index — a sort scope \
        quantifies over the objects an output belongs to; index the result by its object"
      let some (objectType, domain) ← portObjectInfoFor port.node
        | throwError noIndexError
      match domain with
      | .noIndex => throwError noIndexError
      | _ =>
        Meta.forallTelescopeReducing objectType fun _ objectType => do
          let sortedType ← Meta.mkAppM ``PropertyKindCalculus.Sorted #[objectType]
          let some _ ← Meta.synthInstance? sortedType
            | do
              let objectTypeName := toString (← Meta.ppExpr objectType)
              throwError "'{req.name}' is scoped to sort '{s}', but the objects of \
                '{port.node.render}' ('{objectTypeName}') declare no sort — give \
                '{objectTypeName}' a `Sorted` instance"
          pure ()
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
    if let some proof := req.deciderProof then
      let ports := ctr.ports.filter fun port =>
        match req.port with
        | some node => port.node == node
        | none => port.dir.produced
      for port in ports do
        let some member := resultMember? port.node
          | throwError "'{req.name}''s decider proof covers result ports only, but \
            '{port.node.render}' of '{ctr.name}' is not one"
        checkDeciderProof d proof member
  match req.scope with
  | .objects objects =>
    if let some node := req.port then
      if let some port := ctr.ports.find? (·.node == node) then
        unless port.dir.produced do
          throwError "'{req.name}' is scoped to objects or a sort, but '{node.render}' of \
            '{ctr.name}' is an input — an object or sort scope quantifies over the objects \
            an output belongs to; govern a produced port"
    let groups ← objectsByType objects.toArray
    let ports := ctr.ports.filter fun p =>
      p.dir.produced &&
        match req.port with
        | some node => p.node == node
        | none => true
    for (type, _) in groups do
      let typeName := toString (← Meta.ppExpr type)
      for port in ports do
        match ← portDomainFor port.node type with
        | .noIndex =>
          throwError "'{req.name}' is scoped to objects of type '{typeName}', but \
            '{port.node.render}' of '{ctr.name}' carries no '{typeName}' index — an object \
            scope quantifies over the objects an output belongs to; scope it over a sort or \
            `.all`, or index the result by its object"
        | _ => pure ()
  | _ => pure ()
  let attested := !(req.attested.all Char.isWhitespace)
  let referents := kindReferents env
  let mut lines : List String :=
    [s!"statement: {req.statement}", governsLine, s!"scope: {req.scope.label}"]
  if let some proof := req.deciderProof then
    lines := lines ++ [s!"decider proof: {proof}"]
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
          let axs ← checkTheoremEvidence env wname "the witness"
            "is neither a theorem nor a theorem edge — a provable requirement is discharged \
              by a proof, and a definition asserts nothing"
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
      let found ← try Meta.synthInstance? license
        catch e => throwError "could not decide whether '{cls}' has an instance at \
          '{aname}' — the instance search did not finish: {e.toMessageData}"
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
For a `.decided` scope, a supplied `deciderProof` must prove the decider holds for every
result of each governed member. Every failure throws, so the command is the report and the
gate at once — there is no reading of it that states a violation. -/
elab "#kind_requirement " r:ident : command => liftTermElabM do
  let c ← checkRequirement (← realizeGlobalConstNoOverload r)
  logInfo m!"kind requirement '{c.req.name}' ({c.req.kind.label}) on '{c.boundaryName}'\n\
    {String.intercalate "\n" c.lines}"

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
renders as a `⊘` row and is not checked. The header counts the checked requirements, the
violations, the exemptions, and the categories — the attested count is the ratchet. -/
elab "#kind_requirements " nss:ident* : command => liftTermElabM do
  if nss.isEmpty then
    throwError "#kind_requirements expects at least one namespace"
  let scopes := nss.map (·.getId)
  let (names, exempted) ← sweepSubjects scopes (·.isConstOf ``Provenance.Requirement)
  let survey ← runSurvey names exempted checkRequirement fun c =>
    s!"'{c.req.name}' ({c.req.kind.label}) on '{c.boundaryName}' — {dischargeLabel c.req}"
  let provable := survey.passed.countP (·.req.kind matches .provable)
  let empirical := survey.passed.countP (·.req.kind matches .empirical)
  let attested := survey.passed.countP fun c => !(c.req.attested.all Char.isWhitespace)
  survey.log "kind requirements" "requirement(s)"
    s!": {provable} provable, {empirical} empirical, {attested} attested"
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

/-- Compare an object with named objects after unfolding definitionally equal aliases. -/
def objectMem (xs : Array Name) (o : Name) : MetaM Bool := do
  let object ← mkConstWithLevelParams o
  for x in xs do
    let candidate ← mkConstWithLevelParams x
    if ← Meta.isDefEq object candidate then return true
  return false

/-- A boundary mark exempts any coverage violation without changing its subject. -/
def markedCoverageRow (marks : Array ContractMark) (decl : Name)
    (violationLine exemptionSubject : String) : Row :=
  match marks.find? (·.decl == decl) with
  | some mark => ⟨.exempted, s!"⊘ exempted {exemptionSubject} — {mark.reason}"⟩
  | none => ⟨.violation, violationLine⟩

/-- Render missing-object violations or their boundary exemption. -/
def missingObjectRows (marks : Array ContractMark) (decl : Name) (tag : String)
    (port : NodeId) (requirementNames scopedNames : String) (missing : Array String) :
    Array Row := Id.run do
  let mut out := #[]
  for object in missing do
    let subject := s!"{decl} {tag} {port.render} for {object}"
    let line := s!"⚠ UNGOVERNED {subject} — \
      {requirementNames} scoped to {scopedNames}"
    out := out.push <| markedCoverageRow marks decl line subject
  return out

/-- The finite object universe, when `T` is an unparameterized, unindexed inductive with
only nullary constructors. -/
def enumerableObjects (T : Expr) : MetaM (Option (Array Name)) := do
  let T ← Meta.whnf T
  let .const typeName _ := T | return none
  let env ← getEnv
  let some (.inductInfo info) := env.find? typeName | return none
  if info.numParams != 0 || info.numIndices != 0 then return none
  for ctor in info.ctors do
    let some (.ctorInfo ctorInfo) := env.find? ctor | return none
    if ctorInfo.numFields != 0 then return none
  return some info.ctors.toArray

def sortedInstanceFor (objectType : Expr) : MetaM (Option Expr) := do
  let sortedType ← Meta.mkAppM ``PropertyKindCalculus.Sorted #[objectType]
  Meta.synthInstance? sortedType

def sortedSortOf (objectType sorted object : Expr) : MetaM Expr := do
  let sortOf ← Meta.mkAppOptM ``PropertyKindCalculus.Sorted.sortOf
    #[some objectType, some sorted, some object]
  withTransparency .default do Meta.whnf sortOf

def sortMatchesRequirements (governing : Array (Name × Provenance.Requirement))
    (sortOf : Expr) : MetaM Bool := do
  for (_, req) in governing do
    if let .sort s := req.scope then
      let candidate ← mkConstWithLevelParams s
      if ← withTransparency .default do Meta.isDefEq sortOf candidate then
        return true
  return false

def scopedObjectsForType (governing : Array (Name × Provenance.Requirement))
    (objectType : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let mut objects := #[]
  for (_, req) in governing do
    if let .objects scopeObjects := req.scope then
      for object in scopeObjects do
        let some info := env.find? object | continue
        if ← Meta.isDefEq info.type objectType then
          if !objects.contains object then objects := objects.push object
  return objects

def sortScopeDescriptions (governing : Array (Name × Provenance.Requirement)) : String :=
  String.intercalate ", " <| (governing.map fun (_, req) =>
    match req.scope with
    | .sort s => s!"sort '{s}'"
    | .objects objects => s!"objects {names objects.toArray}"
    | .all => "all objects"
    | .decided d => s!"decided by '{d}'").toList

def sortNameForExpr (sortOf : Expr) : MetaM String := do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    if info.type.isConstOf ``PropertyKindCalculus.SortOfSystem then
      let candidate ← mkConstWithLevelParams name
      if ← withTransparency .default do Meta.isDefEq sortOf candidate then
        return toString name
  return toString (← Meta.ppExpr sortOf)

def sortMismatchRows (marks : Array ContractMark) (decl : Name) (tag : String)
    (port : NodeId) (requirementNames scopedNames : String)
    (missing : Array (Name × String)) : Array Row := Id.run do
  let mut out := #[]
  for (object, actualSort) in missing do
    let subject := s!"{decl} {tag} {port.render} for {object}"
    let line := s!"⚠ UNGOVERNED {subject} — {requirementNames} scoped to {scopedNames}; \
      '{object}' is of sort '{actualSort}'"
    out := out.push <| markedCoverageRow marks decl line subject
  return out

def sortCoverageForObjects (marks : Array ContractMark) (decl : Name) (tag : String)
    (port : NodeId) (governing : Array (Name × Provenance.Requirement))
    (requirementNames scopedNames : String) (objectType sorted : Expr)
    (scopedObjects objects : Array Name) : MetaM (Array Row) := do
  let mut covered := #[]
  let mut missing := #[]
  let mut unchecked := #[]
  let typeName := toString (← Meta.ppExpr objectType)
  for object in objects do
    if ← objectMem scopedObjects object then
      covered := covered.push object
    else
      let objectExpr ← mkConstWithLevelParams object
      let actualSort ← sortedSortOf objectType sorted objectExpr
      if ← sortMatchesRequirements governing actualSort then
        covered := covered.push object
      else if actualSort.hasFVar then
        unchecked := unchecked.push object
      else
        missing := missing.push (object, ← sortNameForExpr actualSort)
  if missing.isEmpty && unchecked.isEmpty then
    return #[⟨.ok,
      s!"[governed] {decl} {tag} {port.render} — by {requirementNames}"⟩]
  let mut rows := #[]
  if !covered.isEmpty then
    rows := rows.push ⟨.ok,
      s!"[governed] {decl} {tag} {port.render} for {names covered} — by \
        {requirementNames}"⟩
  for object in unchecked do
    let subject := s!"{decl} {tag} {port.render} for {object}"
    let line := s!"⚠ UNCHECKED {subject} — {requirementNames}: \
      the sort of a generic '{typeName}' object cannot be determined statically"
    rows := rows.push <| markedCoverageRow marks decl line subject
  return rows ++ sortMismatchRows marks decl tag port requirementNames scopedNames missing

def objectScopeCoverageRows (marks : Array ContractMark) (decl : Name) (tag : String)
    (port : NodeId) (governing : Array (Name × Provenance.Requirement))
    (requirementNames : String) : MetaM (Array Row) := do
  let mut scopedObjects : Array Name := #[]
  for (_, req) in governing do
    if let .objects objects := req.scope then
      for object in objects do
        if !scopedObjects.contains object then
          scopedObjects := scopedObjects.push object
  let groups ← objectsByType scopedObjects
  if groups.isEmpty then
    let subject := s!"{decl} {tag} {port.render}"
    return #[markedCoverageRow marks decl
      s!"⚠ UNCHECKED {subject} — {requirementNames}: \
        no scoped object resolves to a declaration" subject]
  let mut out := #[]
  for (type, objects) in groups do
    let scopedNames := names objects
    let domain ← portDomainFor port type
    match domain with
    | .noIndex =>
      let typeName := toString (← Meta.ppExpr type)
      let subject := s!"{decl} {tag} {port.render}"
      out := out.push <| markedCoverageRow marks decl
        s!"⚠ UNCHECKED {subject} — {requirementNames} scoped to {scopedNames}: \
          the result carries no '{typeName}' index" subject
    | .unresolved =>
      let typeName := toString (← Meta.ppExpr type)
      let subject := s!"{decl} {tag} {port.render}"
      out := out.push <| markedCoverageRow marks decl
        s!"⚠ UNCHECKED {subject} — {requirementNames} scoped to {scopedNames}: \
          the result's '{typeName}' object cannot be determined statically" subject
    | .only carried =>
      let mut covered := #[]
      for object in objects do
        if ← objectMem carried.toArray object then covered := covered.push object
      let mut missing := #[]
      for object in carried do
        unless ← objectMem objects object do missing := missing.push object
      if missing.isEmpty then
        out := out.push ⟨.ok,
          s!"[governed] {decl} {tag} {port.render} — by {requirementNames}"⟩
      else
        if !covered.isEmpty then
          out := out.push ⟨.ok,
            s!"[governed] {decl} {tag} {port.render} for {names covered} — by \
              {requirementNames}"⟩
        out := out ++ missingObjectRows marks decl tag port requirementNames scopedNames
          (missing.map toString)
    | .all =>
      match ← enumerableObjects type with
      | some ctors =>
        let mut covered := #[]
        let mut missing := #[]
        for ctor in ctors do
          if ← objectMem objects ctor then covered := covered.push ctor
          else missing := missing.push ctor
        if missing.isEmpty then
          out := out.push ⟨.ok,
            s!"[governed] {decl} {tag} {port.render} — by {requirementNames}"⟩
        else
          if !covered.isEmpty then
            out := out.push ⟨.ok,
              s!"[governed] {decl} {tag} {port.render} for {names covered} — by \
                {requirementNames}"⟩
          out := out ++ missingObjectRows marks decl tag port requirementNames scopedNames
            (missing.map toString)
      | none =>
        let typeName := toString (← Meta.ppExpr type)
        out := out.push ⟨.ok,
          s!"[governed] {decl} {tag} {port.render} for {scopedNames} — by \
            {requirementNames}"⟩
        out := out ++ missingObjectRows marks decl tag port requirementNames scopedNames
          #[s!"every other '{typeName}'"]
  return out

def sortCoverageByDomain (marks : Array ContractMark) (decl : Name) (tag : String)
    (port : NodeId) (governing : Array (Name × Provenance.Requirement))
    (requirementNames : String) (objectType : Expr) (domain : PortDomain) :
    MetaM (Array Row) := do
  let subject := s!"{decl} {tag} {port.render}"
  let noIndexLine := s!"⚠ UNCHECKED {subject} — {requirementNames}: \
    the result carries no object index"
  match domain with
  | .noIndex =>
    return #[markedCoverageRow marks decl noIndexLine subject]
  | .unresolved =>
    let typeName := toString (← Meta.ppExpr objectType)
    let line := s!"⚠ UNCHECKED {subject} — {requirementNames}: \
      the result's '{typeName}' object cannot be determined statically"
    return #[markedCoverageRow marks decl line subject]
  | .only _ | .all =>
    do
      let typeName := toString (← Meta.ppExpr objectType)
      let uncheckedNoSort := s!"⚠ UNCHECKED {subject} — {requirementNames}: \
        the objects of '{typeName}' declare no sort"
      let some sorted ← sortedInstanceFor objectType
        | return #[markedCoverageRow marks decl uncheckedNoSort subject]
      let scopedObjects ← scopedObjectsForType governing objectType
      let scopedNames := names scopedObjects
      let scopeDescription := sortScopeDescriptions governing
      let governedLine := s!"[governed] {decl} {tag} {port.render} — by \
        {requirementNames}"
      match domain with
      | .only carried =>
        return ← sortCoverageForObjects marks decl tag port governing requirementNames
          scopeDescription objectType sorted scopedObjects carried.toArray
      | .all =>
        Meta.withLocalDeclD `x objectType fun x => do
          let actualSort ← sortedSortOf objectType sorted x
          if ← sortMatchesRequirements governing actualSort then
            return #[⟨.ok, governedLine⟩]
          if actualSort.hasFVar then
            match ← enumerableObjects objectType with
            | some objects =>
              return ← sortCoverageForObjects marks decl tag port governing
                requirementNames scopeDescription objectType sorted scopedObjects objects
            | none =>
              let line := s!"⚠ UNCHECKED {subject} — {requirementNames}: \
                the sort of a generic '{typeName}' object cannot be determined statically"
              return #[markedCoverageRow marks decl line subject]
          else
            let some expectedSort := governing.findSome? (fun (_, req) =>
              match req.scope with
              | .sort s => some s
              | _ => none)
              | throwError "a sort-covered port has no sort scope"
            let actualSortName ← sortNameForExpr actualSort
            if scopedObjects.isEmpty then
              let line := s!"⚠ UNGOVERNED {subject} — {requirementNames} scoped to \
                sort '{expectedSort}', but '{typeName}' objects are of sort '{actualSortName}'"
              return #[markedCoverageRow marks decl line subject]
            match ← enumerableObjects objectType with
            | some objects =>
              let mut covered := #[]
              let mut missing := #[]
              for object in objects do
                if ← objectMem scopedObjects object then
                  covered := covered.push object
                else
                  missing := missing.push (object, actualSortName)
              if missing.isEmpty then
                return #[⟨.ok, governedLine⟩]
              let mut rows := #[]
              if !covered.isEmpty then
                rows := rows.push ⟨.ok,
                  s!"[governed] {decl} {tag} {port.render} for {names covered} — by \
                    {requirementNames}"⟩
              return rows ++ sortMismatchRows marks decl tag port requirementNames
                scopeDescription missing
            | none =>
              let subjectOther := s!"{decl} {tag} {port.render} for every other '{typeName}'"
              let line := s!"⚠ UNGOVERNED {subjectOther} — {requirementNames} scoped to \
                {scopeDescription}; objects are of sort '{actualSortName}'"
              let rows := #[⟨.ok,
                s!"[governed] {decl} {tag} {port.render} for {scopedNames} — by \
                  {requirementNames}"⟩]
              pure <| rows.push (markedCoverageRow marks decl line subjectOther)
      | .noIndex | .unresolved => pure #[]

def sortCoverageRows (marks : Array ContractMark) (decl : Name) (tag : String)
    (port : NodeId) (governing : Array (Name × Provenance.Requirement))
    (requirementNames : String) : MetaM (Array Row) := do
  let subject := s!"{decl} {tag} {port.render}"
  let noIndexLine := s!"⚠ UNCHECKED {subject} — {requirementNames}: \
    the result carries no object index"
  let some member := resultMember? port
    | return #[markedCoverageRow marks decl noIndexLine subject]
  let some rows ← withResultIndividualQuantity member fun binders args => do
    let objectType := args[0]!
    let bearer := args[1]!
    let domain ← bearerDomain binders bearer objectType
    match domain with
    | .noIndex => pure #[markedCoverageRow marks decl noIndexLine subject]
    | .unresolved | .only _ | .all => do
      let typeName := toString (← Meta.ppExpr objectType)
      let uncheckedNoSort := s!"⚠ UNCHECKED {subject} — {requirementNames}: \
        the objects of '{typeName}' declare no sort"
      let some sorted ← sortedInstanceFor objectType
        | return #[markedCoverageRow marks decl uncheckedNoSort subject]
      let bearerSort ← sortedSortOf objectType sorted bearer
      let governedLine := s!"[governed] {decl} {tag} {port.render} — by \
        {requirementNames}"
      if ← sortMatchesRequirements governing bearerSort then
        return #[⟨.ok, governedLine⟩]
      let stuck := bearerSort.hasFVar
      if !stuck then
        let objectRequirements := governing.filter fun (_, req) =>
          match req.scope with
          | .objects _ => true
          | .all | .sort _ | .decided _ => false
        if objectRequirements.isEmpty then
          let sortRequirements := governing.filter fun (_, req) =>
            match req.scope with
            | .sort _ => true
            | .all | .objects _ | .decided _ => false
          let scopes := sortScopeDescriptions sortRequirements
          let actualSortName ← sortNameForExpr bearerSort
          let line := s!"⚠ UNGOVERNED {subject} — {requirementNames} scoped to {scopes}, \
            but '{typeName}' objects are of sort '{actualSortName}'"
          return #[markedCoverageRow marks decl line subject]
        let objectRequirementNames := String.intercalate ", "
          (objectRequirements.map fun (_, req) => s!"'{req.name}'").toList
        return ← objectScopeCoverageRows marks decl tag port objectRequirements
          objectRequirementNames
      return ← sortCoverageByDomain marks decl tag port governing requirementNames
        objectType domain
  | return #[markedCoverageRow marks decl noIndexLine subject]
  return rows

/-- One row per produced port of every model boundary in scope. Object scopes inspect the
result `IndividualQuantity` bearer: named T-typed constants are retained, other T-typed terms
reduce to constants, and non-T applications are searched through their arguments. Reducible
projections, lets, and lambdas are followed; missing indices and unresolved bearers are
`⚠ UNCHECKED` violations unless the boundary is exempt. Sort scopes first reduce the actual
bearer's sort inside the member telescope. A definite match governs the port; a definite
mismatch falls back to object scopes or is ungoverned; a stuck sort uses the object-domain
path and may be unchecked. A `.decided` scope governs only when its `deciderProof` proves
that its decider holds for every result of the member; otherwise the port is unchecked. -/
def coverageRows (scope : Array Name) : Elab.TermElabM (Array Row × Tally) := do
  let subs ← subjects scope
  let byBoundary ← requirementsByBoundary
  let marks := kindRequirementFreeMarks (← getEnv)
  let mut out : Array Row := #[]
  let mut tally : Tally := {}
  for s in subs do
    let c ← match s.value with
      | .read c => pure c
      | .counterexample =>
        out := out.push ⟨.exempted, s!"⊘ exempted {s.decl} — counterexample"⟩
        continue
      | .unreadable cause =>
        out := out.push (s.unreadableRow cause)
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
        let mut applicable := #[]
        let mut uncheckedDecided := #[]
        for (declaration, req) in governing do
          let item := (declaration, req)
          match req.scope with
          | .decided _ =>
            if ← deciderProofCoversPort req p.node then
              applicable := applicable.push item
            else
              uncheckedDecided := uncheckedDecided.push item
          | .all | .objects _ | .sort _ => applicable := applicable.push item
        if !applicable.isEmpty then
          let requirementNames := String.intercalate ", "
            (applicable.map (fun (_, r) => s!"'{r.name}'")).toList
          if applicable.any fun (_, req) =>
            match req.scope with
            | .all | .decided _ => true
            | .objects _ | .sort _ => false then
            out := out.push ⟨.ok, s!"[governed] {s.decl} {s.tag} {p.node.render} — by \
              {requirementNames}"⟩
            continue
          if applicable.any fun (_, req) => req.scope matches .sort _ then
            out := out ++ (← sortCoverageRows marks s.decl s.tag p.node applicable
              requirementNames)
            continue
          out := out ++ (← objectScopeCoverageRows marks s.decl s.tag p.node applicable
            requirementNames)
        else if !uncheckedDecided.isEmpty then
          let requirementNames := String.intercalate ", "
            (uncheckedDecided.map (fun (_, req) => s!"'{req.name}'")).toList
          let deciderNames := String.intercalate ", "
            (uncheckedDecided.map fun (_, req) =>
              match req.scope with
              | .decided decider => s!"'{decider}'"
              | .all | .objects _ | .sort _ => "").toList
          let subject := s!"{s.decl} {s.tag} {p.node.render}"
          let line := s!"⚠ UNCHECKED {subject} — {requirementNames}: decided by \
            {deciderNames} with no valid decider proof"
          out := out.push <| markedCoverageRow marks s.decl line subject
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
  let nUnchecked := (rows.filter fun row =>
    row.verdict == .violation && row.line.startsWith "⚠ UNCHECKED").size
  let nUngoverned := nBad - nUnchecked
  let ex := if nEx > 0 then s!", {nEx} exempted" else ""
  let badParts := (if nUngoverned > 0 then [s!"{nUngoverned} UNGOVERNED"] else []) ++
    (if nUnchecked > 0 then [s!"{nUnchecked} UNCHECKED"] else [])
  let bad := String.intercalate ", " badParts
  let ports := if nBad == 0 then
      s!"{rows.size} row(s) over {t.boundaries} model boundary(ies): {nOk} governed{ex} — clean"
    else
      s!"{rows.size} row(s) over {t.boundaries} model boundary(ies): {nOk} governed{ex}, \
        {bad} — requirement-coverage violation"
  s!"{ports}\nrequirements: {t.provable} provable, {t.empirical} empirical, {t.attested} attested"

open Elab Command in
/-- `#kind_requirement_coverage ns …` — the census: every produced port of every model
boundary under the namespaces, each `[governed]` by the requirements naming it,
`⊘ exempted` by a `@[kindRequirementFree]` mark (or as a counterexample), or
`⚠ UNGOVERNED` or `⚠ UNCHECKED`; specification boundaries are listed as the subject of no
requirement. Object scopes inspect the result `IndividualQuantity` bearer: named T-typed
constants are retained, other T-typed terms reduce to constants, and non-T applications are
searched through their arguments. Reducible projections, lets, and lambdas are followed.
No object index or an unresolved bearer is an unchecked violation, unless the boundary has
an exemption mark. Objects match up to definitional equality. `.sort` requires an indexed
result and a `Sorted` instance; the census first reduces the actual result bearer's sort
inside the member telescope, then falls back to object-domain checking if it is stuck. A
definite mismatch is covered only by object scopes, and is otherwise ungoverned.
`.decided` governs only when its `deciderProof` proves that the decider holds for every
result of the member; otherwise it is unchecked. One sorted `info` message to pin, with
category tallies and the attested ratchet. Records an `AuditReceipt` for
`kind_requirement_coverage`. -/
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
message; throws while any produced port of a model boundary in scope is `⚠ UNGOVERNED` or
`⚠ UNCHECKED`. Object scopes inspect the reduced result bearer and match objects up to
definitional equality; named T-typed constants are retained, other T-typed terms reduce to
constants, and reducible wrappers are followed. An object scope must be checkable against
the result's object index. A `.sort` scope requires an index and `Sorted` instance, first
reduces the actual result bearer's sort, and falls back to object-domain checking if it is
stuck. A `.decided` scope needs a valid `deciderProof` theorem for every produced result
port or remains unchecked. Records an
`AuditReceipt` for `kind_requirement_clean` exactly when it does not fire. -/
elab "#kind_requirement_clean" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let bad := violations (← coverageRows scope).1
  unless bad.isEmpty do
    throwError "requirement coverage: {bad.size} produced port(s) no requirement governs or \
      whose object scope cannot be checked \
      — requirement-coverage violation\n{indented bad}\n\n\
      What a model's quantities must satisfy is stated as a `Provenance.Requirement` \
      governing the boundary that produces them, not as prose beside the module. Give each \
      port at issue a requirement — provable with its theorem edge or theorem, empirical \
      with its referents and gate, or attested with a reason — or, where nothing is \
      demanded of what the boundary produces, mark its declaration \
      `@[kindRequirementFree \"reason\"]` so the exemption is data the sweep can read. \
      An object scope must be checkable against the result's object index. Do \
      NOT re-pin a `#kind_requirement_coverage` report whose summary says `violation` — \
      that turns the build green and the census off."
  recordAuditReceipt "kind_requirement_clean" scope

end PropertyKindCalculus.KindRequirement

end Interface
