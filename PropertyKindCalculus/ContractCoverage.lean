/-
# ContractCoverage — the censuses over declared boundaries (M12, M15, M20, M21, M22)

A declared boundary is a `Provenance.Contract` constant, and `#kind_contracts` already sweeps
every one in scope for the consistency of what it declares. Five of the model template's
rubrics ask what a per-contract check cannot see — whether something *else* names the
boundary, or whether the boundary or its edge declares something it was free to leave out —
and each of those has a population that is a type and a per-member predicate that is
decidable. This module is their census, in the shape `#kind_examination_coverage` set
(`ExaminationCoverage.lean`, the Dimension library): one record command whose sorted `info`
message is pinned, one gate that throws and pins nothing, a declared exception where the
population has honest negatives, and an `AuditReceipt` at each success point.

  * **M12 — `#kind_relation_coverage ns …`.** A module's behavior is a measurement model
    carried as a theorem edge. The population is every `Provenance.Contract` in scope; the
    predicate is that some `Provenance.Relation` names it, on either side. Relations are walked
    *unscoped* — a theorem edge may live beside a deployment rather than beside the boundary it
    is about — and a `@[kindCounterexample]` relation is not a witness. The exception is
    `@[kindRelationFree "reason"]` on the contract: a boundary whose behavior is not a
    measurement model (pure data movement; the reference the edges are *about*), said in the
    author's words where the census reads them. Whether a named edge is *valid* is
    `#kind_relations`' question (M13, M14); this census asks only whether one exists.
  * **M15 — `#kind_mereology_coverage ns …`.** Mereology is declared per output port. The
    population is every produced port (`output` or `conditional`) of every contract in scope;
    the predicate is an `aggregations` entry for the port. There is no exception mark, because
    the `AggregationClass` vocabulary is total over the honest negatives — a port that must
    never be summed declares `.intensive`, one its parts do not determine declares
    `.wholeProper` — so "declares nothing" is exactly the finding.
  * **M21 — `#kind_inversion_coverage ns …`, the domain half.** Failure outside an inversion's
    domain is detected and reported. The population is every contract in scope that is the
    left side of an `inverts` relation — the boundary that recovers what another consumed; the
    predicate is a `conditional` port, the role Provenance gives to "produced in some cases and
    not others", with its decider named where one is. The exception is
    `@[kindInversionTotal "reason"]`: an inversion with no outside to detect.
  * **M20 and M21's ambiguity half — `#kind_wellposedness_coverage ns …`.** Where the model
    is inverted, existence and uniqueness are proved on a declared domain — or the failure of
    uniqueness is surfaced rather than resolved to whichever root the algorithm reached
    first. The population is every `inverts` edge (`Provenance.Relation`) under the scope;
    the predicate is that the edge answers for its inversion: a `wellPosed` witness with the
    `domain` it holds on, or a surfaced `ambiguity`. There is no exception mark — the two
    fields are total over the honest negatives (an inversion either has exactly one answer on
    a declared domain or it does not, and either answer is a declaration), so "declares
    neither" is exactly the finding. Whether a named witness has the claimed `∃!` (or
    negated-`∃!`) shape is `#kind_relation`'s question; this census asks only whether the
    edge declares one.
  * **M22 — `#kind_diagnostic_coverage ns …`.** The conditioning and quality outputs a
    consumer must read are part of the declared contract, not a side channel. The population
    is every `@[kindDiagnostic "what it diagnoses"]`-marked `KindOfProperty` under the
    scope; the predicate is a produced port of some declared boundary carrying the kind.
    Enrollment is the mark itself — a kind that is not a diagnostic is simply not marked, so
    there is no exception mark, and a scope with no marks records that visibly rather than
    passing in silence.

A `@[kindCounterexample]` contract is not a subject of any of the censuses; it is listed as
exempted so the census says what it skipped. A mark on a contract that satisfies the predicate
anyway is inert — the census reports the satisfaction — so a stale exemption cannot hide a
later declaration. A contract declared at node or kind types other than `String` is in the
population by type but cannot be read: M12 still decides it (the join is by declaration name)
and the other two report it `UNREADABLE` rather than silently walking past it. Import-closure
sensitive like every environment walk.
-/

module

public import Lean
public import PropertyKindCalculus.KindIncidence

-- Same-module helpers serve both the command elaborators below and runtime callers, so the
-- phase check is relaxed for this file (the module system's mixed-use escape; imports are
-- still checked and take `public meta import`).
set_option compiler.relaxedMetaCheck true

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.ContractCoverage

open Lean Meta
open PropertyKindCalculus.KindIncidence (contractSweepSubjects relationValueOf contractValueOf)

/-! ## The declared marks — two exceptions, one enrollment -/

/-- One declared mark: the declaration (resolved, so it cannot dangle) and the author's
words — the reason a boundary is outside an obligation, or what a diagnostic kind
diagnoses. -/
structure ContractMark where
  /-- The marked declaration. -/
  decl : Name
  /-- The author's words: why, or what. -/
  reason : String
  deriving Repr, Inhabited, BEq

/-- `@[kindRelationFree …]`-marked contracts. -/
initialize kindRelationFreeExt :
    SimplePersistentEnvExtension ContractMark (Array ContractMark) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-- `@[kindInversionTotal …]`-marked contracts. -/
initialize kindInversionTotalExt :
    SimplePersistentEnvExtension ContractMark (Array ContractMark) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-- `@[kindRelationFree "<reason>"]` — declare that a boundary legitimately has no theorem
edge: its behavior is not a measurement model. -/
syntax (name := kindRelationFreeAttr) "kindRelationFree " str : attr

/-- `@[kindInversionTotal "<reason>"]` — declare that an inverted boundary legitimately has no
conditional port: the inversion is total on its input type. -/
syntax (name := kindInversionTotalAttr) "kindInversionTotal " str : attr

/-- `@[kindDiagnostic "<what it diagnoses>"]`-marked kinds. -/
initialize kindDiagnosticExt :
    SimplePersistentEnvExtension ContractMark (Array ContractMark) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-- `@[kindDiagnostic "<what it diagnoses>"]` — declare a `KindOfProperty` to be a quality or
conditioning output a consumer must read. The mark enrolls the kind in
`#kind_diagnostic_coverage`: some declared boundary in scope must carry it on a produced
port, or the kind is a side channel. -/
syntax (name := kindDiagnosticAttr) "kindDiagnostic " str : attr

/-- The check both marks share: the target is a `Provenance.Contract` and the reason is not
blank. -/
private def checkContractMark (attr : String) (decl : Name) (reason : String) :
    AttrM Unit := do
  let env ← getEnv
  let some info := env.find? decl
    | throwError "`@[{attr}]` could not find '{decl}' in the environment"
  unless info.type.getAppFn.isConstOf ``PropertyKindCalculus.Provenance.Contract do
    throwError "`@[{attr}]` expects a 'Provenance.Contract' — '{decl}' is not one. The mark \
      exempts a declared boundary from a census over declared boundaries, so that is where \
      it goes."
  if reason.all Char.isWhitespace then
    throwError "`@[{attr}]` on '{decl}' needs a reason: an exemption without one is the \
      docstring problem in a new place"

initialize registerBuiltinAttribute {
  name  := `kindRelationFreeAttr
  descr := "A boundary declared edge-free on purpose: `#kind_relation_coverage` lists it \
    as exempted instead of gating on it."
  add   := fun decl stx _kind => do
    match stx with
    | `(attr| kindRelationFree $reason:str) =>
        checkContractMark "kindRelationFree" decl reason.getString
        modifyEnv fun env =>
          kindRelationFreeExt.addEntry env { decl, reason := reason.getString }
    | _ => throwError "invalid `kindRelationFree` attribute; expected \
        `kindRelationFree \"<reason>\"`"
}

initialize registerBuiltinAttribute {
  name  := `kindInversionTotalAttr
  descr := "An inverted boundary declared total on purpose: `#kind_inversion_coverage` \
    lists it as exempted instead of gating on it."
  add   := fun decl stx _kind => do
    match stx with
    | `(attr| kindInversionTotal $reason:str) =>
        checkContractMark "kindInversionTotal" decl reason.getString
        modifyEnv fun env =>
          kindInversionTotalExt.addEntry env { decl, reason := reason.getString }
    | _ => throwError "invalid `kindInversionTotal` attribute; expected \
        `kindInversionTotal \"<reason>\"`"
}

initialize registerBuiltinAttribute {
  name  := `kindDiagnosticAttr
  descr := "A quality or conditioning kind a consumer must read: \
    `#kind_diagnostic_coverage` asks the declared boundaries in scope for a produced \
    port carrying it."
  add   := fun decl stx _kind => do
    match stx with
    | `(attr| kindDiagnostic $reason:str) => do
        let env ← getEnv
        let some info := env.find? decl
          | throwError "`@[kindDiagnostic]` could not find '{decl}' in the environment"
        unless info.type.isConstOf ``PropertyKindCalculus.KindOfProperty do
          throwError "`@[kindDiagnostic]` expects a 'KindOfProperty' — '{decl}' is not \
            one. The mark declares a *kind* to be a quality or conditioning output, and \
            the census then asks the boundaries for a port at that kind."
        if reason.getString.all Char.isWhitespace then
          throwError "`@[kindDiagnostic]` on '{decl}' needs to say what the kind \
            diagnoses: a diagnostic no one can interpret is the side channel again"
        modifyEnv fun env =>
          kindDiagnosticExt.addEntry env { decl, reason := reason.getString }
    | _ => throwError "invalid `kindDiagnostic` attribute; expected \
        `kindDiagnostic \"<what it diagnoses>\"`"
}

/-- Every `@[kindRelationFree]` mark in the environment. -/
def kindRelationFreeMarks (env : Environment) : Array ContractMark :=
  kindRelationFreeExt.getState env

/-- Every `@[kindInversionTotal]` mark in the environment. -/
def kindInversionTotalMarks (env : Environment) : Array ContractMark :=
  kindInversionTotalExt.getState env

/-- Every `@[kindDiagnostic]` mark in the environment. -/
def kindDiagnosticMarks (env : Environment) : Array ContractMark :=
  kindDiagnosticExt.getState env

/-! ## The population and the joins -/

/-- A declared boundary as the censuses read it. -/
structure Subject where
  /-- The `Provenance.Contract` declaration. -/
  decl : Name
  /-- Its value, or `none` when the constant is a `Provenance.Contract` at node or kind
  types other than `NodeId`/`KindRef` and cannot be read as one. -/
  value? : Option (Provenance.Contract Provenance.NodeId Provenance.KindRef)
  /-- `@[kindCounterexample]`-marked: not a subject, listed as exempted. -/
  counterexample : Bool

/-- Every `Provenance.Contract` under the scope — `#kind_contracts`' own population
(`contractSweepSubjects`), the counterexamples included and flagged. -/
def subjects (scope : Array Name) : Elab.TermElabM (Array Subject) := do
  let (names, exempted) ← contractSweepSubjects scope
  let mut out : Array Subject := #[]
  for n in names do
    let value? ← try some <$> contractValueOf n catch _ => pure none
    out := out.push { decl := n, value?, counterexample := false }
  for n in exempted do
    out := out.push { decl := n, value? := none, counterexample := true }
  return out

/-- The boundary's declared name, quoted, or `(?)` when the value cannot be read. -/
def Subject.tag (s : Subject) : String :=
  match s.value? with
  | some c => s!"('{c.name}')"
  | none   => "(?)"

/-- Every theorem edge in the environment that is not a counterexample, with its value, sorted
by declaration. **Unscoped**: a theorem edge may live beside a deployment rather than beside
the boundary it is about, so only the contracts are scoped (`Index.edgesByContract`'s rule). -/
def relationEntries : MetaM (Array (Name × Provenance.Relation)) := do
  let env ← getEnv
  let exempt : NameSet :=
    (BoundaryAudit.kindCounterexamples env).foldl (init := {}) (·.insert ·)
  let mut out : Array (Name × Provenance.Relation) := #[]
  for (n, info) in env.constants.toList do
    if n.isInternal || exempt.contains n then continue
    unless info.type.isConstOf ``PropertyKindCalculus.Provenance.Relation do continue
    out := out.push (n, ← relationValueOf n)
  return out.qsort fun a b => a.1.toString < b.1.toString

/-- The witness join: contract declaration name → the edges naming it, on either side. -/
def edgesByContract : MetaM (Std.HashMap Name (Array Name)) := do
  let mut acc : Std.HashMap Name (Array Name) := {}
  for (n, rel) in ← relationEntries do
    for side in [rel.left, rel.right] do
      acc := acc.insert side ((acc.getD side #[]).push n)
  return acc

/-- The inversion join: contract declaration name → the `inverts` edges whose *left* side it
is — the boundaries that recover what another consumed. -/
def invertersByContract : MetaM (Std.HashMap Name (Array Name)) := do
  let mut acc : Std.HashMap Name (Array Name) := {}
  for (n, rel) in ← relationEntries do
    match rel.kind with
    | .inverts => acc := acc.insert rel.left ((acc.getD rel.left #[]).push n)
    | _ => pure ()
  return acc

/-! ## Rows -/

/-- The verdict on one member. -/
inductive Verdict where
  | ok | exempted | violation
  deriving DecidableEq, Repr, Inhabited

/-- One audited member: its verdict and its report line. Lines sort so that the `[…]` rows
come first, then `⊘`, then `⚠`. -/
structure Row where
  /-- The verdict. -/
  verdict : Verdict
  /-- The report line. -/
  line : String
  deriving Repr, Inhabited

/-- Count the rows with a verdict. -/
def count (rows : Array Row) (v : Verdict) : Nat :=
  rows.foldl (fun n r => if r.verdict == v then n + 1 else n) 0

/-- The rows as the report body, sorted. -/
def body (rows : Array Row) : String :=
  String.intercalate "\n" ((rows.map (·.line)).qsort (· < ·)).toList

/-- The violations, for a gate's error. -/
def violations (rows : Array Row) : Array Row := rows.filter (·.verdict == .violation)

/-- The violations as a gate renders them: the sorted body, each line indented. -/
def indented (rows : Array Row) : String :=
  body (rows.map fun r => { r with line := s!"  {r.line}" })

def names (ns : Array Name) : String :=
  String.intercalate ", " (ns.map toString).toList

/-! ## M12 — relation coverage -/

/-- One row per declared boundary: witnessed by the edges naming it, exempted, or
`UNWITNESSED`. -/
def relationRows (scope : Array Name) : Elab.TermElabM (Array Row) := do
  let subs ← subjects scope
  let edges ← edgesByContract
  let marks := kindRelationFreeMarks (← getEnv)
  let mut out : Array Row := #[]
  for s in subs do
    if s.counterexample then
      out := out.push ⟨.exempted, s!"⊘ exempted {s.decl} — counterexample"⟩
      continue
    let es := edges.getD s.decl #[]
    if !es.isEmpty then
      out := out.push ⟨.ok, s!"[witnessed] {s.decl} {s.tag} — edges: {names es}"⟩
    else match marks.find? (·.decl == s.decl) with
      | some m => out := out.push ⟨.exempted, s!"⊘ exempted {s.decl} {s.tag} — {m.reason}"⟩
      | none   => out := out.push ⟨.violation, s!"⚠ UNWITNESSED {s.decl} {s.tag}"⟩
  return out

/-- The summary line: the counts, and `clean` exactly when no row is a violation. -/
def relationSummary (rows : Array Row) : String :=
  let (nOk, nEx, nBad) := (count rows .ok, count rows .exempted, count rows .violation)
  let ex := if nEx > 0 then s!", {nEx} exempted" else ""
  if nBad == 0 then s!"{rows.size} boundary(ies): {nOk} witnessed{ex} — clean"
  else s!"{rows.size} boundary(ies): {nOk} witnessed{ex}, {nBad} UNWITNESSED \
    — relation-coverage violation"

open Elab Command in
/-- `#kind_relation_coverage ns …` — the census behind M12: every declared boundary under the
namespaces, each `[witnessed]` by the theorem edges naming it, `⊘ exempted` by a
`@[kindRelationFree]` mark (or as a counterexample), or `⚠ UNWITNESSED`. One sorted `info`
message to pin. Records an `AuditReceipt` for `kind_relation_coverage`. -/
elab "#kind_relation_coverage" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let rows ← relationRows scope
  recordAuditReceipt "kind_relation_coverage" scope
  if rows.isEmpty then
    logInfo m!"relation coverage — no declared boundaries in the given namespaces"
    return
  logInfo m!"relation coverage:\n{body rows}\n{relationSummary rows}"

open Elab Command in
/-- `#kind_relation_clean ns …` — **the invariant, stated apart from the record.** No message;
throws while any declared boundary in scope is `⚠ UNWITNESSED`. Records an `AuditReceipt` for
`kind_relation_clean` exactly when it does not fire. -/
elab "#kind_relation_clean" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let bad := violations (← relationRows scope)
  unless bad.isEmpty do
    throwError "relation coverage: {bad.size} declared boundary(ies) no theorem edge names \
      — relation-coverage violation\n{indented bad}\n\n\
      A module's behavior is a measurement model carried as a theorem edge, not prose beside the module. Give each boundary at issue a `Provenance.Relation` naming it (left \
      or right) with its witness theorem, or — where its behavior is not a measurement model \
      (pure data movement; the reference an edge is about) — mark its declaration \
      `@[kindRelationFree \"reason\"]` so the exemption is data the sweep can read. Do NOT \
      re-pin a `#kind_relation_coverage` report whose summary says `violation` — that turns \
      the build green and the census off."
  recordAuditReceipt "kind_relation_clean" scope

/-! ## M15 — mereology coverage -/

/-- One row per produced port: `[classed]` by its aggregation class or `⚠ UNDECLARED`; one row
per exempted or unreadable boundary. -/
def mereologyRows (scope : Array Name) : Elab.TermElabM (Array Row) := do
  let mut out : Array Row := #[]
  for s in ← subjects scope do
    if s.counterexample then
      out := out.push ⟨.exempted, s!"⊘ exempted {s.decl} — counterexample"⟩
      continue
    let some c := s.value?
      | out := out.push ⟨.violation,
          s!"⚠ UNREADABLE {s.decl} — not a `Contract NodeId KindRef`"⟩
        continue
    for p in c.ports do
      unless p.dir.produced do continue
      match c.aggregations.find? (·.1 == p.node) with
      | some (_, a) =>
        out := out.push ⟨.ok, s!"[classed] {s.decl} :: {p.node.render} : {p.kind.render} — {a.label}"⟩
      | none =>
        out := out.push ⟨.violation, s!"⚠ UNDECLARED {s.decl} :: {p.node.render} : {p.kind.render}"⟩
  return out

/-- The summary line: ports counted, exempted boundaries beside them, `clean` exactly when no
row is a violation. -/
def mereologySummary (rows : Array Row) : String :=
  let nOk := count rows .ok
  let nEx := count rows .exempted
  let bad := violations rows
  let nUnread := (bad.filter (·.line.startsWith "⚠ UNREADABLE")).size
  let nUndecl := bad.size - nUnread
  let ports := nOk + nUndecl
  let ex := if nEx > 0 then s!"; {nEx} boundary(ies) exempted" else ""
  let unread := if nUnread > 0 then s!"; {nUnread} UNREADABLE" else ""
  if bad.isEmpty then s!"{ports} produced port(s): {nOk} classed{ex} — clean"
  else s!"{ports} produced port(s): {nOk} classed, {nUndecl} UNDECLARED{ex}{unread} \
    — mereology-coverage violation"

open Elab Command in
/-- `#kind_mereology_coverage ns …` — the census behind M15: every produced port of every
declared boundary under the namespaces, each `[classed]` by its declared aggregation class or
`⚠ UNDECLARED`. One sorted `info` message to pin. Records an `AuditReceipt` for
`kind_mereology_coverage`. -/
elab "#kind_mereology_coverage" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let subs ← subjects scope
  let rows ← mereologyRows scope
  recordAuditReceipt "kind_mereology_coverage" scope
  if subs.isEmpty then
    logInfo m!"mereology coverage — no declared boundaries in the given namespaces"
    return
  if rows.isEmpty then
    logInfo m!"mereology coverage — no produced ports in the given namespaces"
    return
  logInfo m!"mereology coverage:\n{body rows}\n{mereologySummary rows}"

open Elab Command in
/-- `#kind_mereology_clean ns …` — **the invariant, stated apart from the record.** No message;
throws while any produced port in scope is `⚠ UNDECLARED` (or a boundary `UNREADABLE`).
Records an `AuditReceipt` for `kind_mereology_clean` exactly when it does not fire. -/
elab "#kind_mereology_clean" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let bad := violations (← mereologyRows scope)
  unless bad.isEmpty do
    throwError "mereology coverage: {bad.size} produced port(s) with no mereology declaration \
      — mereology-coverage violation\n{indented bad}\n\n\
      A license to shard or recarve is derived from the port's declared aggregation class, not from the fact that a sharded run worked. Add an `aggregations` entry for \
      each port at issue — `.intensive` for a value that must never be summed over a carving, \
      `.wholeProper` for one its parts do not determine, `.extensive` (or a qualified class) \
      where it composes. There is no exemption mark: the vocabulary already names every \
      honest negative. Do NOT re-pin a `#kind_mereology_coverage` report whose summary says \
      `violation` — that turns the build green and the census off."
  recordAuditReceipt "kind_mereology_clean" scope

/-! ## M21 — inversion coverage (the domain half) -/

/-- The conditional ports of a contract, each with its decider where one is named. -/
def guards (c : Provenance.Contract Provenance.NodeId Provenance.KindRef) :
    List String :=
  c.ports.filterMap fun p =>
    if p.dir matches .conditional then
      some (match c.deciders.find? (·.1 == p.node) with
        | some (_, d) => s!"{p.node.render} (decider: {d})"
        | none        => p.node.render)
    else none

/-- One row per inverted boundary — a contract that is the left side of an `inverts` edge:
`[guarded]` by its conditional ports, exempted, or `⚠ UNGUARDED`. -/
def inversionRows (scope : Array Name) : Elab.TermElabM (Array Row) := do
  let inverters ← invertersByContract
  let marks := kindInversionTotalMarks (← getEnv)
  let mut out : Array Row := #[]
  for s in ← subjects scope do
    let by_ := inverters.getD s.decl #[]
    if by_.isEmpty then continue
    let via := s!"inverted by: {names by_}"
    if s.counterexample then
      out := out.push ⟨.exempted, s!"⊘ exempted {s.decl} — counterexample; {via}"⟩
      continue
    let some c := s.value?
      | out := out.push ⟨.violation,
          s!"⚠ UNREADABLE {s.decl} — not a `Contract NodeId KindRef`; {via}"⟩
        continue
    let gs := guards c
    if !gs.isEmpty then
      out := out.push ⟨.ok,
        s!"[guarded] {s.decl} {s.tag} — conditional {String.intercalate ", " gs}; {via}"⟩
    else match marks.find? (·.decl == s.decl) with
      | some m =>
        out := out.push ⟨.exempted, s!"⊘ exempted {s.decl} {s.tag} — {m.reason}; {via}"⟩
      | none => out := out.push ⟨.violation, s!"⚠ UNGUARDED {s.decl} {s.tag} — {via}"⟩
  return out

/-- The summary line. -/
def inversionSummary (rows : Array Row) : String :=
  let (nOk, nEx, nBad) := (count rows .ok, count rows .exempted, count rows .violation)
  let ex := if nEx > 0 then s!", {nEx} exempted" else ""
  if nBad == 0 then s!"{rows.size} inverted boundary(ies): {nOk} guarded{ex} — clean"
  else s!"{rows.size} inverted boundary(ies): {nOk} guarded{ex}, {nBad} UNGUARDED \
    — inversion-coverage violation"

open Elab Command in
/-- `#kind_inversion_coverage ns …` — the census behind M21's domain half: every declared
boundary under the namespaces that an `inverts` edge names as its left side, each `[guarded]`
by a `conditional` port (with its decider where named), `⊘ exempted` by a
`@[kindInversionTotal]` mark, or `⚠ UNGUARDED`. One sorted `info` message to pin. Records an
`AuditReceipt` for `kind_inversion_coverage`. -/
elab "#kind_inversion_coverage" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let rows ← inversionRows scope
  recordAuditReceipt "kind_inversion_coverage" scope
  if rows.isEmpty then
    logInfo m!"inversion coverage — no inverted boundaries in the given namespaces"
    return
  logInfo m!"inversion coverage:\n{body rows}\n{inversionSummary rows}"

open Elab Command in
/-- `#kind_inversion_clean ns …` — **the invariant, stated apart from the record.** No message;
throws while any inverted boundary in scope is `⚠ UNGUARDED`. Records an `AuditReceipt` for
`kind_inversion_clean` exactly when it does not fire. -/
elab "#kind_inversion_clean" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let bad := violations (← inversionRows scope)
  unless bad.isEmpty do
    throwError "inversion coverage: {bad.size} inverted boundary(ies) with no declared \
      out-of-domain behavior — inversion-coverage violation\n{indented bad}\n\n\
      An inversion has a domain, and failure outside it is detected at the interface, not \
      carried in a constructor choice no boundary can see. Give each boundary at issue a \
      `conditional` port for the value it produces only inside the domain, and name the \
      predicate that decides it in `deciders`; or — where the inversion is total on its input \
      type — mark its declaration `@[kindInversionTotal \"reason\"]` so the exemption is data \
      the sweep can read. Do NOT re-pin a `#kind_inversion_coverage` report whose summary \
      says `violation` — that turns the build green and the census off."
  recordAuditReceipt "kind_inversion_clean" scope

/-! ## M20 and M21's ambiguity half — well-posedness coverage -/

/-- One row per `inverts` edge under the scope: `[well-posed]` by its witness and domain,
`[surfaced]` by its ambiguity witness, `⊘ exempted` as a counterexample, or `⚠ UNDECIDED`.
A `wellPosed` with no `domain` does not count as well-posed — existence and uniqueness are
proved on a declared domain — and `#kind_relation` refuses the combination outright. -/
def wellPosednessRows (scope : Array Name) : Elab.TermElabM (Array Row) := do
  let env ← getEnv
  let exempt : NameSet :=
    (BoundaryAudit.kindCounterexamples env).foldl (init := {}) (·.insert ·)
  let mut out : Array Row := #[]
  for (n, info) in env.constants.toList do
    if n.isInternal then continue
    unless scope.any (·.isPrefixOf n) do continue
    unless info.type.isConstOf ``PropertyKindCalculus.Provenance.Relation do continue
    let rel ← relationValueOf n
    unless rel.kind matches .inverts do continue
    if exempt.contains n then
      out := out.push ⟨.exempted, s!"⊘ exempted {n} — counterexample"⟩
    else if !rel.wellPosed.isAnonymous && !rel.domain.isAnonymous then
      let amb := if rel.ambiguity.isAnonymous then "" else s!"; ambiguity: {rel.ambiguity}"
      out := out.push ⟨.ok, s!"[well-posed] {n} — {rel.wellPosed} on {rel.domain}{amb}"⟩
    else if !rel.ambiguity.isAnonymous then
      out := out.push ⟨.ok, s!"[surfaced] {n} — ambiguity: {rel.ambiguity}"⟩
    else
      out := out.push ⟨.violation,
        s!"⚠ UNDECIDED {n} — '{rel.left}' inverts '{rel.right}', no well-posedness \
          witness, no surfaced ambiguity"⟩
  return out

/-- The summary line: the counts, and `clean` exactly when no row is a violation. -/
def wellPosednessSummary (rows : Array Row) : String :=
  let nWp := (rows.filter (·.line.startsWith "[well-posed]")).size
  let nSf := (rows.filter (·.line.startsWith "[surfaced]")).size
  let nEx := count rows .exempted
  let bad := violations rows
  let ex := if nEx > 0 then s!", {nEx} exempted" else ""
  if bad.isEmpty then
    s!"{rows.size} inverts edge(s): {nWp} well-posed, {nSf} ambiguity surfaced{ex} — clean"
  else
    s!"{rows.size} inverts edge(s): {nWp} well-posed, {nSf} ambiguity surfaced{ex}, \
      {bad.size} UNDECIDED — well-posedness-coverage violation"

open Elab Command in
/-- `#kind_wellposedness_coverage ns …` — the census behind M20 and M21's ambiguity half:
every `inverts` edge under the namespaces, each `[well-posed]` by a `wellPosed` witness with
the `domain` it holds on, `[surfaced]` by an `ambiguity` witness, or `⚠ UNDECIDED`. There is
no exception mark: the two fields are total over the honest negatives. One sorted `info`
message to pin. Records an `AuditReceipt` for `kind_wellposedness_coverage`. -/
elab "#kind_wellposedness_coverage" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let rows ← wellPosednessRows scope
  recordAuditReceipt "kind_wellposedness_coverage" scope
  if rows.isEmpty then
    logInfo m!"well-posedness coverage — no inverts edges in the given namespaces"
    return
  logInfo m!"well-posedness coverage:\n{body rows}\n{wellPosednessSummary rows}"

open Elab Command in
/-- `#kind_wellposedness_clean ns …` — **the invariant, stated apart from the record.** No
message; throws while any `inverts` edge in scope is `⚠ UNDECIDED`. Records an
`AuditReceipt` for `kind_wellposedness_clean` exactly when it does not fire. -/
elab "#kind_wellposedness_clean" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let bad := violations (← wellPosednessRows scope)
  unless bad.isEmpty do
    throwError "well-posedness coverage: {bad.size} inverts edge(s) with neither a \
      well-posedness witness nor a surfaced ambiguity — well-posedness-coverage \
      violation\n{indented bad}\n\n\
      An inversion either has exactly one answer on a declared domain or it does not, and \
      the edge records which. Give each edge at issue a `wellPosed` witness — a sorry-free \
      theorem concluding with `∃!` — together with the `domain` declaration its statement \
      mentions; or name in `ambiguity` the theorem concluding with the negation of an `∃!` \
      that surfaces the collision, so non-uniqueness is data a consumer can read rather \
      than a root the algorithm happened to reach. There is no exemption mark: either \
      answer is a declaration. Do NOT re-pin a `#kind_wellposedness_coverage` report whose \
      summary says `violation` — that turns the build green and the census off."
  recordAuditReceipt "kind_wellposedness_clean" scope

/-! ## M22 — diagnostic coverage -/

/-- One row per `@[kindDiagnostic]`-marked kind under the scope: `[exported]` by the
produced ports carrying it, or `⚠ SIDECHANNELED`; one `⚠ UNREADABLE` row per boundary
whose ports cannot be read (its ports cannot witness an export). Counterexample
boundaries witness nothing. Empty when no kind in scope is marked — the census is
enrolled by the mark, so an unmarked vocabulary reads empty *visibly*, in the record a
conforming document pins. -/
def diagnosticRows (scope : Array Name) : Elab.TermElabM (Array Row) := do
  let marks := (kindDiagnosticMarks (← getEnv)).filter
    (fun m => scope.any (·.isPrefixOf m.decl))
  if marks.isEmpty then return #[]
  let subs ← subjects scope
  let mut out : Array Row := #[]
  for s in subs do
    if s.counterexample then continue
    if s.value?.isNone then
      out := out.push ⟨.violation,
        s!"⚠ UNREADABLE {s.decl} — not a `Contract NodeId KindRef`"⟩
  for m in marks.qsort (fun a b => a.decl.toString < b.decl.toString) do
    -- exact: a port states its kind by the name the environment resolves, which is the
    -- same name the mark carries — two marks whose names merely share a suffix cannot
    -- credit one another
    let mut hits : Array String := #[]
    for s in subs do
      if s.counterexample then continue
      let some c := s.value? | continue
      for p in c.ports do
        unless p.dir.produced do continue
        if p.kind == .decl m.decl then
          hits := hits.push s!"{s.decl} :: {p.node.render}"
    if hits.isEmpty then
      out := out.push ⟨.violation,
        s!"⚠ SIDECHANNELED {m.decl} ({m.reason}) — no produced port in scope carries it"⟩
    else
      out := out.push ⟨.ok,
        s!"[exported] {m.decl} — {String.intercalate ", " (hits.qsort (· < ·)).toList}"⟩
  return out

/-- The summary line: the counts, and `clean` exactly when no row is a violation. -/
def diagnosticSummary (rows : Array Row) : String :=
  let nOk := count rows .ok
  let bad := violations rows
  let nUnread := (bad.filter (·.line.startsWith "⚠ UNREADABLE")).size
  let nSide := bad.size - nUnread
  let kinds := nOk + nSide
  let unread := if nUnread > 0 then s!"; {nUnread} UNREADABLE" else ""
  if bad.isEmpty then s!"{kinds} diagnostic kind(s): {nOk} exported — clean"
  else s!"{kinds} diagnostic kind(s): {nOk} exported, {nSide} SIDECHANNELED{unread} \
    — diagnostic-coverage violation"

open Elab Command in
/-- `#kind_diagnostic_coverage ns …` — the census behind M22: every
`@[kindDiagnostic]`-marked kind under the namespaces, each `[exported]` by the produced
ports carrying it or `⚠ SIDECHANNELED`. Enrollment is the mark itself, so there is no
exception mark — a kind that is not a quality or conditioning output is simply not
marked — and a scope with no marks records that visibly rather than passing in silence.
One sorted `info` message to pin. Records an `AuditReceipt` for
`kind_diagnostic_coverage`. -/
elab "#kind_diagnostic_coverage" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let rows ← diagnosticRows scope
  recordAuditReceipt "kind_diagnostic_coverage" scope
  if rows.isEmpty then
    logInfo m!"diagnostic coverage — no diagnostic kinds declared in the given namespaces"
    return
  logInfo m!"diagnostic coverage:\n{body rows}\n{diagnosticSummary rows}"

open Elab Command in
/-- `#kind_diagnostic_clean ns …` — **the invariant, stated apart from the record.** No
message; throws while any diagnostic kind in scope is `⚠ SIDECHANNELED` (or a boundary
`UNREADABLE`). Records an `AuditReceipt` for `kind_diagnostic_clean` exactly when it does
not fire. -/
elab "#kind_diagnostic_clean" nss:ident+ : command => liftTermElabM do
  let scope := nss.map (·.getId)
  let bad := violations (← diagnosticRows scope)
  unless bad.isEmpty do
    throwError "diagnostic coverage: {bad.size} diagnostic kind(s) no declared boundary \
      exports — diagnostic-coverage violation\n{indented bad}\n\n\
      A quality or conditioning output a consumer must read is part of the declared \
      contract, not a side channel a downstream stage may or may not read. Give some \
      boundary in scope a produced port at each kind at issue — `conditional` where the \
      value exists only in some cases, with its decider named — or, where the kind is \
      not in fact a diagnostic a consumer needs, remove its `@[kindDiagnostic]` mark: \
      enrollment is the mark, so the mark is also the exemption. Do NOT re-pin a \
      `#kind_diagnostic_coverage` report whose summary says `violation` — that turns \
      the build green and the census off."
  recordAuditReceipt "kind_diagnostic_clean" scope

end PropertyKindCalculus.ContractCoverage

end -- pkc-blanket-expose
end -- pkc-blanket
