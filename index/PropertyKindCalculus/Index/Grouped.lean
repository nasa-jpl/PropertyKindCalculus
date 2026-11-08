/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
module
public import PropertyKindCalculus.Index.Ontology
public import PropertyKindCalculus.Index.Contracts
public import PropertyKindCalculus.ModuleCard

/-!
# The grouped kind view — kinds read through the boundaries that carry them

The `kinds` census is alphabetical: the lookup surface, and the denominator every partition
claim is checked against. It answers "what is this kind?" and not "where does it enter?". The
tables here answer the second question from the same environment, by **joining the census to
the declared `Provenance.Contract`s**: a port states its kind by declaration name (`KindRef.decl`),
so every kind a boundary carries is a row of this join, with the boundary and the port's role.

The join is **restricted to the census**: a contract in scope may state a kind declared outside
it (a shared upstream kind, a kind of another layer), and such a port binds nothing here — the
rows of every table below are census kinds, which is what lets the grouped view and the
absences partition the census exactly. A document wanting the external kinds reads the
`contracts` table, where the interface is rendered whole.

Three readings, one join:

* `kinds-by-boundary` — the grouped reading: boundary, then role (in the module card's reading
  order: inputs, parameters, configuration, outputs), then kind. A document that partitions its
  boundaries into subsystems passes the partition as named scopes and gets a leading
  *Subsystem* column; the assignment is the document's, the rows are the environment's.
* `kinds-in-context` — the census with two **context columns**: which boundaries carry the kind
  and in which roles. Same rows, same order as `kinds`, so it can replace the census in a
  document without disturbing what the census pins.
* `kinds-unbound` — the census kinds **no** declared boundary carries. Rendered as a table of
  absences, like `provenance-coverage`: its row count is the partition's remainder, and
  `#pkc_kinds_partition` states the whole claim — census = bound + unbound — as one line a
  probe can pin.

Like the `contracts` table, `@[kindCounterexample]`-tagged contracts are not sources: a
deliberate misdeclaration binds no kind.
-/

@[expose] public section Blanket

namespace PropertyKindCalculus.Index

open Lean Meta
open PropertyKindCalculus.KindIncidence (contractValueOf)

/-- The kind declarations a kind reference names: a `decl` names one, a `sig` or `tuple` the
declarations of its components, and a binder, an unkinded constant or a rendering none. -/
partial def kindRefDecls : Provenance.KindRef → Array Name
  | .decl n => #[n]
  | .sig cs | .tuple cs => cs.foldl (fun acc c => acc ++ kindRefDecls c) #[]
  | _ => #[]

/-- A port role's label, from the module card's role groups — the one vocabulary for roles in
reading order, so the table and the card cannot disagree. -/
def roleLabel (d : Provenance.PortDir) : String :=
  ((ModuleCard.roleGroups.find? fun (_, ds) => ds.contains d).map (·.1)).getD "other"

/-- A port role's position in the module card's reading order, for sorting. -/
def roleRank (d : Provenance.PortDir) : Nat :=
  (ModuleCard.roleGroups.findIdx? fun (_, ds) => ds.contains d).getD ModuleCard.roleGroups.length

/-- One row of the join: a declared boundary's port and the kind declaration it carries. -/
structure KindBinding where
  /-- The contract declaration. -/
  contract : Name
  /-- The boundary's rendered name, `Contract.name`. -/
  boundary : String
  /-- The port's role. -/
  dir : Provenance.PortDir
  /-- The port's address. -/
  node : Provenance.NodeId
  /-- The kind declaration the port states. -/
  kind : Name
deriving Repr, Inhabited

/-- Every (boundary, port, kind) binding declared in scope whose kind is in `layer`'s census in
scope — the join the three tables and the partition read. A port kind outside the census (declared
elsewhere, or of another layer) binds nothing. Counterexample contracts are excluded, as in the
`contracts` table. A kind a signature states more than once (`k → k`) is one binding of that port,
not two. -/
def kindBindings (layer : KindLayer) (scope : Scope) : MetaM (Array KindBinding) := do
  let env ← getEnv
  let census : NameSet := (constantsOfType env layer.ty scope).foldl (init := {}) (·.insert ·)
  let exempt : NameSet :=
    (BoundaryAudit.kindCounterexamples env).foldl (init := {}) (·.insert ·)
  let mut out : Array KindBinding := #[]
  for n in constantsOfType env ``PropertyKindCalculus.Provenance.Contract scope do
    if exempt.contains n then continue
    let c ← contractValueOf n
    for p in c.ports do
      for k in (kindRefDecls p.kind).toList.eraseDups do
        unless census.contains k do continue
        out := out.push { contract := n, boundary := c.name, dir := p.dir, node := p.node, kind := k }
  return out

/-- The dedicated kinds in scope, by the kind-of-property each is built on. -/
def dedicatedByKind (env : Environment) (scope : Scope) : MetaM (Std.HashMap Name (Array Name)) := do
  let mut acc : Std.HashMap Name (Array Name) := {}
  for d in constantsOfType env ``PropertyKindCalculus.DedicatedKind scope do
    if let some k ← fieldDecl? d ``PropertyKindCalculus.DedicatedKind.kind then
      acc := acc.insert k ((acc.getD k #[]).push d)
  return acc

/-- The index of the first group whose scope covers `n`, or `groups.size` for none — the
unassigned contracts sort last. A group with an empty scope covers nothing here, because the
empty scope's "everything" reading would swallow every later group. -/
def groupIndex (groups : Array (String × Scope)) (n : Name) : Nat :=
  (groups.findIdx? fun (_, s) => !s.isEmpty && s.covers n).getD groups.size

/-- The `kinds-by-boundary` table: one row per census kind of `layer` a declared boundary's port
carries, ordered
by boundary, then role (inputs, parameters, configuration, outputs), then kind, then port. With
`groups`, a leading *Subsystem* column assigns each boundary to the first group whose scope
covers its declaration (unassigned ones render `—` and sort last). The *Dedicated to* column
links the dedicated kinds built on the kind, where the scope declares any. -/
def kindsByBoundaryTable (layer : KindLayer) (scope : Scope)
    (groups : Array (String × Scope) := #[]) : MetaM IndexTable := do
  let env ← getEnv
  let grouped := !groups.isEmpty
  let headers := (if grouped then #["Subsystem"] else #[])
    ++ #["Boundary", "Role", "Kind", "Dedicated to", "Port"]
  let bs ← kindBindings layer scope
  if bs.isEmpty then
    return IndexTable.empty "kinds-by-boundary" "Kinds by boundary and role" headers
  let dedicated ← dedicatedByKind env scope
  let sorted := bs.qsort fun a b =>
    let ga := groupIndex groups a.contract
    let gb := groupIndex groups b.contract
    if ga != gb then ga < gb
    else if a.contract != b.contract then nameLt a.contract b.contract
    else if roleRank a.dir != roleRank b.dir then roleRank a.dir < roleRank b.dir
    else if a.kind != b.kind then nameLt a.kind b.kind
    else a.node.render < b.node.render
  let mut rows : Array (Array IndexCell) := #[]
  for b in sorted do
    let groupCell : Array IndexCell :=
      if grouped then #[.text ((groups[groupIndex groups b.contract]?.map (·.1)).getD "—")]
      else #[]
    let ded := dedicated.getD b.kind #[]
    rows := rows.push (groupCell ++ #[
      .decl b.contract b.boundary,
      .text (roleLabel b.dir),
      .decl b.kind (lastComponent b.kind),
      if ded.isEmpty then IndexCell.blank else .links (ded.map fun d => (d, lastComponent d)),
      .code b.node.render])
  return { id := "kinds-by-boundary", title := "Kinds by boundary and role", headers, rows }

/-- The `kinds` census of `layer` with two context columns: the declared boundaries carrying
each kind and the roles it enters in. Rows and order are exactly `kindsTable`'s, so a document
may substitute this for the census without changing what the census says. -/
def kindsInContextTable (layer : KindLayer) (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let base ← kindsTable layer scope
  let headers := base.headers ++ #["Boundaries", "Roles"]
  let kinds := constantsOfType env layer.ty scope
  let bs ← kindBindings layer scope
  let mut rows : Array (Array IndexCell) := #[]
  for row in base.rows, k in kinds do
    let mine := bs.filter (·.kind == k)
    let contracts := (mine.map (·.contract)).toList.eraseDups.toArray.qsort nameLt
    let roles := ((mine.map fun b => (roleRank b.dir, roleLabel b.dir)).toList.eraseDups.toArray.qsort
      fun a b => a.1 < b.1).map (·.2)
    rows := rows.push (row ++ #[
      if contracts.isEmpty then IndexCell.blank
      else .links (contracts.map fun c => (c, lastComponent c)),
      if roles.isEmpty then IndexCell.blank else .code (String.intercalate ", " roles.toList)])
  return { id := layer.id ++ "-in-context", title := layer.title ++ " in context", headers, rows }

/-- The census kinds of `layer` some declared boundary in scope carries. -/
def boundKinds (layer : KindLayer) (scope : Scope) : MetaM NameSet := do
  return (← kindBindings layer scope).foldl (init := {}) fun s b => s.insert b.kind

/-- The `kinds-unbound` table: the census kinds of `layer` no declared boundary carries. A table
of absences — its row count is the remainder of the partition `#pkc_kinds_partition` states. -/
def kindsUnboundTable (layer : KindLayer) (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let headers := #["Kind", "Identity"]
  let bound ← boundKinds layer scope
  let mut rows : Array (Array IndexCell) := #[]
  for k in constantsOfType env layer.ty scope do
    unless bound.contains k do
      rows := rows.push #[
        IndexCell.decl k (lastComponent k),
        readCell (.declText k) (← fieldStringChain? k layer.identity)]
  return { id := layer.id ++ "-unbound", title := layer.title ++ " no declared boundary carries",
           headers, rows }

/-- The partition of a census: how many of its kinds a declared boundary carries, and how many
none does. `census = bound + unbound` by construction; what a pin fixes is the split. -/
structure KindPartition where
  /-- The census size. -/
  census : Nat
  /-- Census kinds carried by at least one declared boundary. -/
  bound : Nat
  /-- Census kinds carried by none. -/
  unbound : Nat
deriving Repr, Inhabited

/-- The partition of `layer`'s census in scope over the declared boundaries in scope. -/
def kindPartition (layer : KindLayer) (scope : Scope) : MetaM KindPartition := do
  let env ← getEnv
  let kinds := constantsOfType env layer.ty scope
  let bound ← boundKinds layer scope
  let b := (kinds.filter bound.contains).size
  return { census := kinds.size, bound := b, unbound := kinds.size - b }

end PropertyKindCalculus.Index

end Blanket
