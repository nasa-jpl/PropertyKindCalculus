/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette

# ModuleSheet — the module interface document as tables

The same checked objects `ModuleCard` renders as a D2 card — the declared contract, the
theorem-edge survey, the interface's inter-derivability clusters — harvested as
`IndexTable`s of `IndexCell`s, for a document that renders tables with links where the
card renders boxes. A card is legible at the interface's scale of a dozen ports; a
production boundary with its parameters and configuration spelled out is not, and a
table is — with every declaration a cell names carried as a `Lean.Name` for the
rendering document to link (a kind to its declaration, a configuration port to the
declaration that binds it, a witness to its theorem, an aggregation to its evidence).

One producer: the port display rule is `ModuleCard.portDisplay`, the edge rows are
`ModuleCard.relationRows`, the cluster rows are `KindGraph.clusterRows` — the card and
the tables render the same prepared values, so they cannot disagree about an interface.

The harvest is **closure-sensitive** like every environment survey (the relation rows
and the cluster partition see what the elaborating document imports): a document calling
`sheetTables` must import the same closure as the generator that renders the cards, or
its edge and cluster tables under-report silently.
-/

module

public import PropertyKindCalculus.Graph.Footprint
public import PropertyKindCalculus.Index.Basic
public import PropertyKindCalculus.KindEdges

@[expose] public section Blanket

namespace PropertyKindCalculus.ModuleSheet

open Lean Meta
open PropertyKindCalculus.Index (IndexCell IndexTable lastComponent summaryLine shortenNames)
open PropertyKindCalculus.Provenance (Contract Port PortDir NodeId KindRef NodeRef)
open PropertyKindCalculus.KindIncidence (contractValueOf)
open PropertyKindCalculus.ModuleCard (RelationRow ClusterRow relationRows portDisplay)
open PropertyKindCalculus.KindGraph (kindGraphOf clusterRows)

/-- The cell of one port: `portDisplay`'s form (with the card's `⊗` mark on a declared
exit), linked to the binding declaration where the port's address *is* one — a
configuration port names the constant that binds it, and that is the one thing on a
sheet a reader most wants to open. Every other address is a binder or a result, which
no environment page exists for. -/
def portCell (c : Contract NodeId KindRef) (ps : List (Port NodeId KindRef))
    (p : Port NodeId KindRef) : IndexCell :=
  let disp := portDisplay ps p ++ (if c.exits.contains p.node then " ⊗" else "")
  match p.node.root with
  | .const n => .declText n disp
  | _ => .code disp

/-- The cell of one kind reference: a `decl` links its rendering to the kind
declaration; every other class (a generic binder, a signature, a tuple) keeps its
rendered grammar as code — a `links` list would flatten a signature's `→` into commas. -/
def kindCell (k : KindRef) : IndexCell :=
  match k with
  | .decl n => .declText n k.render
  | _ => .code k.render

/-- The `Cases` cell of a produced port: the linked decider of a `conditional` port,
the contract's own reading for a conditional port without one, blank for a plain
output. -/
def casesCell (c : Contract NodeId KindRef) (p : Port NodeId KindRef) : IndexCell :=
  if p.dir == .conditional then
    match c.deciders.find? (·.1 == p.node) with
    | some (_, d) => .declText d s!"decided by {lastComponent d}"
    | none => .text "declared cases; the predicate is stated elsewhere"
  else .blank

/-- The `Aggregation` cell of a produced port: the class label with its names
shortened, linked to the evidence declaration where the class names one; blank for a
port with no distribution claim. -/
def aggregationCell (c : Contract NodeId KindRef) (p : Port NodeId KindRef) : IndexCell :=
  match c.aggregations.find? (·.1 == p.node) with
  | some (_, a) =>
    match a.evidence with
    | some ev => .declText ev (shortenNames a.label)
    | none => .text a.label
  | none => .blank

/-- The role groups of the sheet, in the card's reading order, with the reading each
role's docstring states. -/
def roleGroups : List (String × String × List PortDir) :=
  [("sheet-inputs", "Inputs — consumed per datum", [.input]),
   ("sheet-parameters", "Parameters — left for the deploying tier to bind", [.param]),
   ("sheet-configuration", "Configuration — bound at this tier", [.config]),
   ("sheet-outputs", "Outputs — produced at this boundary", [.output, .conditional])]

/-- **The module interface document as tables**, as a pure function of the prepared
values — the checked contract, the theorem-edge rows, the cluster rows, and the
members' docstring summaries — exactly the doctrine of `ModuleCard`'s emitters: the
caller passes checked objects, and the tables cannot invent an edge or a cluster.

The tables: the members (each with its summary), one table per non-empty interface
role group, the theorem-edge table, and the cluster table. Columns a boundary does not
use are omitted: a parameters table has a `Supplied by` column only where a supplier
clause exists, an outputs table a `Cases` column only where a conditional port does,
and so on. An empty survey contributes no table — the sheet's authored problem header
is where an absence is stated. -/
def sheetTablesOf (c : Contract NodeId KindRef) (rels : List RelationRow)
    (cls : List ClusterRow) (memberDocs : List (Name × String)) :
    Array IndexTable := Id.run do
  let mut tables : Array IndexTable := #[]
  -- the members, each with the first paragraph of its docstring
  let mut memberRows : Array (Array IndexCell) := #[]
  for (m, doc) in memberDocs do
    memberRows := memberRows.push
      #[.decl m (lastComponent m), if doc.isEmpty then .blank else .prose doc]
  tables := tables.push
    { id := "sheet-members", title := s!"Members — the declarations '{c.name}' is claimed for"
      headers := #["Member", "What it does"], rows := memberRows }
  -- the interface, one table per non-empty role group
  for (id, title, dirs) in roleGroups do
    let ps := c.ports.filter (fun p => dirs.contains p.dir)
    if ps.isEmpty then continue
    let produced := dirs.contains PortDir.output
    let withSuppliers := ps.any (fun p => c.suppliers.any (·.1 == p.node))
    let withCases := produced && ps.any (·.dir == .conditional)
    let withAggregations := produced && ps.any (fun p => c.aggregations.any (·.1 == p.node))
    let withExits := ps.any (fun p => c.exits.contains p.node)
    let headers := #["Port", "Kind"]
      ++ (if withSuppliers then #["Supplied by"] else #[])
      ++ (if withCases then #["Cases"] else #[])
      ++ (if withAggregations then #["Aggregation"] else #[])
    let title := title ++ (if withExits then " · ⊗ leaves the calculus" else "")
    let mut rows : Array (Array IndexCell) := #[]
    for p in ps do
      let mut row : Array IndexCell := #[portCell c ps p, kindCell p.kind]
      if withSuppliers then
        row := row.push <| match c.suppliers.find? (·.1 == p.node) with
          | some (_, s) => .declText s (lastComponent s)
          | none => .blank
      if withCases then row := row.push (casesCell c p)
      if withAggregations then row := row.push (aggregationCell c p)
      rows := rows.push row
    tables := tables.push { id, title, headers, rows }
  -- the theorem edges, columns as the survey needs them
  if !rels.isEmpty then
    let withTol := rels.any (fun r => !r.toleranceName.isAnonymous)
    let withHyp := rels.any (fun r => !r.hypothesisNames.isEmpty)
    let headers := #["Claim", "Witness"]
      ++ (if withTol then #["Tolerance"] else #[])
      ++ (if withHyp then #["Under"] else #[])
    let mut rows : Array (Array IndexCell) := #[]
    for r in rels do
      let claim : IndexCell :=
        if r.other.isAnonymous then .text r.claim else .declText r.other r.claim
      let witness : IndexCell :=
        if r.witnessName.isAnonymous then .code r.witness
        else .decl r.witnessName (lastComponent r.witnessName)
      let mut row : Array IndexCell := #[claim, witness]
      if withTol then
        row := row.push <| if r.toleranceName.isAnonymous then .blank
          else .decl r.toleranceName (lastComponent r.toleranceName)
      if withHyp then
        row := row.push <| if r.hypothesisNames.isEmpty then .blank
          else .links (r.hypothesisNames.toArray.map fun h => (h, lastComponent h))
      rows := rows.push row
    tables := tables.push
      { id := "sheet-edges"
        title := "Theorem edges — what relates this boundary to others, by proof"
        headers, rows }
  -- the inter-derivable clusters this interface crosses
  if !cls.isEmpty then
    let mut rows : Array (Array IndexCell) := #[]
    for row in cls do
      let kinds : IndexCell :=
        let linked := row.refs.filterMap fun k => match k with
          | .decl n => some (n, k.render)
          | _ => none
        if linked.length == row.kinds.length then .links linked.toArray
        else .code (String.intercalate ", " row.kinds)
      rows := rows.push #[.code row.representative, kinds]
    tables := tables.push
      { id := "sheet-clusters"
        title := "Inter-derivable kind clusters at this interface — a same-cluster \
          swap is compensable, not impossible"
        headers := #["Cluster", "This interface's kinds in it"], rows }
  return tables

/-- The tables of one **declared** boundary: `sheetTablesOf` over the values the card
generator prepares the same way — the contract read from its declaration, the relation
survey under `root`, the cluster rows of `root`'s kind graph, and each member's
docstring summary — plus the one table only an environment walk can prepare: the
kind-algebra equations at this interface, `KindEdges.groupEdges`'s produced/consumed
groups restricted to the sheet's port kinds, each equation linked to its authoring
declaration. The closure-sensitivity note in the module docstring applies: the surveys
see the elaborating document's imports. -/
def sheetTables (decl : Name) (root : Name) : MetaM (Array IndexTable) := do
  let c ← contractValueOf decl
  let rels ← relationRows root decl
  let kg ← kindGraphOf #[root]
  let cls := clusterRows kg c
  let env ← getEnv
  let mut docs : List (Name × String) := []
  for m in c.members do
    docs := docs ++ [(m, ← summaryLine env m)]
  let mut tables := sheetTablesOf c rels cls docs
  let kindNames := ((c.ports.map (·.kind)).eraseDups.filterMap fun k =>
    match k with | .decl n => some n | _ => none).toArray
  let byKind ← KindEdges.edgesByKind kindNames
  let mut kindRows : Array (Array IndexCell) := #[]
  for n in kindNames do
    let es := byKind.getD n #[]
    if es.isEmpty then continue
    kindRows := kindRows.push
      #[.declText n (lastComponent n), .codeGroups (KindEdges.groupEdges (lastComponent n) es)]
  if !kindRows.isEmpty then
    tables := tables.push
      { id := "sheet-kind-equations"
        title := "Kind algebra at this interface — the licensed equations over the \
          sheet's kinds, each linked to its authoring declaration"
        headers := #["Kind", "Produced / consumed"], rows := kindRows }
  return tables

end PropertyKindCalculus.ModuleSheet

end Blanket
