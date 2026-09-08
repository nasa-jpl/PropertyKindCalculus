/-
# ModuleCard — the metrological module interface document, generated

One declared boundary as a **specification sheet**: the interface a module advertises,
drawn from the checked declaration rather than beside it. Where the assembly figures
(`KindGraphD2`) render the *dissection* — every node, every wire — the card renders the
*claim*: the ports grouped by role and binding time, the clauses the contract carries
(deciders, aggregation classes, suppliers, exits), the theorem edges that relate this
boundary to others, and the inter-derivable kind clusters its interface crosses. It is
the reading a consumer of the module needs before deploying it, at the scale of the
contract's own vocabulary.

The emitter is a pure function of the contract value and of *prepared* rows for the two
readings the contract itself does not carry — the theorem edges (`RelationRow`, from
`checkRelation`'s results) and the kind clusters (`ClusterRow`, from the kind graph's
SCC partition) — so the caller passes checked objects and the card cannot invent an
edge or a cluster. The palette and the address shortening are `KindGraphD2`'s, so a
port reads the same in the card and in the dissection figure beside it.

The output is D2 text (https://d2lang.com) laid out as a grid — a card, not a layered
graph: rows stack, role groups sit side by side, and nothing is routed. Labels are
plain text for the same reason as in `KindGraphD2`: a markdown label becomes a
foreignObject HTML island that librsvg and LaTeX pipelines silently drop.
-/
import PropertyKindCalculus.KindGraphD2

namespace PropertyKindCalculus.ModuleCard

open PropertyKindCalculus.Provenance (Contract Port PortDir NodeId KindRef)
open PropertyKindCalculus.KindGraphD2 (esc q qLines boxStyle portFill portStroke shortAddr)

/-- One theorem edge as the card states it: the claim as read from this module
(`inverts '…'`, `bounded by '…'`), the witness, and the optional tolerance and named
hypotheses — prepared by the caller from `checkRelation`'s result, so the row is a
rendering of a checked edge. -/
structure RelationRow where
  /-- The claim, phrased from this module's side. -/
  claim : String
  /-- The witness theorem's declaration name. -/
  witness : String
  /-- The tolerance declaration, where the edge names one. -/
  tolerance : String := ""
  /-- The named side conditions the claim holds under. -/
  hypotheses : List String := []
deriving Repr, Inhabited

/-- One inter-derivable kind cluster crossing this module's interface: the cluster's
representative (the SCC pipeline's name for it) and the module's own kinds that fall in
it — prepared by the caller from the kind graph's partition. -/
structure ClusterRow where
  /-- The cluster's representative kind. -/
  representative : String
  /-- The kinds of this module's ports that belong to the cluster. -/
  kinds : List String
deriving Repr, Inhabited

/-- The role groups of the interface panel, in reading order: what the module takes per
datum, what a deployment must bind, what this tier already bound, what it produces. -/
private def roleGroups : List (String × List PortDir) :=
  [("inputs", [.input]),
   ("parameters", [.param]),
   ("configuration", [.config]),
   ("outputs", [.output, .conditional])]

/-- One clause row: label, fill, stroke, optional tooltip. -/
private structure ClauseRow where
  label : String
  fill : String
  stroke : String
  tooltip : Option String := none

private def clauseFill : String := "#f3f4f6"
private def clauseStroke : String := "#6b7280"
private def edgeFill : String := "#e5e7eb"
private def edgeStroke : String := "#111827"
private def clusterFill : String := "#fce7f3"
private def clusterStroke : String := "#be185d"

/-- Emit one panel of stacked rows. -/
private def panel (key label : String) (rows : List ClauseRow) : String := Id.run do
  if rows.isEmpty then return ""
  let mut out := s!"  {q key}: \{\n"
  out := out ++ s!"    label: {q label}\n"
  out := out ++ "    grid-columns: 1\n    grid-gap: 4\n"
  out := out ++ "    style: {stroke: \"#9ca3af\"; fill: \"#ffffff\"; border-radius: 8; font-size: 14; bold: true}\n"
  let mut i := 0
  for r in rows do
    out := out ++ s!"    {q s!"r{i}"}: \{label: {q r.label}; "
    if let some t := r.tooltip then
      out := out ++ s!"tooltip: {q t}; "
    out := out ++ s!"style: \{fill: {q r.fill}; stroke: {q r.stroke}; \
      border-radius: 6; font-size: 13; bold: false}}\n"
    i := i + 1
  out := out ++ "  }\n"
  return out

/-- **The module interface document** as a D2 card: the header with the module's name
and tallies, the interface panel (role groups side by side, ports as rows in the
dissection palette), the clause panel (decides / aggregates / supplies / exits), the
theorem-edge panel, and the cluster panel. `notes` renders as extra header lines — the
caller's place for a checked verdict worth advertising (a footprint verdict, a
discharge line). -/
def moduleCard (c : Contract NodeId KindRef)
    (relations : List RelationRow := [])
    (clusters : List ClusterRow := [])
    (notes : List String := []) : String := Id.run do
  let mut out := ""
  out := out ++ "vars: {\n  d2-config: {\n    layout-engine: dagre\n  }\n}\n"
  out := out ++ "direction: down\n"
  out := out ++ ("\"__title\": {label: " ++ q s!"metrological module — {c.name}"
    ++ "; shape: text; near: top-center; style: {font-size: 20; bold: true}}\n")
  out := out ++ "\"card\": {\n"
  out := out ++ "  label: \"\"\n"
  out := out ++ "  grid-columns: 1\n  grid-gap: 10\n"
  out := out ++ "  style: {stroke: \"#d1d5db\"; fill: \"#fafafa\"; border-radius: 10}\n"
  -- the header: tallies and the caller's checked notes
  let tally := s!"{c.members.length} member(s) · {c.ports.length} port(s) · \
    {c.exits.length} exit(s) · {relations.length} theorem edge(s)"
  out := out ++ "  \"__about\": {\n    label: \"\"\n    grid-columns: 1\n    grid-gap: 4\n"
  out := out ++ boxStyle ++ "\n"
  out := out ++ s!"    \"t\": \{label: {q tally}; shape: text; style: \{font-size: 13}}\n"
  let mut ni := 0
  for n in notes do
    out := out ++ s!"    {q s!"n{ni}"}: \{label: {q n}; shape: text; \
      style: \{font-size: 13; font-color: \"#374151\"}}\n"
    ni := ni + 1
  out := out ++ "  }\n"
  -- the interface: role groups side by side, rows in the dissection palette
  let groups := roleGroups.filterMap fun (label, dirs) =>
    let ps := c.ports.filter (fun p => dirs.contains p.dir)
    if ps.isEmpty then none else some (label, ps)
  if !groups.isEmpty then
    out := out ++ "  \"interface\": {\n"
    out := out ++ s!"    label: {q "interface"}\n"
    out := out ++ s!"    grid-columns: {groups.length}\n    grid-gap: 8\n"
    out := out ++ "    style: {stroke: \"#9ca3af\"; fill: \"#ffffff\"; border-radius: 8; font-size: 14; bold: true}\n"
    let deciderOf (n : NodeId) : Option Lean.Name :=
      c.deciders.find? (·.1 == n) |>.map (·.2)
    for (glabel, ps) in groups do
      out := out ++ s!"    {q glabel}: \{\n      grid-columns: 1\n      grid-gap: 4\n"
      out := out ++ "      style: {stroke: \"#e5e7eb\"; fill: \"#ffffff\"; border-radius: 8; font-size: 13; bold: true}\n"
      let mut i := 0
      for p in ps do
        let rn := p.node.render
        let a := shortAddr rn
        let disp := if (ps.filter (fun p' => shortAddr p'.node.render == a)).length == 1
          then a else rn
        let mark := if c.exits.contains p.node then " ⊗" else ""
        let tip := match deciderOf p.node, disp == rn with
          | some d, _ => some s!"decided by {d} · {rn}"
          | none, false => some rn
          | none, true => none
        let row : ClauseRow :=
          ⟨s!"{disp} : {p.kind.render}{mark}", portFill p.dir, portStroke p.dir, tip⟩
        out := out ++ s!"      {q s!"p{i}"}: \{label: {q row.label}; "
        if let some t := row.tooltip then
          out := out ++ s!"tooltip: {q t}; "
        out := out ++ s!"style: \{fill: {q row.fill}; stroke: {q row.stroke}; \
          border-radius: 6; font-size: 13; bold: false}}\n"
        i := i + 1
      out := out ++ "    }\n"
    out := out ++ "  }\n"
  -- the clauses: what the contract says beyond its port list
  let clauseRows : List ClauseRow :=
    c.aggregations.map (fun (n, a) =>
      ⟨s!"aggregates {shortAddr n.render}: {a.label}", clauseFill, clauseStroke,
        some n.render⟩)
    ++ c.suppliers.map (fun (n, s) =>
      ⟨s!"supplies {shortAddr n.render}: {shortAddr (toString s)}", clauseFill,
        clauseStroke, some s!"{n.render} ← {s}"⟩)
    ++ c.exits.map (fun n =>
      ⟨s!"exit {shortAddr n.render} ⊗ — leaves the calculus", clauseFill, clauseStroke,
        some n.render⟩)
  out := out ++ panel "clauses" "declared clauses" clauseRows
  -- the theorem edges: what relates this boundary to others, by proof
  let relRows : List ClauseRow := relations.map fun r =>
    let tolPart := if r.tolerance.isEmpty then "" else s!" · tolerance {shortAddr r.tolerance}"
    let hypPart := if r.hypotheses.isEmpty then "" else
      s!" · under {String.intercalate ", " (r.hypotheses.map shortAddr)}"
    ⟨s!"{r.claim}{tolPart}{hypPart}", edgeFill, edgeStroke,
      some s!"witness: {r.witness}"⟩
  out := out ++ panel "edges" "theorem edges" relRows
  -- the clusters: the inter-derivable kind components this interface crosses
  let clRows : List ClauseRow := clusters.map fun cl =>
    ⟨s!"cluster {cl.representative}: {String.intercalate ", " cl.kinds}",
      clusterFill, clusterStroke,
      some "kinds mutually derivable through licensed edges — a same-cluster swap is \
        compensable, not impossible"⟩
  out := out ++ panel "clusters" "inter-derivable kind clusters at this interface" clRows
  out := out ++ "}\n"
  return out

/-! ## The prepared rows — checked objects in, card rows out -/

open Lean Meta in
/-- The theorem-edge rows of one boundary: every `Provenance.Relation` declared under
`root`, re-checked exactly as `#kind_relation` checks one (a failing edge refuses the
card), phrased from `decl`'s side — the active claim where `decl` is the left boundary,
the passive reading where it is the right. `decl` is the contract's declaration name,
as the relations spell it. -/
def relationRows (root : Name) (decl : Name) : MetaM (List RelationRow) := do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, info) in env.constants.toList do
    if n.isInternal then continue
    unless root.isPrefixOf n do continue
    if info.type.isConstOf ``Provenance.Relation then names := names.push n
  let sorted := names.qsort fun a b => a.toString < b.toString
  let mut rows : List RelationRow := []
  for n in sorted do
    let c ← KindIncidence.checkRelation n
    let rel := c.rel
    let tolS := if rel.tolerance.isAnonymous then "" else toString rel.tolerance
    if rel.left == decl then
      rows := rows ++ [{ claim := s!"{rel.kind.label} '{c.rightName}'",
                         witness := toString rel.witness, tolerance := tolS,
                         hypotheses := rel.hypotheses.map toString }]
    else if rel.right == decl then
      let passive := match rel.kind with
        | .inverts => s!"inverted by '{c.leftName}'"
        | .boundedBy => s!"bounds '{c.leftName}'"
        | .equals => s!"equals '{c.leftName}'"
        | .refines => s!"refined by '{c.leftName}'"
      rows := rows ++ [{ claim := passive, witness := toString rel.witness,
                         tolerance := tolS, hypotheses := rel.hypotheses.map toString }]
  return rows

end PropertyKindCalculus.ModuleCard
