/-
# KindGraphD2 — the assembly figure, generated from the checked object

Dybkær's dissection of a property statement, as a figure a pipeline *generates*: each
assembly level is a container — its ports and interior introduction events as rows,
colored by role and evidence tier, exits marked `⊗` at the erasure boundary, an
attested row carrying its reason as the tooltip — and the occurrences of the assembled
graph are the arrows: witness edges labeled with their family glyph, procedure edges
with their step name, identity wires thin and gray, the citation relation dashed
between containers (a reference the walk could not wire is a citation, never an edge
of the checked object). The emitter is a *pure* function of the `Assembly` value the
verdict and the kernel theorem are stated on, so the figure cannot drift from the
object: what `#kind_assembly_decide` accepted is what is drawn, and the provenance box
carries the figure's own accountability — the evaluated verdict beside the assembled
declarations with their source files (`AssemblyLevel.src`), so the reader is told
which definitions, in which files, the graph is a reading of. **Red is the
nonconformance reading** (`KindIncidence`, "Unkinded positions"): an unkinded
signature position draws as a red row, an unkinded flow — unkinded information
minting or steering kinded information — as a red arrow, and the provenance box
pairs the wiring verdict with the unkinded count, so a figure with red in it says so
in its own header. A shape legend repeats
the row palette and the arrow classes as the shapes themselves. Every label is plain
text: a markdown label would render as a foreignObject HTML island, which librsvg and
LaTeX pipelines silently drop, so the emitted document stays pure SVG.

The output is D2 text (https://d2lang.com) requesting the `dagre` layered engine. The
division of labor is deliberate: WHAT the figure claims — which nodes meet at which
edges, at which kinds, under which tiers — is this module's output, decidable by
evaluation on the emitted text; WHERE a box sits is the layout engine's problem
(crossing minimization, edge routing through nested boxes), a solved one no
hand-rolled coordinate pass should re-solve. The engine is named for a reason that
belongs to the figure rather than to the layout: ELK sizes a node to hold one port per
incident edge, so a heavily-wired row is drawn as a tall, mostly empty box. That makes
*area* a picture of degree — a configuration constant eight steps read grows into a
placard beside a measurand read once — and a reader being shown which rows matter must
not be shown it by an artifact of the routing. `dagre` leaves a row the size of what it
says. A multi-operand hyperedge meets at a
small diamond junction node — the standard drawing of a hyperedge in a binary-edge
grammar — with arrowhead-suppressed legs from the operands and one arrowed leg to the
result: legs stay directed so the layered engine orders operands before the junction
and the junction before the result. A junction whose operands and result all live in
one level nests inside that level's container — a hyperedge interior to a step is
drawn interior to its box, not routed out and back in.

## The reading scale

A declared boundary of any size draws as one container per level and one row per node.
That is the reading a reviewer needs when checking a particular wire, and the one that
is unreadable when asking what the scope *is*. So the same assembly emits two figures.
`emit` is the full dissection. `emitOverview` is the same value at the scale of its
members: one box per level carrying its interface tally and its unkinded count, one
arrow per pair of levels information crosses between carrying how many wires cross.
Both are pure functions of the one `Assembly`, so the overview is not a summary drawn
beside the figure — it is the same object, and a box the contract does not declare
cannot appear in either.

A row's *label* may be shorter than its node name. A node name is an address, so a
configuration port carries the namespace it was declared in; a namespace is not what
tells one row of a box from another, and repeating it on every row is what makes a box
wider than a screen. The label therefore drops the leading namespace components — and
only where the result still *identifies* the row inside its box: a shortening that
would collide with another row's leaves both at their full addresses. The D2 key stays
the full address, and a shortened row carries its full address as its tooltip, so
nothing the figure claims lives only in the label.
-/
import PropertyKindCalculus.KindIncidence

namespace PropertyKindCalculus.KindGraphD2

open PropertyKindCalculus.Provenance (Port Intro Occurrence EdgeFamily IntroTier PortDir)
open PropertyKindCalculus.KindIncidence
  (Assembly AssemblyLevel LevelTally tallyOf crossings citeEdges)

/-- Escape a fragment for a double-quoted D2 key or value. -/
def esc (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '\\' => acc ++ "\\\\"
    | '"' => acc ++ "\\\""
    | c => acc.push c

/-- A double-quoted D2 key or value — quoting also neutralizes D2's reserved words as
node names. -/
def q (s : String) : String := "\"" ++ esc s ++ "\""

/-- A double-quoted D2 label of several lines. D2 reads `\n` inside a quoted string as
a line break and renders it as `tspan`s — still pure SVG, unlike a markdown label,
which becomes a foreignObject HTML island that librsvg and LaTeX pipelines drop. -/
def qLines (ls : List String) : String :=
  "\"" ++ String.intercalate "\\n" (ls.map esc) ++ "\""

/-- The row fill of a port role (light, so the row text reads dark) — a `param`, bound
by the tier below rather than here, reads as its own colour and not as a configuration
this tier fixed, and a `conditional` output reads as its own shade of the output green,
because it is produced in some cases of the result and not others. -/
def portFill : PortDir → String
  | .input => "#dbeafe"
  | .config => "#fef3c7"
  | .param => "#ede9fe"
  | .output => "#dcfce7"
  | .conditional => "#ecfccb"

/-- The row border of a port role. -/
def portStroke : PortDir → String
  | .input => "#2563eb"
  | .config => "#d97706"
  | .param => "#7c3aed"
  | .output => "#16a34a"
  | .conditional => "#65a30d"

/-- The row fill of an unkinded signature position — red: outside the kinded
algebra. -/
def unkindedFill : String := "#fee2e2"

/-- The row border of an unkinded position, and the color of an unkinded-flow
arrow. -/
def unkindedStroke : String := "#dc2626"

/-- The row fill of an introduction tier. -/
def tierFill : IntroTier → String
  | .derived => "#f3f4f6"
  | .gated => "#ccfbf1"
  | .attested _ => "#fde68a"

/-- The row border of an introduction tier. -/
def tierStroke : IntroTier → String
  | .derived => "#6b7280"
  | .gated => "#0d9488"
  | .attested _ => "#b45309"

/-- The glyph an edge family is labeled with in the figure (the equation grammar's
operator, compressed to fit an arrow). -/
def familyGlyph : EdgeFamily → String
  | .product => "·"
  | .quotient => "/"
  | .reciprocal => "1/x"
  | .transcendental => "f"
  | .power p => s!"^{EdgeFamily.renderExp p}"
  | .reference => "ref"
  | .additive => "±"
  | .tableMul => "[T]·"
  | .tableDiv => "[T]/"
  | .copy => ""
  | .step nm _ => s!"[{nm}]"
  | .select _ => "select"

/-- The arrow color of an edge family: identity wires gray, procedure edges indigo,
nominal selections teal (a label chooses; it does not compute), witness edges
near-black. -/
def familyStroke : EdgeFamily → String
  | .copy => "#9ca3af"
  | .step _ _ => "#4f46e5"
  | .select _ => "#0d9488"
  | _ => "#111827"

/-- The tier label without the attested reason — the reason becomes the row's
tooltip. -/
def tierShortLabel : IntroTier → String
  | .derived => "derived"
  | .gated => "gated"
  | .attested _ => "attested"

/-- The inclusion-mode label of a level. -/
def modeLabel (l : AssemblyLevel) : String :=
  if l.walked then "walked" else "interface"

/-- Is this dot-component a namespace rather than part of the declaration below it? A
namespace is capitalized by Lean convention; a declaration and the field path under it
are not. -/
def isNamespaceComponent (s : String) : Bool :=
  match s.toList with
  | c :: _ => c.isUpper
  | [] => false

/-- Drop the leading namespace components of a dotted address, always keeping at least
the last one. -/
def dropNamespace : List String → List String
  | [] => []
  | [x] => [x]
  | x :: rest => if isNamespaceComponent x then dropNamespace rest else x :: rest

/-- The short display form of an address (module header, "The reading scale"):
`SoilMoisture.Algorithm.Batch.mironovCoeffsC.ndA0` reads as `mironovCoeffsC.ndA0`. -/
def shortAddr (n : String) : String :=
  String.intercalate "." (dropNamespace (n.splitOn "."))

/-- One row of a level's container: the graph node it stands for, its container-local
key (the level's namespace prefix stripped), display label, fill and border colors,
and an optional tooltip — the attested reason, the row's full address when the label
was shortened, or both. -/
structure Row where
  node : String
  key : String
  label : String
  fill : String
  stroke : String
  tooltip : Option String
deriving Inhabited

/-- The rows of one level: ports in graph order, the signature's unkinded positions in
red, then introduction events, exits marked `⊗` at the erasure boundary. A row's label
carries the short form of its address wherever that still tells the row from the other
rows of this box, and then carries the full address as the tooltip. -/
def levelRows (l : AssemblyLevel) : Array Row := Id.run do
  let strip (n : String) : String :=
    if n.startsWith (l.name ++ "/") then (n.drop (l.name.length + 1)).toString else n
  let exitMark (n : String) : String :=
    if l.graph.exits.contains n then " ⊗" else ""
  -- every address this box will show, so a shortening can be checked against the rest
  -- of the box rather than assumed harmless
  let addrs : List String :=
    l.graph.ports.map (fun p => strip p.node)
      ++ l.unkinded.map (fun u => strip u.node)
      ++ l.graph.intros.map (fun i => strip i.node)
  let shorts := addrs.map shortAddr
  let disp (a : String) : String :=
    let s := shortAddr a
    if (shorts.filter (· == s)).length == 1 then s else a
  let addrTip (a : String) : Option String :=
    if disp a == a then none else some a
  let mut rows : Array Row := #[]
  for p in l.graph.ports do
    let a := strip p.node
    rows := rows.push
      ⟨p.node, a, s!"{p.dir.label} {disp a} : {p.kind}{exitMark p.node}",
        portFill p.dir, portStroke p.dir, addrTip a⟩
  for u in l.unkinded do
    let a := strip u.node
    rows := rows.push
      ⟨u.node, a, s!"unkinded {u.dir.label} {disp a} : {u.type}",
        unkindedFill, unkindedStroke, addrTip a⟩
  for i in l.graph.intros do
    let a := strip i.node
    let tip := match i.tier, addrTip a with
      | .attested r, some full => some s!"{r} · {full}"
      | .attested r, none => some r
      | _, some full => some full
      | _, none => none
    rows := rows.push
      ⟨i.node, a, s!"{tierShortLabel i.tier} {disp a} : {i.kind}{exitMark i.node}",
        tierFill i.tier, tierStroke i.tier, tip⟩
  return rows

/-- The style of the two header boxes — the provenance box and the legend. -/
def boxStyle : String :=
  "  style: {stroke: \"#9ca3af\"; fill: \"#ffffff\"; border-radius: 8; font-size: 13; font-color: \"#374151\"}"

/-- The preamble both figures share: the engine request, the flow direction, the
title, and the provenance box — the evaluated verdict and the unkinded count beside
the assembled declarations with their source files, so either figure carries its own
accountability. -/
def preamble (a : Assembly) (title : String) : String := Id.run do
  let mut out := ""
  let put (s : String) : String := s ++ "\n"
  out := out ++ put "vars: {"
  out := out ++ put "  d2-config: {"
  out := out ++ put "    layout-engine: dagre"
  out := out ++ put "  }"
  out := out ++ put "}"
  out := out ++ put "direction: right"
  let ok := a.graph.wellFormed
  let (vc, vt) := if ok then ("#16a34a", "well-formed: true")
    else ("#dc2626", "well-formed: false")
  out := out ++ put ("\"__title\": {label: " ++ q title
    ++ "; shape: text; near: top-center; style: {font-size: 20; bold: true}}")
  -- a grid of one column, not a chain of invisible edges: a chained column is a
  -- layered graph, and the engine spaces it like one — the accountability box grew
  -- taller than the drawing it accounts for
  out := out ++ put "\"__provenance\": {"
  out := out ++ put ("  label: " ++ q "assembled from (in list order)")
  out := out ++ put "  near: top-left"
  out := out ++ put "  grid-columns: 1"
  out := out ++ put "  grid-gap: 6"
  out := out ++ put boxStyle
  out := out ++ put ("  \"v\": {label: \"" ++ vt
    ++ "\"; shape: text; style: {font-size: 13; font-color: \"" ++ vc ++ "\"; bold: true}}")
  -- the wiring verdict's red twin: the unkinded count, so a figure with red rows and
  -- arrows in it says so in its own header
  let unkCount := a.levels.foldl (init := 0) fun n l => n + l.unkinded.length
  let (uc, ut) := if unkCount == 0 then
      ("#16a34a", "unkinded positions: none — fully kinded")
    else
      ("#dc2626", s!"unkinded positions: {unkCount} — outside the kinded algebra")
  out := out ++ put ("  \"u\": {label: \"" ++ ut
    ++ "\"; shape: text; style: {font-size: 13; font-color: \"" ++ uc ++ "\"; bold: true}}")
  for i in [0:a.levels.size] do
    let l := a.levels[i]!
    -- the declaration over its file, not beside it: the two together are the claim, and
    -- side by side they make the accountability box wider than the title above it
    let lines := if l.src.isEmpty then [s!"{l.decl}"] else [s!"{l.decl}", s!"  {l.src}"]
    out := out ++ put ("  " ++ q s!"s{i}" ++ ": {label: " ++ qLines lines
      ++ "; shape: text; style: {font-size: 12; font: mono; font-color: \"#374151\"}}")
  out := out ++ put "}"
  return out

/-- Emit the assembly as a D2 document (module header: the figure is a pure rendering
of the checked object; layout is the engine's). -/
def emit (a : Assembly) (title : String := "kind assembly") : String := Id.run do
  let mut out := preamble a title
  let put (s : String) : String := s ++ "\n"
  -- the shape legend: a two-column table, each column a grid of swatches. A grid
  -- packs cells without needing an invisible edge to order them — and without the
  -- layered engine's opinion about where an unconnected node belongs. An arrow class
  -- shows as its line colour on a pill's border rather than as a drawn arrow: a legend
  -- states the mapping colour ↦ meaning, and a drawn arrow costs three rows to say the
  -- same thing. Every label is plain text — a markdown label would render as a
  -- foreignObject HTML island, which librsvg and LaTeX pipelines silently drop, so the
  -- emitted document stays pure SVG
  out := out ++ put "\"__legend\": {"
  out := out ++ put ("  label: " ++ q "legend")
  out := out ++ put "  near: bottom-center"
  out := out ++ put "  grid-columns: 2"
  out := out ++ put "  grid-gap: 16"
  out := out ++ put boxStyle
  let subStyle :=
    "    style: {stroke: \"#e5e7eb\"; fill: \"#ffffff\"; font-size: 12; font-color: \"#6b7280\"}"
  out := out ++ put "  \"rows\": {"
  out := out ++ put ("    label: " ++ q "node rows")
  out := out ++ put "    grid-columns: 2"
  out := out ++ put "    grid-gap: 8"
  out := out ++ put subStyle
  let swatches : Array (String × String × String) :=
    #[("input port", portFill .input, portStroke .input),
      ("config port", portFill .config, portStroke .config),
      ("param port", portFill .param, portStroke .param),
      ("output port", portFill .output, portStroke .output),
      ("conditional output", portFill .conditional, portStroke .conditional),
      ("derived", tierFill .derived, tierStroke .derived),
      ("gated", tierFill .gated, tierStroke .gated),
      ("attested ⓘ", tierFill (.attested ""), tierStroke (.attested "")),
      ("unkinded", unkindedFill, unkindedStroke)]
  for i in [0:swatches.size] do
    let (lbl, f, st) := swatches[i]!
    out := out ++ put ("    " ++ q s!"sw{i}" ++ ": {label: " ++ q lbl
      ++ "; style: {fill: " ++ q f ++ "; stroke: " ++ q st
      ++ "; border-radius: 6; font-size: 12}}")
  out := out ++ put "  }"
  out := out ++ put "  \"arrows\": {"
  out := out ++ put ("    label: " ++ q "arrow classes (line colour)")
  out := out ++ put "    grid-columns: 2"
  out := out ++ put "    grid-gap: 8"
  out := out ++ put subStyle
  let samples : Array (String × String × String) :=
    #[("witness", "#111827", ""),
      ("procedure [step]", "#4f46e5", ""),
      ("nominal selection", "#0d9488", ""),
      ("identity wire", "#9ca3af", ""),
      ("citation (dashed)", "#4f46e5", "; stroke-dash: 4"),
      ("unkinded flow", unkindedStroke, "")]
  for i in [0:samples.size] do
    let (lbl, stroke, dash) := samples[i]!
    out := out ++ put ("    " ++ q s!"l{i}" ++ ": {label: " ++ q lbl
      ++ "; style: {fill: \"#ffffff\"; stroke: " ++ q stroke ++ "; stroke-width: 3"
      ++ dash ++ "; border-radius: 6; font-size: 12}}")
  out := out ++ put "  }"
  -- a borderless box, not a `text` shape: a text shape does not size the grid cell it
  -- sits in, and the note then runs out of the legend
  out := out ++ put ("  \"note\": {label: " ++ qLines
      ["⊗ exit at the erasure boundary · ⓘ carries the attested reason",
       "red = outside the kinded algebra",
       "a shortened label's full address is its tooltip"]
    ++ "; style: {stroke-width: 0; fill: \"#ffffff\"; font-size: 12; font-color: \"#374151\"}}")
  out := out ++ put "}"
  -- the level containers: one box per level, its mode on the label and — interface
  -- mode — on a dashed border; every row registers its graph node's D2 path and its
  -- level (junction nesting below asks which container an endpoint lives in)
  let mut path : Std.HashMap String String := {}
  let mut level : Std.HashMap String String := {}
  for l in a.levels do
    let rows := levelRows l
    out := out ++ put (q l.name ++ ": {")
    out := out ++ put ("  label: " ++ q s!"{l.name} ({modeLabel l})")
    let dash := if l.walked then "" else "; stroke-dash: 2"
    out := out ++ put ("  style: {stroke: \"#374151\"; fill: \"#f9fafb\"; border-radius: 8; font-size: 15"
      ++ dash ++ "}")
    for r in rows do
      let tip := match r.tooltip with
        | some t => "; tooltip: " ++ q t
        | none => ""
      out := out ++ put ("  " ++ q r.key ++ ": {label: " ++ q r.label
        ++ "; style: {fill: " ++ q r.fill ++ "; stroke: " ++ q r.stroke
        ++ "; border-radius: 6; font-size: 13}" ++ tip ++ "}")
      path := path.insert r.node (q l.name ++ "." ++ q r.key)
      level := level.insert r.node l.name
    out := out ++ put "}"
  -- the occurrences: a single-operand edge draws direct with its glyph; a
  -- multi-operand hyperedge meets at a diamond junction — arrowhead-suppressed
  -- directed legs in (the layered engine orders them), one arrowed leg out carrying
  -- the glyph; a junction interior to one level nests inside that level's container
  let mut jIdx := 0
  for o in a.graph.occurrences do
    let some dst := path.get? o.result | continue
    let srcs := o.operands.filterMap fun oc => path.get? oc.1
    if srcs.isEmpty then continue
    let stroke := familyStroke o.family
    let glyph := familyGlyph o.family
    let lbl := if glyph.isEmpty then "" else "label: " ++ q glyph ++ "; "
    let eStyle := "style: {stroke: " ++ q stroke
      ++ "; font-size: 12; font-color: \"#4b5563\"}"
    if srcs.length == 1 then
      out := out ++ put (s!"{srcs[0]!} -> {dst}: " ++ "{" ++ lbl ++ eStyle ++ "}")
    else
      let home : Option String := Id.run do
        let some l := level.get? o.result | return none
        for oc in o.operands do
          unless level.get? oc.1 == some l do return none
        return some l
      let j := match home with
        | some l => q l ++ "." ++ q s!"__j{jIdx}"
        | none => q s!"__j{jIdx}"
      jIdx := jIdx + 1
      out := out ++ put (j ++ ": {label: \"\"; shape: diamond; width: 16; height: 16; style: {fill: \"#ffffff\"; stroke: "
        ++ q stroke ++ "}}")
      for src in srcs do
        out := out ++ put (s!"{src} -> {j}: " ++ "{style: {stroke: " ++ q stroke
          ++ "}; target-arrowhead: {shape: none}}")
      out := out ++ put (s!"{j} -> {dst}: " ++ "{" ++ lbl ++ eStyle ++ "}")
  -- the unkinded flows, red: an unkinded signature position minting or steering a
  -- kinded node — a path outside the kinded algebra ("Red is the nonconformance
  -- reading", module header)
  for l in a.levels do
    for (s, t) in l.leaks do
      let some src := path.get? s | continue
      let some dst := path.get? t | continue
      out := out ++ put (s!"{src} -> {dst}: " ++ "{style: {stroke: "
        ++ q unkindedStroke ++ "}}")
  -- the citation relation, dashed between containers — drawn, never wired. Its
  -- endpoints are resolved to levels first: a citation names a member, and a member
  -- dissected at three call sites is three levels
  for (src, dst) in citeEdges a do
    out := out ++ put (s!"{q src} -> {q dst}: "
      ++ "{style: {stroke: \"#4f46e5\"; stroke-dash: 4; opacity: 0.6}}")
  return out

/-! ## The overview — the same object at the scale of its steps -/

/-- **The overview figure** — the same `Assembly` the full figure draws, read at the
scale of its members: one box per level carrying its interface tally and its unkinded
count, one arrow per pair of levels information crosses between carrying how many
wires cross, and the citation relation dashed. It is not a summary drawn beside the
figure; it is the same checked value, so a box that is not in the contract cannot
appear here either. -/
def emitOverview (a : Assembly) (title : String := "kind assembly") : String := Id.run do
  let mut out := preamble a (title ++ " — overview")
  let put (s : String) : String := s ++ "\n"
  -- one box, not a container: at this scale the legend explains the boxes and the
  -- arrows, and nothing in it needs a shape of its own
  out := out ++ put ("\"__legend\": {label: " ++ qLines
      ["legend",
       "solid border — the walk read this member's body",
       "dashed border — the member entered at its signature",
       "red box — the member states unkinded positions",
       "arrow — information crosses; the label is how many wires",
       "dashed arrow — a citation: referenced, never wired"]
    ++ "; near: bottom-center; style: {stroke: \"#9ca3af\"; fill: \"#ffffff\"; \
       border-radius: 8; font-size: 13; font-color: \"#374151\"}}")
  for l in a.levels do
    let t := tallyOf l
    let nodes := t.ins + t.cfgs + t.outs + t.interior + t.unkinded
    let red := t.unkinded > 0
    let lines := [l.name, s!"{modeLabel l} · {nodes} nodes",
                  s!"{t.ins} in · {t.cfgs} config · {t.outs} out · {t.interior} interior"]
      ++ (if red then [s!"⚠ {t.unkinded} unkinded"] else [])
    let (fill, stroke) := if red then (unkindedFill, unkindedStroke)
      else ("#f9fafb", "#374151")
    let dash := if l.walked then "" else "; stroke-dash: 2"
    out := out ++ put (q l.name ++ ": {label: " ++ qLines lines ++ "; style: {fill: "
      ++ q fill ++ "; stroke: " ++ q stroke
      ++ "; border-radius: 8; font-size: 14" ++ dash ++ "}}")
  for c in crossings a do
    let lbl := if c.2.2 == 1 then "1 wire" else s!"{c.2.2} wires"
    out := out ++ put (q c.1 ++ " -> " ++ q c.2.1 ++ ": {label: " ++ q lbl
      ++ "; style: {stroke: \"#4f46e5\"; font-size: 12; font-color: \"#4b5563\"}}")
  for (src, dst) in citeEdges a do
    out := out ++ put (s!"{q src} -> {q dst}: "
      ++ "{style: {stroke: \"#4f46e5\"; stroke-dash: 4; opacity: 0.6}}")
  return out

end PropertyKindCalculus.KindGraphD2
