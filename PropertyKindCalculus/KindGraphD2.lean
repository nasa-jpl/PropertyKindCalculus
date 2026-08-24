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

The output is D2 text (https://d2lang.com) requesting the ELK layered engine. The
division of labor is deliberate: WHAT the figure claims — which nodes meet at which
edges, at which kinds, under which tiers — is this module's output, decidable by
evaluation on the emitted text; WHERE a box sits is the layout engine's problem
(crossing minimization, orthogonal edge routing through nested boxes), a solved one no
hand-rolled coordinate pass should re-solve. A multi-operand hyperedge meets at a
small diamond junction node — the standard drawing of a hyperedge in a binary-edge
grammar — with arrowhead-suppressed legs from the operands and one arrowed leg to the
result: legs stay directed so the layered engine orders operands before the junction
and the junction before the result. A junction whose operands and result all live in
one level nests inside that level's container — a hyperedge interior to a step is
drawn interior to its box, not routed out and back in.
-/
import PropertyKindCalculus.KindIncidence

namespace PropertyKindCalculus.KindGraphD2

open PropertyKindCalculus.Provenance (Port Intro Occurrence EdgeFamily IntroTier PortDir)
open PropertyKindCalculus.KindIncidence (Assembly AssemblyLevel)

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
  | .tableMul => "[T]·"
  | .tableDiv => "[T]/"
  | .copy => ""
  | .step nm _ => s!"[{nm}]"

/-- The arrow color of an edge family: identity wires gray, procedure edges indigo,
witness edges near-black. -/
def familyStroke : EdgeFamily → String
  | .copy => "#9ca3af"
  | .step _ _ => "#4f46e5"
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

/-- One row of a level's container: the graph node it stands for, its container-local
key (the level's namespace prefix stripped), display label, fill and border colors,
and the attested reason as an optional tooltip. -/
structure Row where
  node : String
  key : String
  label : String
  fill : String
  stroke : String
  tooltip : Option String
deriving Inhabited

/-- The rows of one level: ports in graph order, the signature's unkinded positions in
red, then introduction events, exits marked `⊗` at the erasure boundary. -/
def levelRows (l : AssemblyLevel) : Array Row := Id.run do
  let strip (n : String) : String :=
    if n.startsWith (l.name ++ "/") then (n.drop (l.name.length + 1)).toString else n
  let exitMark (n : String) : String :=
    if l.graph.exits.contains n then " ⊗" else ""
  let mut rows : Array Row := #[]
  for p in l.graph.ports do
    rows := rows.push
      ⟨p.node, strip p.node,
        s!"{p.dir.label} {strip p.node} : {p.kind}{exitMark p.node}",
        portFill p.dir, portStroke p.dir, none⟩
  for u in l.unkinded do
    rows := rows.push
      ⟨u.node, strip u.node,
        s!"unkinded {u.dir.label} {strip u.node} : {u.type}",
        unkindedFill, unkindedStroke, none⟩
  for i in l.graph.intros do
    let tip := match i.tier with
      | .attested r => some r
      | _ => none
    rows := rows.push
      ⟨i.node, strip i.node,
        s!"{tierShortLabel i.tier} {strip i.node} : {i.kind}{exitMark i.node}",
        tierFill i.tier, tierStroke i.tier, tip⟩
  return rows

/-- Emit the assembly as a D2 document (module header: the figure is a pure rendering
of the checked object; layout is the engine's). -/
def emit (a : Assembly) (title : String := "kind assembly") : String := Id.run do
  let mut out := ""
  let put (s : String) : String := s ++ "\n"
  out := out ++ put "vars: {"
  out := out ++ put "  d2-config: {"
  out := out ++ put "    layout-engine: elk"
  out := out ++ put "  }"
  out := out ++ put "}"
  out := out ++ put "direction: right"
  -- the header claims, pinned outside the drawing: the title; the provenance box —
  -- the evaluated verdict with the assembled declarations and their source files, the
  -- assembly's own provenance beside its judgment; and the shape legend. All three
  -- are plain-text rows chained by invisible edges into rows/columns: a markdown
  -- label would render as a foreignObject HTML island, which librsvg and LaTeX
  -- pipelines silently drop, so the emitted document stays pure SVG
  let ok := a.graph.wellFormed
  let (vc, vt) := if ok then ("#16a34a", "well-formed: true")
    else ("#dc2626", "well-formed: false")
  out := out ++ put ("\"__title\": {label: " ++ q title
    ++ "; shape: text; near: top-center; style: {font-size: 20; bold: true}}")
  let boxStyle := "  style: {stroke: \"#9ca3af\"; fill: \"#ffffff\"; border-radius: 8; font-size: 13; font-color: \"#374151\"}"
  out := out ++ put "\"__provenance\": {"
  out := out ++ put ("  label: " ++ q "assembled from (in list order)")
  out := out ++ put "  near: top-left"
  out := out ++ put "  direction: down"
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
  out := out ++ put "  \"v\" -> \"u\": {style: {opacity: 0}}"
  for i in [0:a.levels.size] do
    let l := a.levels[i]!
    let line := if l.src.isEmpty then s!"{l.decl}" else s!"{l.decl} — {l.src}"
    out := out ++ put ("  " ++ q s!"s{i}" ++ ": {label: " ++ q line
      ++ "; shape: text; style: {font-size: 12; font: mono; font-color: \"#374151\"}}")
  let mut prev := "\"u\""
  for i in [0:a.levels.size] do
    let cur := q s!"s{i}"
    out := out ++ put ("  " ++ prev ++ " -> " ++ cur ++ ": {style: {opacity: 0}}")
    prev := cur
  out := out ++ put "}"
  out := out ++ put "\"__legend\": {"
  out := out ++ put ("  label: " ++ q "legend")
  out := out ++ put "  near: bottom-center"
  out := out ++ put "  direction: right"
  out := out ++ put boxStyle
  let swatches : Array (String × String × String) :=
    #[("input port", portFill .input, portStroke .input),
      ("config port", portFill .config, portStroke .config),
      ("output port", portFill .output, portStroke .output),
      ("conditional output", portFill .conditional, portStroke .conditional),
      ("derived", tierFill .derived, tierStroke .derived),
      ("gated", tierFill .gated, tierStroke .gated),
      ("attested ⓘ", tierFill (.attested ""), tierStroke (.attested "")),
      ("unkinded", unkindedFill, unkindedStroke)]
  for i in [0:swatches.size] do
    let (lbl, f, s) := swatches[i]!
    out := out ++ put ("  " ++ q s!"sw{i}" ++ ": {label: " ++ q lbl
      ++ "; style: {fill: " ++ q f ++ "; stroke: " ++ q s
      ++ "; border-radius: 6; font-size: 12}}")
    if i > 0 then
      out := out ++ put ("  " ++ q s!"sw{i-1}" ++ " -> " ++ q s!"sw{i}"
        ++ ": {style: {opacity: 0}}")
  let samples : Array (String × String × String) :=
    #[("witness", "#111827", ""),
      ("procedure [step]", "#4f46e5", ""),
      ("identity wire", "#9ca3af", ""),
      ("citation", "#4f46e5", "; stroke-dash: 4"),
      ("unkinded flow", unkindedStroke, "")]
  for i in [0:samples.size] do
    let (lbl, stroke, dash) := samples[i]!
    let dot := ": {label: \"\"; shape: circle; width: 10; height: 10; style: {fill: "
      ++ q stroke ++ "; stroke: " ++ q stroke ++ "}}"
    out := out ++ put ("  " ++ q s!"l{i}a" ++ dot)
    out := out ++ put ("  " ++ q s!"l{i}b" ++ dot)
    out := out ++ put ("  " ++ q s!"l{i}a" ++ " -> " ++ q s!"l{i}b" ++ ": {label: "
      ++ q lbl ++ "; style: {stroke: " ++ q stroke ++ dash
      ++ "; font-size: 12; font-color: \"#374151\"}}")
    if i > 0 then
      out := out ++ put ("  " ++ q s!"l{i-1}b" ++ " -> " ++ q s!"l{i}a"
        ++ ": {style: {opacity: 0}}")
  out := out ++ put ("  \"note\": {label: "
    ++ q "⊗ exit at the erasure boundary · ⓘ carries the attested reason · red = outside the kinded algebra"
    ++ "; shape: text; style: {font-size: 12; font-color: \"#374151\"}}")
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
  -- the citation relation, dashed between containers — drawn, never wired
  for (src, dst) in a.cites do
    out := out ++ put (s!"{q src} -> {q dst}: "
      ++ "{style: {stroke: \"#4f46e5\"; stroke-dash: 4; opacity: 0.6}}")
  return out

end PropertyKindCalculus.KindGraphD2
