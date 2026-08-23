/-
# KindGraphSvg — the assembly figure, generated from the checked object

Dybkær's dissection of a property statement, as a figure a pipeline *generates*: each
assembly level is a box — its ports and interior introduction events as rows, colored
by role and evidence tier, exits marked at the erasure boundary — and the occurrences
of the assembled graph are the arrows: witness edges labeled with their family glyph,
procedure edges with their step name, identity wires drawn thin and gray, the citation
relation dashed between title bars (a reference the walk could not wire is a citation,
never an edge of the checked object). The renderer is a *pure* function of the
`Assembly` value the verdict and the kernel theorem are stated on, so the figure can
never drift from the object: what `#kind_assembly_decide` accepted is what is drawn,
and the verdict chip in the header repeats the evaluated judgment.

Layout is deliberately minimal — boxes flow left to right in level order, wrapping in
rows; arrows are cubic connectors between row anchors with a diamond junction for
multi-operand hyperedges — because the figure's claim is provenance, not aesthetics: a
reader checks which nodes meet at which edges, and every pixel of that answer is
computed from the graph. No external layout engine, no drawing by hand.
-/
import PropertyKindCalculus.KindIncidence

namespace PropertyKindCalculus.KindGraphSvg

open PropertyKindCalculus.Provenance (Port Intro Occurrence EdgeFamily IntroTier PortDir)
open PropertyKindCalculus.KindIncidence (Assembly AssemblyLevel)

/-- XML-escape a rendered fragment. -/
def esc (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '"' => acc ++ "&quot;"
    | c => acc.push c

/-- The bullet color of a port role. -/
def portColor : PortDir → String
  | .input => "#2563eb"
  | .config => "#d97706"
  | .output => "#16a34a"

/-- The bullet color of an introduction tier. -/
def tierColor : IntroTier → String
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
  | .tableMul => "[T]·"
  | .tableDiv => "[T]/"
  | .copy => ""
  | .step nm _ => s!"[{nm}]"

/-- The tier label without the attested reason — the reason becomes the row's
tooltip. -/
def tierShortLabel : IntroTier → String
  | .derived => "derived"
  | .gated => "gated"
  | .attested _ => "attested"

/-- The inclusion-mode label of a level. -/
def modeLabel (l : AssemblyLevel) : String :=
  if l.walked then "walked" else "interface"

/-- One rendered node row: identifier, display text, bullet color, optional tooltip. -/
structure Row where
  node : String
  text : String
  color : String
  tooltip : Option String
deriving Inhabited

/-- A laid-out level box. -/
structure Box where
  name : String
  mode : String
  rows : Array Row
  x : Nat := 0
  y : Nat := 0
  w : Nat := 0
  h : Nat := 0
deriving Inhabited

private def rowH : Nat := 20
private def titleH : Nat := 30
private def padX : Nat := 12
private def padBot : Nat := 10
private def gapX : Nat := 110
private def gapY : Nat := 80
private def marginX : Nat := 30
private def marginY : Nat := 64
private def charW : Nat := 8
private def maxPerRow : Nat := 4

/-- The rows of one level: ports in graph order, then introduction events, exits
marked `⊗` at the erasure boundary, the node's namespace prefix stripped for
display. -/
def levelRows (l : AssemblyLevel) : Array Row := Id.run do
  let strip (n : String) : String :=
    if n.startsWith (l.name ++ "/") then (n.drop (l.name.length + 1)).toString else n
  let exitMark (n : String) : String :=
    if l.graph.exits.contains n then " ⊗" else ""
  let mut rows : Array Row := #[]
  for p in l.graph.ports do
    rows := rows.push
      ⟨p.node, s!"{p.dir.label} {strip p.node} : {p.kind}{exitMark p.node}",
        portColor p.dir, none⟩
  for i in l.graph.intros do
    let tip := match i.tier with
      | .attested r => some r
      | _ => none
    rows := rows.push
      ⟨i.node, s!"{tierShortLabel i.tier} {strip i.node} : {i.kind}{exitMark i.node}",
        tierColor i.tier, tip⟩
  return rows

/-- Lay the boxes out: flowing rows of at most `maxPerRow`, each box sized by its
longest row text. Returns the boxes with positions and the total (width, height). -/
def layout (levels : Array AssemblyLevel) : Array Box × Nat × Nat := Id.run do
  let mut boxes : Array Box := #[]
  for l in levels do
    let rows := levelRows l
    let textMax := rows.foldl (init := l.name.length + (modeLabel l).length + 3)
      fun m r => max m r.text.length
    let w := min 420 (max 190 (textMax * charW + 2 * padX + 12))
    let h := titleH + rows.size * rowH + padBot
    boxes := boxes.push { name := l.name, mode := modeLabel l, rows, w, h }
  -- flow positions
  let mut x := marginX
  let mut y := marginY
  let mut rowMaxH := 0
  let mut inRow := 0
  let mut totalW := 0
  for i in [0:boxes.size] do
    if inRow == maxPerRow then
      x := marginX
      y := y + rowMaxH + gapY
      rowMaxH := 0
      inRow := 0
    boxes := boxes.modify i fun b => { b with x, y }
    x := x + boxes[i]!.w + gapX
    totalW := max totalW x
    rowMaxH := max rowMaxH boxes[i]!.h
    inRow := inRow + 1
  return (boxes, totalW + marginX - gapX, y + rowMaxH + marginY)

/-- The anchor geometry of every node: left x, right x, center y. -/
def anchors (boxes : Array Box) : Std.HashMap String (Nat × Nat × Nat) := Id.run do
  let mut m : Std.HashMap String (Nat × Nat × Nat) := {}
  for b in boxes do
    for i in [0:b.rows.size] do
      let yC := b.y + titleH + i * rowH + rowH / 2
      m := m.insert b.rows[i]!.node (b.x, b.x + b.w, yC)
  return m

/-- A cubic connector between two row anchors, choosing the facing sides. -/
def connector (src dst : Nat × Nat × Nat) (cls : String) (marker : Bool) : String :=
  let (sl, sr, sy) := src
  let (dl, dr, dy) := dst
  let (sx, dx) := if sr < dl then (sr, dl) else if dr < sl then (sl, dr) else (sr, dr + 30)
  let mx := (sx + dx) / 2
  let m := if marker then " marker-end=\"url(#arr)\"" else ""
  if sr < dl || dr < sl then
    s!"<path class=\"{cls}\" d=\"M {sx} {sy} C {mx} {sy} {mx} {dy} {dx} {dy}\"{m}/>"
  else
    -- same box (or overlapping): bulge out past the right edge
    s!"<path class=\"{cls}\" d=\"M {sx} {sy} C {sx + 34} {sy} {dx + 4} {dy} {dr} {dy}\"{m}/>"

/-- Render the assembly as a self-contained SVG document (module header: the figure is
a pure rendering of the checked object). -/
def render (a : Assembly) (title : String := "kind assembly") : String := Id.run do
  let (boxes, w, h) := layout a.levels
  let pos := anchors boxes
  let mut out := ""
  let put (s : String) : String := s ++ "\n"
  out := out ++ put s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{w}\" height=\"{h}\" viewBox=\"0 0 {w} {h}\" font-family=\"ui-monospace, SFMono-Regular, Menlo, monospace\" font-size=\"12\">"
  out := out ++ put "<defs><marker id=\"arr\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\"><path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"#111827\"/></marker></defs>"
  out := out ++ put "<style>.edge{stroke:#111827;fill:none;stroke-width:1.4}.wire{stroke:#9ca3af;fill:none;stroke-width:1.1}.proc{stroke:#4f46e5;fill:none;stroke-width:1.8}.cite{stroke:#4f46e5;fill:none;stroke-width:1;stroke-dasharray:5 4;opacity:.55}</style>"
  out := out ++ put s!"<rect x=\"0\" y=\"0\" width=\"{w}\" height=\"{h}\" fill=\"#ffffff\"/>"
  -- header: title and the evaluated verdict
  let ok := a.graph.wellFormed
  let (vc, vt) := if ok then ("#16a34a", "well-formed: true") else ("#dc2626", "well-formed: false")
  out := out ++ put s!"<text x=\"{marginX}\" y=\"30\" font-size=\"15\" font-weight=\"bold\" fill=\"#111827\">{esc title}</text>"
  out := out ++ put s!"<text x=\"{marginX}\" y=\"48\" fill=\"{vc}\">{vt}</text>"
  -- boxes
  for b in boxes do
    out := out ++ put s!"<rect x=\"{b.x}\" y=\"{b.y}\" width=\"{b.w}\" height=\"{b.h}\" rx=\"8\" fill=\"#f9fafb\" stroke=\"#374151\" stroke-width=\"1.3\"/>"
    out := out ++ put s!"<text x=\"{b.x + padX}\" y=\"{b.y + 19}\" font-weight=\"bold\" fill=\"#111827\">{esc b.name} <tspan font-weight=\"normal\" fill=\"#6b7280\">({b.mode})</tspan></text>"
    out := out ++ put s!"<line x1=\"{b.x}\" y1=\"{b.y + titleH - 5}\" x2=\"{b.x + b.w}\" y2=\"{b.y + titleH - 5}\" stroke=\"#d1d5db\"/>"
    for i in [0:b.rows.size] do
      let r := b.rows[i]!
      let yC := b.y + titleH + i * rowH + rowH / 2
      let tip := match r.tooltip with
        | some t => s!"<title>{esc t}</title>"
        | none => ""
      out := out ++ put s!"<circle cx=\"{b.x + padX}\" cy=\"{yC}\" r=\"4\" fill=\"{r.color}\"/>"
      out := out ++ put s!"<text x=\"{b.x + padX + 10}\" y=\"{yC + 4}\" fill=\"#1f2937\">{tip}{esc r.text}</text>"
  -- occurrences: identity wires thin and gray, procedure edges indigo with their step
  -- name, witness edges black with their family glyph; multi-operand hyperedges meet
  -- at a diamond junction
  for o in a.graph.occurrences do
    let some dst := pos.get? o.result | continue
    let srcs := o.operands.filterMap fun oc => pos.get? oc.1
    if srcs.isEmpty then continue
    let cls := match o.family with
      | .copy => "wire"
      | .step _ _ => "proc"
      | _ => "edge"
    let glyph := familyGlyph o.family
    if srcs.length == 1 then
      let src := srcs[0]!
      out := out ++ put (connector src dst cls true)
      unless glyph.isEmpty do
        let (sl, sr, sy) := src
        let (dl, dr, dy) := dst
        let lx := ((if sr < dl then sr else min sl dr) + (if sr < dl then dl else max sl dr)) / 2
        out := out ++ put s!"<text x=\"{lx}\" y=\"{(sy + dy) / 2 - 4}\" fill=\"#4b5563\" text-anchor=\"middle\">{esc glyph}</text>"
    else
      -- diamond junction between the operands' centroid and the result
      let (dl, _, dy) := dst
      let cx := srcs.foldl (init := 0) (fun s (_, sr, _) => s + sr) / srcs.length
      let cy := srcs.foldl (init := 0) (fun s (_, _, sy) => s + sy) / srcs.length
      let jx := (cx + dl) / 2
      let jy := (cy + dy) / 2
      for src in srcs do
        out := out ++ put (connector src (jx - 5, jx - 5, jy) cls false)
      out := out ++ put (connector (jx + 5, jx + 5, jy) dst cls true)
      out := out ++ put s!"<path d=\"M {jx} {jy - 6} L {jx + 6} {jy} L {jx} {jy + 6} L {jx - 6} {jy} z\" fill=\"#ffffff\" stroke=\"#111827\" stroke-width=\"1.2\"/>"
      unless glyph.isEmpty do
        out := out ++ put s!"<text x=\"{jx}\" y=\"{jy - 10}\" fill=\"#4b5563\" text-anchor=\"middle\">{esc glyph}</text>"
  -- the citation relation, dashed between title bars
  let boxOf (n : String) : Option Box := boxes.find? (·.name == n)
  for (src, dst) in a.cites do
    let some sb := boxOf src | continue
    let some db := boxOf dst | continue
    let sy := sb.y + titleH / 2
    let dy := db.y + titleH / 2
    let (sx, dx) :=
      if sb.x + sb.w < db.x then (sb.x + sb.w, db.x)
      else if db.x + db.w < sb.x then (sb.x, db.x + db.w)
      else (sb.x + sb.w, db.x + db.w + 20)
    let mx := (sx + dx) / 2
    out := out ++ put s!"<path class=\"cite\" d=\"M {sx} {sy} C {mx} {sy} {mx} {dy} {dx} {dy}\" marker-end=\"url(#arr)\"/>"
  -- legend
  let ly := h - 18
  out := out ++ put s!"<text x=\"{marginX}\" y=\"{ly}\" fill=\"#6b7280\">● input/config/output ports · introduction tiers (derived / gated / attested — hover for the reason) · ⊗ exit — black: witness edge · indigo: procedure edge · gray: identity wire · dashed: citation</text>"
  out := out ++ put "</svg>"
  return out

end PropertyKindCalculus.KindGraphSvg
