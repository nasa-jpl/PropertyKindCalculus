/-
# Validation probes — `KindGraphD2` (the generated assembly figure)

The emitter is a pure function of the `Assembly` value, so its claims are decidable by
evaluation on a hand-built assembly: the document requests the ELK layered engine;
each level emits as a container labeled with its inclusion mode, an interface level's
border dashed; every node row carries its role or tier and its kind, an attested row
carrying its reason as the tooltip; a multi-operand procedure edge meets at a diamond
junction — arrowhead-suppressed directed legs in, one arrowed leg out carrying the
step name — nested inside the level container when the hyperedge is interior to it
and at top level when it spans levels; the identity wire draws gray; the citation
relation draws dashed; an unkinded signature position draws as a red row and an
unkinded flow as a red arrow, the provenance box pairing the wiring verdict with the
unkinded count; and the header repeats
the evaluated verdict — the figure is generated from the checked object, never drawn
beside it.
-/
import PropertyKindCalculus.KindGraphD2

namespace PropertyKindCalculus.Tests.KindGraphD2

open PropertyKindCalculus
open PropertyKindCalculus.Provenance (NodeId KindRef)
open PropertyKindCalculus.KindIncidence (Assembly AssemblyLevel citeEdges)
open PropertyKindCalculus.KindGraphD2

/-- Does `sub` occur in `s`? Evaluation-only probe helper. -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The hand-built two-box assembly of the core probes: caller `A` wired into callee
`B` by a two-operand procedure edge interior to `A`, a cross-level product occurrence
spanning both boxes, an attested source carrying its reason, one exit, and the red
reading — an unkinded argument `n : Nat` on `A` whose flows reach the attested mint
and the output. -/
def probe : Assembly :=
  let ax := (NodeId.binder "x").within `A
  let ay := (NodeId.binder "y").within `A
  let ares := NodeId.result.within `A
  let aseed := (NodeId.letBound "seed").within `A
  let bx := (NodeId.letBound "x").within `B
  let bres := NodeId.result.within `B
  let kx : KindRef := .decl `kx
  let ky : KindRef := .decl `ky
  let kz : KindRef := .decl `kz
  let gA : Provenance NodeId KindRef :=
    { ports := [⟨ax, kx, .input⟩, ⟨ay, ky, .input⟩,
                ⟨(NodeId.config `Probe.Ns.tableC).field "lo", kx, .config⟩,
                ⟨(NodeId.config `Probe.One.dup).field "q", kx, .config⟩,
                ⟨(NodeId.config `Probe.Two.dup).field "q", kx, .config⟩,
                ⟨ares, kz, .output⟩]
      intros := [⟨aseed, kx, .attested "vendor sheet"⟩]
      occurrences := [⟨.step `B none 2, [(ax, kx), (ay, ky)], ares, kz, "A"⟩]
      exits := [ax] }
  let gB : Provenance NodeId KindRef :=
    { ports := [⟨bres, kz, .output⟩]
      intros := [⟨bx, kx, .derived⟩]
      occurrences := [⟨.step `B none 1, [(bx, kx)], bres, kz, "B"⟩]
      exits := [] }
  let wires : Provenance NodeId KindRef :=
    ⟨[], [], [⟨.copy, [(ax, kx)], bx, kx, "A"⟩,
              ⟨.product, [(ay, ky), (bx, kx)], bres, kz, "A"⟩], []⟩
  { levels := #[⟨`A, "A", .inst `A 1, true, gA, "src/a.lean", [⟨"A/n", "Nat", .input⟩],
                 [("A/n", aseed), ("A/n", ares)]⟩,
                ⟨`B, "B", .inst `B 1, false, gB, "", [], []⟩]
    graph := (gA.union gB).union wires
    cites := #[(`A, `B)] }

/-- The emitted document. -/
def d2 : String := emit probe (title := "probe assembly")

#guard d2.startsWith "vars: {"
#guard hasSub d2 "layout-engine: dagre"
#guard hasSub d2 "direction: right"
-- the provenance box: the evaluated judgment beside the assembled declarations and
-- their source files — the module name line when a source resolves, the bare
-- declaration when unattributed
#guard probe.graph.wellFormed
#guard hasSub d2 "well-formed: true"
#guard hasSub d2 "label: \"probe assembly\""
#guard hasSub d2 "\"__provenance\": {"
-- a grid of one column: a chained column is a layered graph, and the engine spaces it
-- like one
#guard hasSub d2 "  grid-columns: 1"
#guard !hasSub d2 "\"v\" -> \"u\""
#guard hasSub d2 "label: \"assembled from (in list order)\""
#guard hasSub d2 "label: \"A\\n  src/a.lean\""
#guard hasSub d2 "\"s1\": {label: \"B\";"
-- the shape legend is a two-column table of grids — the row palette beside the arrow
-- classes, so it reads as a caption and not as a strip the width of the drawing. Cells
-- are packed by the grid, so no invisible edge orders them
#guard hasSub d2 "\"__legend\": {"
#guard hasSub d2 "  grid-columns: 2"
#guard hasSub d2 "label: \"node rows\""
#guard hasSub d2 "label: \"arrow classes (line colour)\""
#guard hasSub d2 "label: \"input port\""
#guard hasSub d2 "label: \"attested ⓘ\"; style: {fill: \"#fde68a\""
-- an arrow class is its line colour on a pill's border, not a drawn arrow
#guard hasSub d2 "label: \"citation (dashed)\"; style: {fill: \"#ffffff\"; stroke: \"#4f46e5\"; stroke-width: 3; stroke-dash: 4"
-- containers carry their names and inclusion modes; interface borders dash
#guard hasSub d2 "label: \"A (walked)\""
#guard hasSub d2 "label: \"B (interface)\""
#guard hasSub d2 "stroke-dash: 2"
-- rows carry roles, tiers, kinds; the attested reason is the tooltip; exits mark ⊗
#guard hasSub d2 "label: \"input x : kx ⊗\""
#guard hasSub d2 "label: \"output result : kz\""
#guard hasSub d2 "label: \"derived x : kx\""
#guard hasSub d2 "tooltip: \"vendor sheet\""
-- the procedure edge interior to `A` meets at a junction nested inside `A`'s
-- container: arrowhead-suppressed directed legs in, one arrowed leg out carrying the
-- step name
#guard hasSub d2 "\"A\".\"__j0\": {label: \"\"; shape: diamond"
#guard hasSub d2 "\"A\".\"x\" -> \"A\".\"__j0\": {style: {stroke: \"#4f46e5\"}; target-arrowhead: {shape: none}}"
#guard hasSub d2 "\"A\".\"y\" -> \"A\".\"__j0\""
#guard hasSub d2 "\"A\".\"__j0\" -> \"A\".\"result\": {label: \"[B]\""
-- the cross-level product occurrence meets at a top-level junction
#guard hasSub d2 "\"__j1\": {label: \"\"; shape: diamond"
#guard hasSub d2 "\"A\".\"y\" -> \"__j1\""
#guard hasSub d2 "\"B\".\"x\" -> \"__j1\""
#guard hasSub d2 "\"__j1\" -> \"B\".\"result\": {label: \"·\""
-- the identity wire draws gray; the citation draws dashed between the containers
#guard hasSub d2 "\"A\".\"x\" -> \"B\".\"x\": {style: {stroke: \"#9ca3af\""
#guard hasSub d2 "\"A\" -> \"B\": {style: {stroke: \"#4f46e5\"; stroke-dash: 4"
-- the red reading: the unkinded position is a red row, its flows red arrows into the
-- mint and the output, the provenance box pairs the verdict with the count, and the
-- legend states the color's meaning
#guard hasSub d2 "label: \"unkinded input n : Nat\"; style: {fill: \"#fee2e2\"; stroke: \"#dc2626\""
#guard hasSub d2 "\"A\".\"n\" -> \"A\".\"seed\": {style: {stroke: \"#dc2626\"}}"
#guard hasSub d2 "\"A\".\"n\" -> \"A\".\"result\": {style: {stroke: \"#dc2626\"}}"
#guard hasSub d2 "unkinded positions: 1 — outside the kinded algebra"
#guard hasSub d2 "label: \"unkinded\"; style: {fill: \"#fee2e2\""
#guard hasSub d2 "label: \"unkinded flow\"; style: {fill: \"#ffffff\"; stroke: \"#dc2626\""
#guard hasSub d2 "red = outside the kinded algebra"

/-! ## The address a label may drop, and the one it may not

A node name is an address; a namespace is not what tells one row from another. The
label drops the leading namespace components — but only where the short form still
identifies the row in its box, so two configuration constants that would shorten to the
same thing both keep their full addresses. The D2 key is the full address either way,
and a shortened row carries it as the tooltip: nothing the figure claims is only in the
label. -/

#guard shortAddr "SoilMoisture.Algorithm.Batch.mironovCoeffsC.ndA0" == "mironovCoeffsC.ndA0"
#guard shortAddr "coeffs.ndA0" == "coeffs.ndA0"
-- always at least the last component, even when every component is a namespace
#guard shortAddr "Outer.Inner" == "Inner"
-- unique in its box: the label shortens, the key stays the address, the tooltip carries it
#guard hasSub d2 "\"Probe.Ns.tableC.lo\": {label: \"config tableC.lo : kx\""
#guard hasSub d2 "tooltip: \"Probe.Ns.tableC.lo\""
-- the two that would collide at `dup.q` both keep their full addresses, and neither
-- gets a tooltip it does not need
#guard hasSub d2 "label: \"config Probe.One.dup.q : kx\""
#guard hasSub d2 "label: \"config Probe.Two.dup.q : kx\""
#guard !hasSub d2 "tooltip: \"Probe.One.dup.q\""

/-! ## A citation names a member, and a member can be several levels

The citation relation is harvested per declaration, so it names a *member*. A member
dissected at three call sites is three levels, and a member the assembly never included
is no level at all — drawing either name straight would put a box in the figure that the
checked object does not have. Both endpoints resolve to levels first. -/

/-- An assembly whose citations name a dissected member and a member that is not
there. -/
def instanced : Assembly :=
  let g : Provenance NodeId KindRef := ⟨[], [], [], []⟩
  { levels := #[⟨`A, "A", .inst `A 1, true, g, "", [], []⟩,
                ⟨`B, "B#1", .inst `B 1, false, g, "", [], []⟩,
                ⟨`B, "B#2", .inst `B 2, false, g, "", [], []⟩]
    graph := g
    cites := #[(`A, `B), (`A, `notAMember)] }

#guard citeEdges instanced == #[("A", "B#1"), ("A", "B#2")]
#guard !hasSub (emit instanced) "\"notAMember\""

/-! ## The overview — the same object at the scale of its steps

`emitOverview` reads the assembled value at the scale of its members: one box per
level with its interface tally and its unkinded count, one arrow per pair of levels
information crosses between with how many wires cross, the citation dashed. It shares
the preamble with the full figure, so the two carry the same verdict and the same
provenance; and it is emitted from the same value, so a member the contract does not
declare cannot appear in it either. -/

/-- The overview document of the same probe. -/
def ov : String := emitOverview probe (title := "probe assembly")

#guard hasSub ov "label: \"probe assembly — overview\""
#guard hasSub ov "well-formed: true"
#guard hasSub ov "layout-engine: dagre"
-- `A` is walked, states 2 inputs and 3 configuration ports, 1 output, 1 interior
-- introduction, and one unkinded position — so its box is red and says so
#guard hasSub ov "\"A\": {label: \"A\\nwalked · 8 nodes\\n2 in · 3 config · 1 out · 1 interior\\n⚠ 1 unkinded\"; style: {fill: \"#fee2e2\""
-- `B` entered at its signature: dashed, and nothing red
#guard hasSub ov "\"B\": {label: \"B\\ninterface · 2 nodes\\n0 in · 0 config · 1 out · 1 interior\"; style: {fill: \"#f9fafb\""
#guard hasSub ov "stroke-dash: 2"
-- two occurrences carry information from `A` into `B` — the identity wire and the
-- product — so the crossing is one arrow labelled with its count
#guard hasSub ov "\"A\" -> \"B\": {label: \"2 wires\""
-- and the citation stays dashed, drawn but never wired
#guard hasSub ov "\"A\" -> \"B\": {style: {stroke: \"#4f46e5\"; stroke-dash: 4"
-- the overview's legend is one text block: it explains the boxes, not the palette
#guard hasSub ov "solid border — the walk read this member's body"
#guard hasSub ov "dashed arrow — a citation: referenced, never wired"

end PropertyKindCalculus.Tests.KindGraphD2
