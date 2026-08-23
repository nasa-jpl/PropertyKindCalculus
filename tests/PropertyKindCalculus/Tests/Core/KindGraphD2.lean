/-
# Validation probes — `KindGraphD2` (the generated assembly figure)

The emitter is a pure function of the `Assembly` value, so its claims are decidable by
evaluation on a hand-built assembly: the document requests the ELK layered engine;
each level emits as a container labeled with its inclusion mode, an interface level's
border dashed; every node row carries its role or tier and its kind, an attested row
carrying its reason as the tooltip; a multi-operand procedure edge meets at a diamond
junction with undirected legs in and one arrowed leg out carrying the step name; the
identity wire draws gray; the citation relation draws dashed; and the header repeats
the evaluated verdict — the figure is generated from the checked object, never drawn
beside it.
-/
import PropertyKindCalculus.KindGraphD2

namespace PropertyKindCalculus.Tests.KindGraphD2

open PropertyKindCalculus
open PropertyKindCalculus.KindIncidence (Assembly AssemblyLevel)
open PropertyKindCalculus.KindGraphD2

/-- Does `sub` occur in `s`? Evaluation-only probe helper. -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The hand-built two-box assembly of the core probes: caller `A` wired into callee
`B` by a two-operand procedure edge, an attested source carrying its reason, and one
exit. -/
def probe : Assembly :=
  let gA : Provenance String String :=
    { ports := [⟨"A/x", "kx", .input⟩, ⟨"A/y", "ky", .input⟩,
                ⟨"A/result", "kz", .output⟩]
      intros := [⟨"A/seed", "kx", .attested "vendor sheet"⟩]
      occurrences := [⟨.step "B" 2, [("A/x", "kx"), ("A/y", "ky")], "A/result", "kz", "A"⟩]
      exits := ["A/x"] }
  let gB : Provenance String String :=
    { ports := [⟨"B/result", "kz", .output⟩]
      intros := [⟨"B/x", "kx", .derived⟩]
      occurrences := [⟨.step "B" 1, [("B/x", "kx")], "B/result", "kz", "B"⟩]
      exits := [] }
  let wires : Provenance String String :=
    ⟨[], [], [⟨.copy, [("A/x", "kx")], "B/x", "kx", "A"⟩], []⟩
  { levels := #[⟨`A, "A", true, gA⟩, ⟨`B, "B", false, gB⟩]
    graph := (gA.union gB).union wires
    cites := #[("A", "B")] }

/-- The emitted document. -/
def d2 : String := emit probe (title := "probe assembly")

#guard d2.startsWith "vars: {"
#guard hasSub d2 "layout-engine: elk"
#guard hasSub d2 "direction: right"
-- the header repeats the evaluated judgment on the object
#guard probe.graph.wellFormed
#guard hasSub d2 "well-formed: true"
#guard hasSub d2 "label: \"probe assembly\""
-- containers carry their names and inclusion modes; interface borders dash
#guard hasSub d2 "label: \"A (walked)\""
#guard hasSub d2 "label: \"B (interface)\""
#guard hasSub d2 "stroke-dash: 2"
-- rows carry roles, tiers, kinds; the attested reason is the tooltip; exits mark ⊗
#guard hasSub d2 "label: \"input x : kx ⊗\""
#guard hasSub d2 "label: \"output result : kz\""
#guard hasSub d2 "label: \"derived x : kx\""
#guard hasSub d2 "tooltip: \"vendor sheet\""
-- the two-operand procedure edge meets at a diamond junction: undirected legs in,
-- one arrowed leg out carrying the step name
#guard hasSub d2 "\"__j0\": {label: \"\"; shape: diamond"
#guard hasSub d2 "\"A\".\"x\" -- \"__j0\""
#guard hasSub d2 "\"A\".\"y\" -- \"__j0\""
#guard hasSub d2 "\"__j0\" -> \"A\".\"result\": {label: \"[B]\""
-- the identity wire draws gray; the citation draws dashed between the containers
#guard hasSub d2 "\"A\".\"x\" -> \"B\".\"x\": {style: {stroke: \"#9ca3af\""
#guard hasSub d2 "\"A\" -> \"B\": {style: {stroke: \"#4f46e5\"; stroke-dash: 4"

end PropertyKindCalculus.Tests.KindGraphD2
