/-
# Validation probes — `KindGraphSvg` (the generated assembly figure)

The renderer is a pure function of the `Assembly` value, so its claims are decidable by
evaluation on a hand-built assembly: the document is a single self-contained `<svg>`;
each level renders as a titled box carrying its inclusion mode; every node row carries
its role or tier and its kind, an attested row carrying its reason as the tooltip; a
procedure edge is labeled with its step name; the citation relation renders dashed; and
the header repeats the evaluated verdict — the figure is generated from the checked
object, never drawn beside it.
-/
import PropertyKindCalculus.KindGraphSvg

namespace PropertyKindCalculus.Tests.KindGraphSvg

open PropertyKindCalculus
open PropertyKindCalculus.KindIncidence (Assembly AssemblyLevel)
open PropertyKindCalculus.KindGraphSvg

/-- Does `sub` occur in `s`? Evaluation-only probe helper. -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The hand-built two-box assembly of the core probes: caller `A` wired into callee
`B`, an attested source carrying its reason, and one exit. -/
def probe : Assembly :=
  let gA : Provenance String String :=
    { ports := [⟨"A/x", "kx", .input⟩, ⟨"A/result", "ky", .output⟩]
      intros := [⟨"A/seed", "kx", .attested "vendor sheet"⟩]
      occurrences := [⟨.step "B" 1, [("A/x", "kx")], "A/result", "ky", "A"⟩]
      exits := ["A/x"] }
  let gB : Provenance String String :=
    { ports := [⟨"B/result", "ky", .output⟩]
      intros := [⟨"B/x", "kx", .derived⟩]
      occurrences := [⟨.step "B" 1, [("B/x", "kx")], "B/result", "ky", "B"⟩]
      exits := [] }
  let wires : Provenance String String :=
    ⟨[], [], [⟨.copy, [("A/x", "kx")], "B/x", "kx", "A"⟩], []⟩
  { levels := #[⟨`A, "A", true, gA⟩, ⟨`B, "B", false, gB⟩]
    graph := (gA.union gB).union wires
    cites := #[("A", "B")] }

/-- The rendered document. -/
def svg : String := render probe (title := "probe assembly")

#guard svg.startsWith "<svg xmlns=\"http://www.w3.org/2000/svg\""
#guard hasSub svg "</svg>"
-- the verdict chip repeats the evaluated judgment on the object
#guard probe.graph.wellFormed
#guard hasSub svg ">well-formed: true</text>"
-- boxes carry their names and inclusion modes
#guard hasSub svg "A <tspan"
#guard hasSub svg "(walked)"
#guard hasSub svg "(interface)"
-- rows carry roles, tiers, kinds; the attested reason is the tooltip; exits mark ⊗
#guard hasSub svg "input x : kx ⊗"
#guard hasSub svg "output result : ky"
#guard hasSub svg "derived x : kx"
#guard hasSub svg "<title>vendor sheet</title>attested seed : kx"
-- the procedure edge is labeled with its step name; the citation renders dashed
#guard hasSub svg ">[B]</text>"
#guard hasSub svg "class=\"cite\""
#guard hasSub svg "class=\"wire\""

end PropertyKindCalculus.Tests.KindGraphSvg
