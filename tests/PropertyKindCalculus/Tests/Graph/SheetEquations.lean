/-
# Validation probes — `SheetEquations` (the assembly rendered as TeX equations)

The renderers are pure functions of occurrence values, so their claims are decidable on
hand-built occurrences — one per rendering rule worth fixing:

  * the `op` field is what makes the rendering value-honest: an `additive` renders `+`
    or `-` only by the recorded scalar head, and an anonymous op renders the family's
    own name — stated ignorance, never an invented sign;
  * node TeX keeps synthesized projections distinct (`t_{1}.fst` vs `t_{1}.snd`) and
    escapes underscores;
  * lines come out in dependency order even when the walk emitted a definition after
    its use.
-/
import PropertyKindCalculus.Graph.SheetEquations

namespace PropertyKindCalculus.Tests.SheetEquations

open PropertyKindCalculus.SheetEquations
open PropertyKindCalculus.Provenance (NodeId KindRef Occurrence)

/-- A member-local named node. -/
def nd (s : String) : NodeId := { root := .letBound s }
/-- A synthesized node, optionally projected. -/
def fr (k : Nat) (path : List String := []) : NodeId := { root := .fresh k, path }

def kx : KindRef := .decl `kx

/-! ## Node TeX -/

#guard texOfNode (nd "theta") == "\\mathit{theta}"
#guard texOfNode (nd "eps_b") == "\\mathit{eps\\_b}"
#guard texOfNode (fr 1) == "t_{1}"
#guard texOfNode (fr 1 ["fst"]) != texOfNode (fr 1 ["snd"])
#guard texOfNode { root := .const `A.B.table, path := ["lo"] } == "\\mathrm{table.lo}"

/-! ## The op field decides the sign; ignorance is stated, never invented -/

def addO : Occurrence NodeId KindRef :=
  ⟨.additive, [(nd "a", kx), (nd "b", kx)], nd "s", kx, "probe", ``HAdd.hAdd⟩
def subO : Occurrence NodeId KindRef :=
  ⟨.additive, [(nd "a", kx), (nd "b", kx)], nd "d", kx, "probe", ``HSub.hSub⟩
def anonO : Occurrence NodeId KindRef :=
  ⟨.additive, [(nd "a", kx), (nd "b", kx)], nd "u", kx, "probe", .anonymous⟩

#guard texOfOccurrence addO == "\\mathit{a} + \\mathit{b}"
#guard texOfOccurrence subO == "\\mathit{a} - \\mathit{b}"
#guard texOfOccurrence anonO == "\\operatorname{additive}(\\mathit{a}, \\mathit{b})"

-- A transcendental names its discharging declaration as the operator, and that
-- declaration is the line's link.
def sinO : Occurrence NodeId KindRef :=
  ⟨.transcendental, [(nd "theta", kx)], nd "kx", kx, "probe", `Probe.sinQ⟩
#guard texOfOccurrence sinO == "\\operatorname{sinQ}(\\mathit{theta})"
#guard opOfOccurrence sinO == `Probe.sinQ

-- A step renders its callee applied; the callee is the link even with no recorded op.
def stepO : Occurrence NodeId KindRef :=
  ⟨.step `Probe.fwd none 2, [(nd "x", kx), (nd "y", kx)], nd "z", kx, "probe", .anonymous⟩
#guard texOfOccurrence stepO == "\\operatorname{fwd}(\\mathit{x}, \\mathit{y})"
#guard opOfOccurrence stepO == `Probe.fwd

-- The structural forms.
#guard texOfOccurrence
    ⟨.quotient, [(nd "a", kx), (nd "b", kx)], nd "q", kx, "probe", `Probe.divQ⟩
  == "\\frac{\\mathit{a}}{\\mathit{b}}"
#guard texOfOccurrence
    ⟨.power (1/2 : Rat), [(fr 1, kx)], nd "r", kx, "probe", `Probe.sqrtQ⟩
  == "t_{1}^{1 / 2}"
#guard texOfOccurrence ⟨.copy, [(nd "a", kx)], nd "b", kx, "probe", .anonymous⟩
  == "\\mathit{a}"

/-! ## Dependency order: the definition of `t_1` lands before its use -/

def useFirst : List (Occurrence NodeId KindRef) :=
  [⟨.power (1/2 : Rat), [(fr 1, kx)], nd "r", kx, "probe", `Probe.sqrtQ⟩,
   ⟨.additive, [(nd "one", kx), (nd "kx2", kx)], fr 1, kx, "probe", ``HSub.hSub⟩]

#guard (dependencyOrder useFirst).map (·.result) == [fr 1, nd "r"]

end PropertyKindCalculus.Tests.SheetEquations
