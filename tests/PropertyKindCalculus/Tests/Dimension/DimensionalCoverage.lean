/-
`Tests.Dimension.DimensionalCoverage` — the indexed probe for `#kind_dimensional_coverage`
(the dimensional cross-check of the kind algebra).

One probe world, every verdict class exercised, the full report pinned:

  * `[coherent]` — a dimensioned product (`L · L → L²`), its quotient dual, the half-power
    read back, a dimension-one triple (the trivially-balancing case), and a transcendental
    over a dimension-one kind;
  * `[parametric]` — a ∀-quantified edge (generic vocabulary, no fixed dimensional content);
    the same edge as *hypothesis* must NOT appear — an assumed edge is not authored;
  * `⚠ UNDIMENSIONED` — an edge over a kind with no `DimensionedKind` counterpart;
  * `⚠ CONFLICTING` — a kind two `DimensionedKind` declarations dimension differently;
  * `⚠ INCOHERENT` — the refuted edge: `L · L → L` cannot balance.
-/
import PropertyKindCalculus.DimensionalCoverage

namespace PropertyKindCalculus.Tests.Dimension.Coverage

open PropertyKindCalculus

/-! ## The probe world: kinds, dimension assignments, edges -/

/-- A probe length kind. -/
def probeLen : KindOfProperty := { id := "coverage probe length", scale := .ratio }
/-- A probe area kind (`probeLen²`). -/
def probeArea : KindOfProperty := { id := "coverage probe area", scale := .ratio }
/-- A probe dimension-one kind. -/
def probeNum : KindOfProperty := { id := "coverage probe number", scale := .ratio }
/-- A probe kind deliberately left without a `DimensionedKind` counterpart. -/
def probeBad : KindOfProperty := { id := "coverage probe undimensioned", scale := .ratio }
/-- A probe kind deliberately dimensioned twice, disagreeing. -/
def probeConf : KindOfProperty := { id := "coverage probe conflicted", scale := .ratio }

/-- `probeLen` carries the length dimension. -/
def probeLenDK : DimensionedKind := { kind := probeLen, dim := Dim.length }
/-- `probeArea` carries the area dimension (`L²`). -/
def probeAreaDK : DimensionedKind := { kind := probeArea, dim := Dim.area }
/-- `probeNum` is dimension one. -/
def probeNumDK : DimensionedKind := { kind := probeNum, dim := 1 }
/-- One assignment for `probeConf`: the length dimension … -/
def probeConfDK : DimensionedKind := { kind := probeConf, dim := Dim.length }
/-- … and a disagreeing second assignment: dimension one. The coverage check must flag it. -/
def probeConfDK' : DimensionedKind := { kind := probeConf, dim := 1 }

/-- The coherent product: `L · L → L²`. -/
theorem probe_len_sq : ProductKind probeLen probeLen probeArea := ProductKind.ofRatio _ _ _
/-- The coherent quotient dual: `L² / L → L`. -/
theorem probe_area_div : QuotientKind probeArea probeLen probeLen := QuotientKind.ofRatio _ _ _
/-- The coherent half-power: `(L²)^(1/2) → L`. -/
theorem probe_sqrt : PowerKind (1 / 2) probeArea probeLen := PowerKind.ofRatio _ _ _
/-- The trivially-balancing dimension-one triple. -/
theorem probe_num_sq : ProductKind probeNum probeNum probeNum := ProductKind.ofRatio _ _ _
/-- The coherent transcendental: dimension one in, dimension one out. -/
theorem probe_exp : TranscendentalKind probeNum probeNum := ⟨rfl, rfl⟩

/-- **The refuted edge**: `L · L → L` cannot balance (`1 + 1 ≠ 1` on the length exponent). -/
theorem probe_len_sq_bad : ProductKind probeLen probeLen probeLen := ProductKind.ofRatio _ _ _
/-- The uncovered edge: `probeBad` has no `DimensionedKind`. -/
theorem probe_undim : ProductKind probeLen probeBad probeArea := ProductKind.ofRatio _ _ _
/-- The conflicted edge: `probeConf` is dimensioned twice, disagreeing. -/
theorem probe_conf : ProductKind probeConf probeNum probeConf := ProductKind.ofRatio _ _ _

/-- The parametric edge: generic vocabulary, restated from a hypothesis. The *hypothesis*
occurrence must not be reported (an assumed edge is not authored); the ∀-quantified
*conclusion* reports as `[parametric]`. -/
theorem probe_param (k : KindOfProperty) (h : ProductKind k probeLen probeArea) :
    ProductKind k probeLen probeArea := h

/-! ## The pinned report -/

/--
info: dimensional coverage:
[coherent] probeArea / probeLen → probeLen
[coherent] probeArea ^ 1 / 2 → probeLen
[coherent] probeLen · probeLen → probeArea
[coherent] probeNum · probeNum → probeNum
[coherent] transcendental : probeNum → probeNum
[parametric] k · probeLen → probeArea
⚠ CONFLICTING probeConf · probeNum → probeConf — disagreeing DimensionedKinds for: probeConf
⚠ INCOHERENT probeLen · probeLen → probeLen
⚠ UNDIMENSIONED probeLen · probeBad → probeArea — no DimensionedKind for: probeBad
9 kind edge(s): 5 coherent, 1 parametric, 1 UNDIMENSIONED, 1 INCOHERENT, 1 CONFLICTING — dimensional-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage PropertyKindCalculus.Tests.Dimension.Coverage

end PropertyKindCalculus.Tests.Dimension.Coverage
