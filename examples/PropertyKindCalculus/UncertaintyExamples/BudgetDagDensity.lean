/-
# Worked example — the ×/÷ budget DAG on a genuinely heterogeneous model (block mass density)

`Uncertainty.BudgetDag` closes residual item 2 of `UNCERTAINTY.md` (§4.4's kinded budget,
generalized): "the `ProductKind`/`QuotientKind` edges are threaded through a multi-node graph
rather than a single quadrature". This example exercises the closed residual on the model class
that motivated it — the mass density of a machined block, `ρ = m / ((l·w)·h)`, with **five
distinct kinds** (mass, length, area, volume, mass density) threaded through one budget, every
interior node carrying its own `ProductKind`/`QuotientKind` witness. The Stage-3.4 baseline
`analyzeQ` (`Adequacy/Significance.lean`) covers the *homogeneous-input* case — all inputs at one
shared kind `kᵢ`, one sensitivity kind `kₒ/kᵢ` — so it cannot type this model at all; the DAG
serves it edge by edge.

Three things are checked here:

  * **The `Float` budget reproduces hand-computed GUM.** Leaves seeded from `InputDist.normal`
    descriptors give `ρ = 2500 kg/m³`; the per-occurrence contributions (in `contribsQ` order
    `[m, l, w, h]`) are `ρ` times the relative uncertainties — `[1.0, 2.5, 5.0, 25.0] kg/m³` —
    and their quadrature is `u_c = √657.25 ≈ 25.637 kg/m³`. The recursive per-node quadrature
    `propagateQ` agrees with the flat `combinedQ`-of-`contribsQ` to `Float` tolerance — the
    executable shadow (LadderNesting-style) of the ℝ collapse theorem applied below.
  * **The heterogeneous conflations are type errors.** `#check_failure` probes certify that the
    division's operands cannot be swapped against the `QuotientKind` witness, that a density
    contribution and a mass uncertainty cannot share one quadrature, and that the builder's
    argument kinds cannot be permuted — each a misuse a kind-erased evaluation DAG computes
    without complaint.
  * **The ℝ collapse theorem is applied** (`BudgetExpr.propagateQ_unc_eq_combinedQ`, from
    `BudgetDagLaws`): this file is the *index entry* of the reflection convention — an
    un-indexed reflection never builds and silently rots — and the capstone's axiom profile is
    pinned to the classical trio.

Honest scope. The budget is the first-order GUM law under the independence assumption: quadrature
treats every leaf *occurrence* as an independent input, so a model with a repeated input, and any
input correlation, are not specified by this DAG. The kind witnesses are `ofRatio`-liberal (the
trust model of `QuantityClassification.lean`): the three edges signed here are the author's
metrological claims, made grep-enumerable, not derived facts. And the `Float` `#guard`s are
rounding-tolerant checks of the executable shadow, not proofs — the exact identity lives only in
the ℝ theorem. Mathlib-backed (the ℝ rung, via the rigor import); TorchLean-free.
-/

module

public import PropertyKindCalculus.Uncertainty.BudgetDagLaws
meta import PropertyKindCalculus.Uncertainty.BudgetDagLaws
public import PropertyKindCalculus.Uncertainty
meta import PropertyKindCalculus.Uncertainty
public import Mathlib.Tactic.NormNum
meta import Mathlib.Tactic.NormNum

@[expose] public section Blanket

namespace PropertyKindCalculus.UncertaintyExamples.BudgetDagDensity

open PropertyKindCalculus PropertyKindCalculus.Uncertainty
open PropertyKindCalculus (Quantity ProductKind QuotientKind KindOfProperty)

/-! ## The five kinds of the density budget

All distinct, all ratio-scale. The sanctioned edges are exactly the three witnesses below
(`hArea`, `hVol`, `hDens`) — the model's whole kind algebra, enumerable by grep; the
specifically-forbidden conflations are certified as type errors further down. -/

/-- Mass of the block (SI: kg). -/
def massK : KindOfProperty := { id := "mass", scale := .ratio }

/-- A machined dimension of the block (SI: m). -/
def lengthK : KindOfProperty := { id := "length", scale := .ratio }

/-- Face area of the block, `length·length` (SI: m²). -/
def areaK : KindOfProperty := { id := "area", scale := .ratio }

/-- Volume of the block, `area·length` (SI: m³). -/
def volumeK : KindOfProperty := { id := "volume", scale := .ratio }

/-- Mass density of the block, `mass/volume` (SI: kg/m³). -/
def densityK : KindOfProperty := { id := "mass density", scale := .ratio }

/-- The kind equation `length·length = area` — the witness the `l·w` node carries. -/
theorem hArea : ProductKind lengthK lengthK areaK :=
  ProductKind.ofRatio lengthK lengthK areaK

/-- The kind equation `area·length = volume` — the witness the `(l·w)·h` node carries. -/
theorem hVol : ProductKind areaK lengthK volumeK :=
  ProductKind.ofRatio areaK lengthK volumeK

/-- The kind equation `mass/volume = density` — the witness the root `m / V` node carries. -/
theorem hDens : QuotientKind massK volumeK densityK :=
  QuotientKind.ofRatio massK volumeK densityK

/-- **The write-once density budget tree** `ρ = m / ((l·w)·h)`, over an arbitrary carrier `R`:
one authored form runs at `Float` (the numbers below) and at `ℝ` (the collapse theorem below).
Each interior node carries its kind witness — the per-edge threading of residual item 2. -/
def densityExpr {R : Type} (m : EstimateQ massK R) (l w : EstimateQ lengthK R)
    (h : EstimateQ lengthK R) : BudgetExpr R densityK :=
  .div hDens (.leaf m) (.mul hVol (.mul hArea (.leaf l) (.leaf w)) (.leaf h))

/-! ## Run 1 — the `Float` budget reproduces the hand-computed GUM numbers

Inputs (SI): `m = 0.25 kg (u = 10⁻⁴)`, `l = 0.10 m (u = 10⁻⁴)`, `w = 0.05 m (u = 10⁻⁴)`,
`h = 0.02 m (u = 2·10⁻⁴)`. Hand-computed GUM: `ρ = 0.25/10⁻⁴ = 2500 kg/m³`; the contribution of
each input is `ρ` times its relative uncertainty (`4·10⁻⁴`, `10⁻³`, `2·10⁻³`, `10⁻²`), i.e.
`[1.0, 2.5, 5.0, 25.0] kg/m³`; the combined standard uncertainty is
`u_c = √(1² + 2.5² + 5² + 25²) = √657.25 ≈ 25.637 kg/m³`. -/

/-- The mass descriptor: `Normal(0.25 kg, σ = 10⁻⁴)`. -/
def mDist : InputDist Float := InputDist.normal 0.25 1e-4
/-- The block-length descriptor: `Normal(0.10 m, σ = 10⁻⁴)`. -/
def lDist : InputDist Float := InputDist.normal 0.10 1e-4
/-- The block-width descriptor: `Normal(0.05 m, σ = 10⁻⁴)`. -/
def wDist : InputDist Float := InputDist.normal 0.05 1e-4
/-- The block-height descriptor: `Normal(0.02 m, σ = 2·10⁻⁴)` — the dominant relative input. -/
def hDist : InputDist Float := InputDist.normal 0.02 2e-4

/-- The mass leaf, seeded from its descriptor (`value = mean`, `unc = √variance`). -/
def mEst : EstimateQ massK Float := EstimateQ.ofInputDist mDist
/-- The length leaf. -/
def lEst : EstimateQ lengthK Float := EstimateQ.ofInputDist lDist
/-- The width leaf. -/
def wEst : EstimateQ lengthK Float := EstimateQ.ofInputDist wDist
/-- The height leaf. -/
def hEst : EstimateQ lengthK Float := EstimateQ.ofInputDist hDist

/-- The concrete `Float` budget for the machined block. -/
def densityBudget : BudgetExpr Float densityK := densityExpr mEst lEst wEst hEst

/-- The point density `ρ` (a `Quantity densityK` magnitude — kind-checked before erasure). -/
def rhoVal : Float := (densityBudget.valueQ).magnitude
/-- The four per-leaf-occurrence output contributions, in `contribsQ` order `[m, l, w, h]`. -/
def contribMags : List Float := densityBudget.contribsQ.map (·.magnitude)
/-- The flat quadrature `combinedQ`-of-`contribsQ` — the spec-shaped combined uncertainty. -/
def combinedFlat : Float := (combinedQ densityBudget.contribsQ).magnitude
/-- The recursive per-node quadrature `propagateQ` — the DAG-shaped combined uncertainty. -/
def combinedProp : Float := (densityBudget.propagateQ).unc.magnitude
/-- `propagateQ`'s point value (must be `valueQ` — value propagation is not perturbed). -/
def propVal : Float := (densityBudget.propagateQ).value.magnitude

#eval s!"density budget: ρ = {rhoVal} kg/m³   contributions = {contribMags}   " ++
  s!"u_c(flat) = {combinedFlat}   u_c(propagated) = {combinedProp}   (√657.25 = {Float.sqrt 657.25})"

-- The value: ρ = 0.25 / ((0.10·0.05)·0.02) = 2500 kg/m³, and propagateQ's value agrees.
#guard Float.abs (rhoVal - 2500.0) < 1e-6
#guard Float.abs (propVal - rhoVal) < 1e-12
-- The four contributions, in per-occurrence order [m, l, w, h]: ρ · (4e-4, 1e-3, 2e-3, 1e-2).
#guard contribMags.length == 4
#guard Float.abs (contribMags[0]! - 1.0) < 1e-6      -- 2500 · (1e-4 / 0.25)
#guard Float.abs (contribMags[1]! - 2.5) < 1e-6      -- 2500 · (1e-4 / 0.10)
#guard Float.abs (contribMags[2]! - 5.0) < 1e-6      -- 2500 · (1e-4 / 0.05)
#guard Float.abs (contribMags[3]! - 25.0) < 1e-6     -- 2500 · (2e-4 / 0.02)
-- Their quadrature is the GUM combined standard uncertainty u_c = √657.25 ≈ 25.637 kg/m³.
#guard Float.abs (combinedFlat - Float.sqrt 657.25) < 1e-6
#guard Float.abs (combinedFlat - 25.6369) < 1e-3
-- The executable shadow of the ℝ collapse theorem (LadderNesting-style): the recursive
-- per-node quadrature agrees with the flat quadrature of the contribution list to Float
-- tolerance — the same identity `propagateQ_unc_eq_combinedQ` proves exactly over ℝ below.
#guard Float.abs (combinedProp - combinedFlat) < 1e-9

/-! ## The heterogeneous conflations are type errors

Each `#check_failure` is a misuse a kind-erased evaluation DAG would compute without complaint.
First the well-typed reference: the explicit tree `densityExpr` abbreviates. -/

#check (BudgetExpr.div hDens (.leaf mEst)
  (.mul hVol (.mul hArea (.leaf lEst) (.leaf wEst)) (.leaf hEst)) : BudgetExpr Float densityK)

/-- A volume estimate (the machined block's nominal `10⁻⁴ m³`), used only to *attempt* the
swapped division below. -/
def volEst : EstimateQ volumeK Float := { value := ⟨1e-4⟩, unc := ⟨1e-6⟩ }

-- FORBIDDEN: swap the division's operands — volume/mass is not the quotient the
-- `QuotientKind massK volumeK densityK` witness signs, so neither leaf typechecks.
#check_failure BudgetExpr.div hDens (.leaf volEst) (.leaf mEst)

/-- One well-typed density contribution (the head of `contribsQ`, kind `densityK`). -/
def oneDensityContribution : Quantity densityK Float := densityBudget.contribsQ.headD ⟨0.0⟩

/-- The mass input's standard uncertainty at the *mass* kind — an input-side quantity. -/
def massUnc : Quantity massK Float := stdUncQ (k := massK) mDist.moments

-- FORBIDDEN: heterogeneous quadrature — a density contribution and a mass uncertainty cannot
-- share one `combinedQ` list; quadrature demands homogeneity at the output kind.
#check_failure combinedQ [oneDensityContribution, massUnc]

-- FORBIDDEN: a mass estimate where a length is demanded (and a length where a mass is) — the
-- builder's argument kinds are fixed, so swapped arguments do not elaborate.
#check_failure densityExpr lEst mEst wEst hEst

/-! ## Run 2 — the ℝ collapse theorem, applied

The indexed-reflection convention: an un-indexed reflection never builds and silently rots, so
this file is the index entry that keeps `BudgetExpr.propagateQ_unc_eq_combinedQ` applied. The
scoped `instNumCarrierReal` is active because `PropertyKindCalculus.Uncertainty` is open. The
literal ℝ estimates keep the `NonnegUncs` side condition a `norm_num` fact. -/

/-- An ℝ mass estimate `2 ± 1/10` (literal magnitudes; the collapse is shape-generic). -/
noncomputable def mR : EstimateQ massK ℝ := ⟨⟨2⟩, ⟨1/10⟩⟩
/-- An ℝ length estimate `3 ± 1/10`. -/
noncomputable def lR : EstimateQ lengthK ℝ := ⟨⟨3⟩, ⟨1/10⟩⟩
/-- An ℝ width estimate `5 ± 1/10`. -/
noncomputable def wR : EstimateQ lengthK ℝ := ⟨⟨5⟩, ⟨1/10⟩⟩
/-- An ℝ height estimate `7 ± 1/10`. -/
noncomputable def hR : EstimateQ lengthK ℝ := ⟨⟨7⟩, ⟨1/10⟩⟩

/-- The *same* write-once `densityExpr`, instantiated at the proof carrier ℝ. -/
noncomputable def densityExprR : BudgetExpr ℝ densityK := densityExpr mR lR wR hR

/-- All leaf uncertainties of the ℝ budget are nonnegative — `NonnegUncs` unfolds through the
tree by `simp`, leaving the four literal facts `0 ≤ 1/10` to `norm_num`. -/
theorem densityExprR_nonnegUncs : densityExprR.NonnegUncs := by
  norm_num [densityExprR, densityExpr, BudgetExpr.NonnegUncs, mR, lR, wR, hR]

/-- **The collapse, applied.** Over ℝ, the recursive per-node quadrature `propagateQ` computes
*exactly* the flat quadrature of the per-occurrence contribution list — the identity whose
`Float` shadow is `#guard`ed in Run 1. -/
example : (densityExprR.propagateQ).unc = combinedQ densityExprR.contribsQ :=
  BudgetExpr.propagateQ_unc_eq_combinedQ densityExprR densityExprR_nonnegUncs

-- Sorry-free: the capstone's axiom profile is the classical trio, no `sorryAx`.
/-- info: 'PropertyKindCalculus.Uncertainty.BudgetExpr.propagateQ_unc_eq_combinedQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PropertyKindCalculus.Uncertainty.BudgetExpr.propagateQ_unc_eq_combinedQ

end PropertyKindCalculus.UncertaintyExamples.BudgetDagDensity

end Blanket
