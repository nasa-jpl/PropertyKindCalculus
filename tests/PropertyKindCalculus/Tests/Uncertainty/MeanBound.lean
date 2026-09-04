/-
# Validation probes — the weighted mean at binary32 (R9 × R18)

The capstone `mean_fp32_within_errBound` bounds the gap between a mean computed on the binary32
grid and the exact real mean of the same data. Three dangers, three probes.

**A bound is worthless if nothing satisfies its hypotheses.** It asks for two licenses — the
rounded total nonzero and the exact total nonzero — so the probe builds a carving that discharges
both by arithmetic, and applies the theorem to it. A single-part carving suffices to make the
statement non-vacuous *and* exercises both nonlinear nodes: the budget it produces is
`eps32 (w·v)/|w| + eps32 ((w·v)/w)`, one rounding at the product and one at the quotient, with the
quotient rule's `1/|w|` factor on the first.

**An induction is worthless if it is never entered.** The compilation lemmas and the regularity of
the two folds hold at every carving, so they are driven through a depth-2 union — the join is
where `denExpr`/`numExpr` recurse and where the `add` nodes of the budget come from.

**The two licenses are not one license.** That claim is the reason `specCarving` takes the
specification's license as an argument rather than reading it off the carving, so the probe
exhibits the separation at the executable carrier: three binary32 weights whose exact sum is `1`
and whose binary32 total is exactly `+0`. The exact arithmetic is checked in `Float`, where all
three weights and both partial sums (`16777217`, `1`) are exactly representable, so the binary64
computation *is* the real computation rather than an approximation of it.
-/

import PropertyKindCalculus.Uncertainty.Adequacy.MeanBound

namespace PropertyKindCalculus.Tests.MeanBound

open PropertyKindCalculus
open PropertyKindCalculus.Uncertainty.Adequacy
open TorchLean.Floats
open TorchLean.Floats.IEEE754

/-! ## Inhabitation — a carving that discharges both licenses -/

/-- A one-part carving. -/
def atomParts : Decomposition Bool := .atom true

/-- A two-part carving — the depth that enters the inductive step. -/
def pairParts : Decomposition Bool := .union (.atom true) (.atom false)

/-- Weight 3 at binary32 — an exactly representable magnitude, so no rounding fact is needed to
know the single-part total is 3. -/
noncomputable def w3 : Bool → FP32 := fun _ => ⟨(3 : ℝ)⟩

/-- Value 2 at binary32. -/
noncomputable def v2 : Bool → FP32 := fun _ => ⟨(2 : ℝ)⟩

/-- The carving, with its executable license discharged by arithmetic on the semantic value. -/
noncomputable def carving3 : WeightedCarving FP32 Bool where
  parts := atomParts
  weight := w3
  total_ne_zero := fp32_ne_zero_of_val (by simp [totalWeight, atomParts, Decomposition.fold, w3])

/-- The **specification's** license — a second fact about the same weights, which the carving's
own field does not supply. -/
theorem carving3_spec_license :
    totalWeight (fun p => (carving3.weight p).val) carving3.parts ≠ Carrier.zero := by
  simp [totalWeight, carving3, atomParts, Decomposition.fold, w3, Carrier.zero]

-- Inhabitation: the capstone, applied. Both licenses are discharged above, so this is the bound
-- holding of a carving that exists rather than of a hypothesis.
theorem r9_mean_fp32_bound (ρ : ℕ → FP32) :
    |(carving3.mean v2).val
        - (specCarving carving3 carving3_spec_license).mean (fun p => (v2 p).val)|
      ≤ errBound (meanExpr carving3.weight v2 carving3.parts) ρ :=
  mean_fp32_within_errBound carving3 v2 ρ carving3_spec_license

-- and the bound it is compared against is a genuine budget, not a negative number.
theorem r9_mean_fp32_budget_nonneg (ρ : ℕ → FP32) :
    0 ≤ errBound (meanExpr carving3.weight v2 carving3.parts) ρ :=
  errBound_meanExpr_nonneg _ _ _ ρ

/-! ## The inductive step — the compilation at a join -/

-- The two folds compile correctly through a union, in both interpretations.
theorem r9_den_fp32_depth2 (ρ : ℕ → FP32) :
    evalFP32 (denExpr w3 pairParts) ρ = totalWeight w3 pairParts :=
  evalFP32_denExpr w3 ρ pairParts

theorem r9_num_fp32_depth2 (ρ : ℕ → FP32) :
    evalFP32 (numExpr w3 v2 pairParts) ρ = weightedSum w3 v2 pairParts :=
  evalFP32_numExpr w3 v2 ρ pairParts

theorem r9_den_exact_depth2 (ρ : ℕ → FP32) :
    evalExact (denExpr w3 pairParts) ρ = totalWeight (fun p => (w3 p).val) pairParts :=
  evalExact_denExpr w3 ρ pairParts

theorem r9_num_exact_depth2 (ρ : ℕ → FP32) :
    evalExact (numExpr w3 v2 pairParts) ρ
      = weightedSum (fun p => (w3 p).val) (fun p => (v2 p).val) pairParts :=
  evalExact_numExpr w3 v2 ρ pairParts

-- and both folds are regular at a join with no side condition — only the mean's own `div` node
-- carries one.
theorem r9_folds_regular_depth2 (ρ : ℕ → FP32) :
    Regular (numExpr w3 v2 pairParts) ρ ∧ Regular (denExpr w3 pairParts) ρ :=
  ⟨regular_numExpr w3 v2 ρ pairParts, regular_denExpr w3 ρ pairParts⟩

/-! ## Boundary — the two licenses are independent

Three weights: `2²⁴`, `1`, `−2²⁴`. Their exact sum is `1`. Folded at the executable binary32
carrier in that order, the `1` is absorbed by the first addition and the total is exactly `+0` —
so the specification's license holds and the executable one fails, on the same weights. By
`toReal_add_eq_fp32Round` this executable fold is the binary32 rounding spec's fold on the finite
path, which is the fold `WeightedCarving FP32`'s field is about. -/

/-- `2²⁴` at executable binary32. -/
def bigE : IEEE32Exec := IEEE32Exec.ofBits 0x4B800000

/-- `1` at executable binary32. -/
def oneE : IEEE32Exec := IEEE32Exec.ofBits 0x3F800000

/-- `−2²⁴` at executable binary32. -/
def negBigE : IEEE32Exec := IEEE32Exec.ofBits 0xCB800000

-- The three bit patterns are the values claimed: mantissa × 2^exp reads 2²⁴, 1, −2²⁴.
#guard (IEEE32Exec.toDyadic? bigE).map (fun d => (d.sign, d.mant, d.exp)) == some (false, 8388608, 1)
#guard (IEEE32Exec.toDyadic? oneE).map (fun d => (d.sign, d.mant, d.exp)) == some (false, 8388608, -23)
#guard (IEEE32Exec.toDyadic? negBigE).map (fun d => (d.sign, d.mant, d.exp)) == some (true, 8388608, 1)

-- Absorption: the first addition returns its larger operand unchanged.
#guard (IEEE32Exec.add bigE oneE).toBits == bigE.toBits

-- so the executable total is exactly +0 — the license `WeightedCarving FP32` carries fails.
#guard (IEEE32Exec.add (IEEE32Exec.add bigE oneE) negBigE).toBits == 0

-- while the exact total is 1 — the license the specification carving carries holds. Every value
-- and every partial sum here is exactly representable in binary64, so this Float computation is
-- the real one.
#guard ((16777216.0 : Float) + 1.0) == 16777217.0
#guard (((16777216.0 : Float) + 1.0) - 16777216.0) == 1.0

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.mean_fp32_within_errBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mean_fp32_within_errBound

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.regular_meanExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms regular_meanExpr

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.evalFP32_meanExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalFP32_meanExpr

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.fp32_val_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fp32_val_ne_zero

end PropertyKindCalculus.Tests.MeanBound
