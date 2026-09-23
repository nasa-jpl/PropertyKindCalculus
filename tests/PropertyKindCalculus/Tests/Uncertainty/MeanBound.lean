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

**The two licenses are not one license, in either direction.** That claim is the reason
`specCarving` takes the specification's license as an argument rather than reading it off the
carving, so the probe exhibits *both* separations at the executable carrier — an asserted
independence with one witness would have evidenced only half of it:

  * exact total `1`, binary32 total exactly `+0` (weights `2²⁴`, `1`, `−2²⁴`) — the guard rejects
    a mean that exists;
  * exact total `0`, binary32 total exactly `−2` (weights `2²⁴`, `1`, `1`, `−(2²⁴+2)`) — the guard
    *passes* and the division returns a finite, plausible number for a mean that does not exist.
    This is the direction with no error signal, and it is the reason the distinction is worth
    carrying in a signature.

The exact arithmetic is checked in `Float`, where every weight and every partial sum is exactly
representable in binary64, so the binary64 computation *is* the real computation rather than an
approximation of it.

**And then the two ways to put the licenses back together.** Nonnegative weights make them
equivalent (`licenses_agree_of_nonneg`), which is checked here by driving the capstone through a
depth-2 carving of indicator weights with *both* conditions discharged by arithmetic — the join
the earlier single-part witness could not reach without a rounding fact. Not rounding the
denominator at all makes them the same statement (`Aggregation.licenses_agree_of_exact`), checked
in the core tier.
-/

module

public import PropertyKindCalculus.Uncertainty.Adequacy.MeanBound
meta import PropertyKindCalculus.Uncertainty.Adequacy.MeanBound

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.MeanBound

open PropertyKindCalculus
open PropertyKindCalculus.Uncertainty.Adequacy
open TorchLean.Floats
open TorchLean.Floats.IEEE754
open FloatLib.Floats (ExecFloat)
open FloatLib.Floats.ExecFloat.Binary (isFinite toModel)

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
def bigE : IEEE32Exec := ExecFloat.Binary.ofBits32 0x4B800000

/-- `1` at executable binary32. -/
def oneE : IEEE32Exec := ExecFloat.Binary.ofBits32 0x3F800000

/-- `−2²⁴` at executable binary32. -/
def negBigE : IEEE32Exec := ExecFloat.Binary.ofBits32 0xCB800000

-- The three bit patterns are the values claimed: mantissa × 2^exp reads 2²⁴, 1, −2²⁴.
#guard (toModel bigE).toDyadic?.map (fun d => (d.negative, d.significand, d.exponent)) == some (false, 8388608, 1)
#guard (toModel oneE).toDyadic?.map (fun d => (d.negative, d.significand, d.exponent)) == some (false, 8388608, -23)
#guard (toModel negBigE).toDyadic?.map (fun d => (d.negative, d.significand, d.exponent)) == some (true, 8388608, 1)

-- Absorption: the first addition returns its larger operand unchanged.
#guard ExecFloat.Binary.toBits32 (ExecFloat.add bigE oneE) == ExecFloat.Binary.toBits32 bigE

-- so the executable total is exactly +0 — the license `WeightedCarving FP32` carries fails.
#guard ExecFloat.Binary.toBits32 (ExecFloat.add (ExecFloat.add bigE oneE) negBigE) == 0

-- while the exact total is 1 — the license the specification carving carries holds. Every value
-- and every partial sum here is exactly representable in binary64, so this Float computation is
-- the real one.
#guard ((16777216.0 : Float) + 1.0) == 16777217.0
#guard (((16777216.0 : Float) + 1.0) - 16777216.0) == 1.0

/-- `−(2²⁴+2)` at executable binary32 — representable, since the spacing at `2²⁴` is `2`. -/
def negBigPlus2E : IEEE32Exec := ExecFloat.Binary.ofBits32 0xCB800001

-- It is the value claimed: mantissa 8388609 × 2¹ = 16777218 = 2²⁴+2, negated.
#guard (toModel negBigPlus2E).toDyadic?.map (fun d => (d.negative, d.significand, d.exponent))
        == some (true, 8388609, 1)

-- The other direction. Fold `2²⁴, 1, 1, −(2²⁴+2)` left-associated: each `1` is absorbed, so the
-- running total is still `2²⁴` when the last weight arrives, and the result is `−2` — bits
-- 0xC0000000. The exact total is 0, so here the specification's license FAILS and the
-- executable one HOLDS: the run-time guard passes and the mean does not exist.
#guard ExecFloat.Binary.toBits32 (ExecFloat.add (ExecFloat.add bigE oneE) oneE) == ExecFloat.Binary.toBits32 bigE
#guard ExecFloat.Binary.toBits32 (ExecFloat.add (ExecFloat.add (ExecFloat.add bigE oneE) oneE) negBigPlus2E)
        == 0xC0000000
#guard (((16777216.0 : Float) + 1.0 + 1.0) - 16777218.0) == 0.0

/-! ## Nonnegative weights — the capstone with both licenses discharged, at depth 2 -/

/-- An indicator weight: `1` at every part. Nonnegative and on the grid, which is what the
positivity route asks for — and the shape a validity-masked mean has. -/
noncomputable def wOne : Bool → FP32 := fun _ => ⟨(1 : ℝ)⟩

theorem wOne_nonneg : ∀ p, 0 ≤ (wOne p).val := by
  intro p; show (0:ℝ) ≤ 1; norm_num

theorem wOne_grid : ∀ p, (wOne p).IsRepresentable := fun _ => one_representable

/-- The exact total over the two-part carving is `2`. -/
theorem wOne_pos : 0 < totalWeight (fun p => (wOne p).val) pairParts := by
  show (0:ℝ) < (1:ℝ) + (1:ℝ)
  norm_num

-- Inhabitation at a JOIN: the capstone applied to a depth-2 carving whose *both* licenses are
-- discharged by arithmetic. Positivity is what makes this reachable — the rounded total at a
-- union is a `fp32Round` of a sum, and without nonnegativity there is no way to know it is
-- nonzero without a rounding fact about the specific values.
theorem r9_mean_fp32_bound_depth2_nonneg (ρ : ℕ → FP32) :
    |((carvingOfNonneg wOne pairParts wOne_nonneg wOne_grid wOne_pos).mean v2).val
        - (specCarving (carvingOfNonneg wOne pairParts wOne_nonneg wOne_grid wOne_pos)
              wOne_pos.ne').mean (fun p => (v2 p).val)|
      ≤ errBound (meanExpr wOne v2 pairParts) ρ :=
  mean_fp32_within_errBound_of_nonneg wOne v2 pairParts ρ wOne_nonneg wOne_grid wOne_pos

/-! ## The same mean with its kinds on — `Quantity.div_refines` at a model-level site

`WeightedCarvingQ.mean_div_refines` reads the R10 quotient bridge at the mean's own `div` node.
Instantiated here on the indicator-weighted carving above, at the binary32 spec rung: the weights
are lengths, the values are lengths, the numerator is an area, and dividing that by a length lands
back on length — which is the `QuotientKind` the mean asks for. This is the first place a
model-level construct rides `div_refines` rather than a hand-built quotient. -/

/-- Length, ratio-scale. -/
def lengthK : KindOfProperty := { id := "length", scale := .ratio }

/-- Area — the kind the numerator lands in. -/
def areaK : KindOfProperty := { id := "area", scale := .ratio }

theorem prodLen : ProductKind lengthK lengthK areaK := .ofRatio _ _ _
theorem quotArea : QuotientKind areaK lengthK lengthK := .ofRatio _ _ _
theorem diffLen : DifferenceKind lengthK := DifferenceKind.ofScale
theorem diffArea : DifferenceKind areaK := DifferenceKind.ofScale

/-- The indicator weights, with the kind on. -/
noncomputable def qwOne : Bool → Quantity lengthK FP32 := fun p => ⟨wOne p⟩

/-- The values, with the kind on. -/
noncomputable def qv2 : Bool → Quantity lengthK FP32 := fun p => ⟨v2 p⟩

/-- The kinded total is the carrier total — the erasure theorem, at this witness. -/
theorem qwOne_total :
    (totalWeightQ diffLen qwOne pairParts).magnitude = totalWeight wOne pairParts :=
  totalWeightQ_magnitude diffLen qwOne pairParts

/-- **The kinded carving exists**, with its license discharged rather than assumed: the exact total
is `2`, positivity carries that to the rounded total, and the erasure theorem transports it to the
kinded field. -/
noncomputable def qCarving : WeightedCarvingQ FP32 lengthK Bool where
  parts := pairParts
  weight := qwOne
  differenceKind := diffLen
  total_ne_zero := by
    rw [qwOne_total]
    exact fp32_ne_zero_of_val
      (totalWeight_fp32_pos wOne wOne_nonneg wOne_grid pairParts wOne_pos).ne'

/-- **R10 at the mean's division.** Forgetting the binary32 mean to `ℝ` is the rounding of the real
quotient of the forgotten numerator and denominator. -/
theorem r10_mean_div_refines :
    (Quantity.toSpec (qCarving.mean prodLen quotArea diffArea qv2) : Quantity lengthK ℝ)
      = Quantity.roundBy (CarrierRefinement.round (E := FP32))
          (Quantity.div quotArea
            (Quantity.toSpec (weightedSumQ prodLen diffArea qCarving.weight qv2 qCarving.parts))
            (Quantity.toSpec qCarving.total)) :=
  qCarving.mean_div_refines prodLen quotArea diffArea qv2

/-- And the kinded mean erases to the carrier mean of the same data, so the binary32 bound above
applies to it unchanged. -/
theorem r10_kinded_mean_erases :
    (qCarving.mean prodLen quotArea diffArea qv2).magnitude
      = qCarving.toCarving.mean (fun p => (qv2 p).magnitude) :=
  qCarving.mean_magnitude prodLen quotArea diffArea qv2

-- and the equivalence itself, at that carving: the executable license is now a consequence.
theorem r9_licenses_agree_nonneg :
    (totalWeight wOne pairParts).val ≠ 0
      ↔ totalWeight (fun p => (wOne p).val) pairParts ≠ 0 :=
  licenses_agree_of_nonneg wOne wOne_nonneg wOne_grid pairParts

-- Boundary — nonnegativity is load-bearing, not decoration: the two witnesses above are exactly
-- carvings it excludes, and each has a negative weight.

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.mean_fp32_within_errBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mean_fp32_within_errBound

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.regular_meanExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms regular_meanExpr

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.evalFP32_meanExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalFP32_meanExpr

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.fp32_val_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fp32_val_ne_zero

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.licenses_agree_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms licenses_agree_of_nonneg

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.mean_fp32_within_errBound_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mean_fp32_within_errBound_of_nonneg

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.fp32Round_add_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fp32Round_add_ge

end PropertyKindCalculus.Tests.MeanBound

end Blanket
