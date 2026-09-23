/-
# Worked example — Stage 3 numerical adequacy: a flagged vs. a clean evaluation

The payoff of the `Adequacy` carrier (`UNCERTAINTY.md` §4.3): a model written *once* over
`[NumCarrier α]` is analyzed for floating-point information loss *for free* by instantiating it at
the analysis carrier — no rewrite. Two write-once kernels, each run in a deliberately-inadequate and
an adequate configuration:

  * **Swamping.** `accModel bias x = bias + x`. When the accumulator's ulp exceeds twice the input
    uncertainty, that uncertainty falls below half a ulp of the sum and is *numerically invisible* —
    the carrier flags it (theorem A3, `Adequacy.Soundness.verdict_sound`). The *same* kernel with a
    small accumulator certifies clean.
  * **Catastrophic cancellation.** `diffModel a b = a − b`. Near-equal operands give an exact result
    (Sterbenz, A2) whose *relative* uncertainty reaches 100% — the carrier flags it
    (`Adequacy.Sterbenz32.relUnc_amplifies`). A well-separated subtraction certifies clean.

Everything here is a **checked fact** (the module builds under CI). Mathlib- and TorchLean-free.
-/

module

public import PropertyKindCalculus.Uncertainty
meta import PropertyKindCalculus.Uncertainty

@[expose] public section Blanket

namespace PropertyKindCalculus.UncertaintyExamples.AdequacySwamping

open PropertyKindCalculus PropertyKindCalculus.Paradigm PropertyKindCalculus.Uncertainty

/-! ## The write-once kernels (over any `[NumCarrier α]`) -/

/-- Add a small measured quantity to a large bias — a WO1 kernel (runs at `ℝ`, `Float`, `Adequacy`,
… unchanged). -/
def accModel {α : Type} [NumCarrier α] (bias x : α) : α := bias + x

/-- Subtract two near-equal measured quantities — a WO1 kernel. -/
def diffModel {α : Type} [NumCarrier α] (a b : α) : α := a - b

/-! ## The binary32 ulp is what the check turns on -/

-- ulp32(10⁸) = 2^(26−23) = 8, so an uncertainty below 4 sits under half a ulp; ulp32(100) ≈ 7.6·10⁻⁶.
#eval s!"ulp32(1e8) = {Adequacy.ulp32 1e8}   ulp32(100) = {Adequacy.ulp32 100.0}"
#guard Float.abs (Adequacy.ulp32 1e8 - 8.0) < 1e-9
#guard Adequacy.ulp32 100.0 < 1e-4

/-! ## Swamping — the same `accModel`, flagged then clean

An input `x = 1 ± 1` added to a large bias `10⁸`: the uncertainty `1` is below `½ ulp32(10⁸) = 4`, so
it is swamped — the carrier records an absorption. Added to a small bias `100`, the same uncertainty
`1` far exceeds `½ ulp32(100)`, so it survives — no violation. -/

/-- Inadequate: large accumulator swamps the input uncertainty. -/
def swamped : Adequacy := accModel (Adequacy.exact 1e8) (Adequacy.input 1.0 1.0)
/-- Adequate: small accumulator, the same input uncertainty survives. -/
def clean : Adequacy := accModel (Adequacy.exact 100.0) (Adequacy.input 1.0 1.0)

#eval s!"swamped: adequate? {Adequacy.isAdequate swamped}   absorptions = {swamped.report.absorptions}"
#eval s!"clean:   adequate? {Adequacy.isAdequate clean}   absorptions = {clean.report.absorptions}"

-- The deliberately-inadequate evaluation is flagged (one swamping site); the adequate one is clean.
#guard swamped.report.absorptions == 1
#guard Adequacy.isAdequate swamped == false
#guard clean.report.absorptions == 0
#guard Adequacy.isAdequate clean == true
-- The value is genuinely corrupted: 10⁸ ⊕ (1 ± 1) carries a ±1 uncertainty the FP result cannot hold.
#guard Float.abs (swamped.value - 1e8) < 2.0

/-! ## Catastrophic cancellation — the same `diffModel`, flagged then clean

`a − b` with `a ≈ b` (difference ~10⁻⁷) but each carrying uncertainty `10⁻³`: the result's relative
uncertainty is ~10⁴ (≥ 100%), so the carrier flags cancellation. A well-separated difference
(`3 − 1 = 2`) with the same uncertainties certifies clean. -/

/-- Inadequate: near-equal subtraction, relative uncertainty ≥ 100%. -/
def cancelled : Adequacy := diffModel (Adequacy.input 1.0000001 0.001) (Adequacy.input 1.0 0.001)
/-- Adequate: well-separated subtraction. -/
def separated : Adequacy := diffModel (Adequacy.input 3.0 0.001) (Adequacy.input 1.0 0.001)

#eval s!"cancelled: adequate? {Adequacy.isAdequate cancelled}   cancellations = {cancelled.report.cancellations}"
#eval s!"separated: adequate? {Adequacy.isAdequate separated}   cancellations = {separated.report.cancellations}"

#guard cancelled.report.cancellations == 1
#guard Adequacy.isAdequate cancelled == false
#guard separated.report.cancellations == 0
#guard Adequacy.isAdequate separated == true

end PropertyKindCalculus.UncertaintyExamples.AdequacySwamping

end Blanket
