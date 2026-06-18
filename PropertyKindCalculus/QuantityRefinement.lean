/-
# QuantityRefinement — the exec/spec refinement bridge (R10 capstone)

A `LawfulCarrier` (`ℝ`, `Int`) carries the additivity laws; an executable float
carrier (`Float`, and TorchLean's IEEE-754 binary32) carries *execution* but
**not** those laws — floating-point addition is not associative. The two are
reconciled by a *refinement*: the executable result, forgotten back to the
specification numbers, is the *rounding* of the specification computation.

This module specifies that reconciliation once, parametrically, exactly as the
rest of R10 is parametric. A `CarrierRefinement E S` packages

  * a forgetful map `toSpec : E → S` (the analogue of TorchLean's `toReal`,
    sending an *exec* magnitude to its *spec* magnitude), and
  * a spec-side `round : S → S` (snap to the representable grid),

with the single law that *forgetting an exec addition equals rounding the spec
addition*:
$$ \mathrm{toSpec}(x +_E y) = \mathrm{round}\,(\mathrm{toSpec}\,x +_S \mathrm{toSpec}\,y). $$

Lifting that law along the kind index gives the headline capstone
`Quantity.add_refines`: for a kind-`k` quantity, the exec sum *viewed in the spec
carrier* is the rounded spec sum. So a law proved over the lawful spec carrier
descends to the executable run with exactly one rounding step — the bridge that
carries the {representation-parametric laws} from the lawful `ℝ` onto the
executable float that is not lawful, one kind-indexed value serving both proof
and execution.

The class is the abstract pattern; TorchLean's `FP32` (rounding spec) and
`IEEE32Exec` (executable, with NaN) are its motivating *instance* (a separate,
PhysLib/TorchLean-backed library). In plain engineering terms `CarrierRefinement`
is the *rounding contract* between a slow exact number type and the fast machine
number type that stands in for it; proving the contract once means every kind,
unit, and aggregation written above the carrier inherits it.
-/

import PropertyKindCalculus.Quantity

namespace PropertyKindCalculus

/-- **A carrier refinement (R10).** A specification of how an *exec* carrier `E`
(fast, lossy — e.g. an IEEE-754 float) stands in for a *spec* carrier `S` (exact —
e.g. `ℝ`): a forgetful map `toSpec : E → S` and a spec-side `round : S → S`, such
that forgetting an exec addition equals rounding the spec addition. This is the
abstract form of TorchLean's `BridgeFP32` pattern ("compute in `ℝ`, then round").
`toSpec` plays the role of TorchLean's `toReal`. -/
class CarrierRefinement (E S : Type) [Carrier E] [Carrier S] where
  /-- Forget an exec magnitude to its spec magnitude (TorchLean's `toReal`). -/
  toSpec : E → S
  /-- Snap a spec magnitude to the representable grid (rounding). -/
  round : S → S
  /-- The exec zero forgets to the spec zero (zero is represented exactly). -/
  toSpec_zero : toSpec Carrier.zero = Carrier.zero
  /-- **The bridge law.** Forgetting an exec addition equals rounding the spec
  addition of the forgotten summands. -/
  toSpec_add : ∀ x y : E,
    toSpec (Carrier.add x y) = round (Carrier.add (toSpec x) (toSpec y))

namespace Quantity

variable {k : KindOfProperty} {E S : Type}

/-- Forget an exec-carried quantity to its spec carrier, kindwise — the kind index
rides along unchanged (the analogue of TorchLean's `toReal`, lifted to a kind-`k`
magnitude). -/
def toSpec [Carrier E] [Carrier S] [CarrierRefinement E S]
    (x : Quantity k E) : Quantity k S :=
  ⟨CarrierRefinement.toSpec x.magnitude⟩

/-- Lift a magnitude-level rounding to a kind-`k` quantity. -/
def roundBy [Carrier S] (r : S → S) (x : Quantity k S) : Quantity k S :=
  ⟨r x.magnitude⟩

/-- The zero quantity refines exactly: no rounding is needed at zero. -/
theorem zero_refines [Carrier E] [Carrier S] [CarrierRefinement E S] :
    Quantity.toSpec (Quantity.zero : Quantity k E) = (Quantity.zero : Quantity k S) := by
  unfold Quantity.toSpec Quantity.zero
  rw [CarrierRefinement.toSpec_zero]

/-- **Exec refines spec across representations (R10 capstone).** For a kind-`k`
quantity, the executable sum *viewed in the spec carrier* equals the rounding of
the spec sum:
$$ \mathrm{toSpec}(x +_E y) = \mathrm{round}\,(\mathrm{toSpec}\,x +_S \mathrm{toSpec}\,y). $$
This is `CarrierRefinement.toSpec_add` lifted along the kind index, so a law proved
over the lawful spec carrier transfers to the executable run with one rounding
step. The kind `k` is preserved throughout — the bridge never crosses kinds. -/
theorem add_refines [Carrier E] [Carrier S] [CarrierRefinement E S]
    (h : DifferenceKind k) (x y : Quantity k E) :
    (Quantity.toSpec (Quantity.add h x y) : Quantity k S)
      = Quantity.roundBy (CarrierRefinement.round (E := E))
          (Quantity.add h (Quantity.toSpec x) (Quantity.toSpec y)) := by
  unfold Quantity.toSpec Quantity.roundBy Quantity.add
  rw [CarrierRefinement.toSpec_add]

end Quantity

end PropertyKindCalculus
