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

## The whole arithmetic surface, not just `+`

`CarrierRefinement` carries the additive law alone, which is enough for the
extensive mode (§13.5.1) and for nothing else. A weighted mean, a ratio, a
conversion factor, a sensitivity coefficient — every one of them is a `+`/`*`/`/`
expression, and none of them can cross the bridge on an additive contract. So the
multiplicative surface is stated here too, as `MulRefinement` and `DivRefinement`.

Both are `Prop` classes *parametrized by* a `CarrierRefinement`, not extensions of
it. That is deliberate: a single expression uses all three operations at once, so
`extends` would put two independent paths to `toSpec` and `round` in scope
simultaneously, and instance resolution would be free to pick either. Taking the
refinement as a parameter means one carrier has one forgetful map and one rounding,
and the two extra classes say only that the *same* pair also commutes with `*` and
with `/`.

The line the split follows is data versus proof. `CarrierRefinement` carries
*data* — `toSpec` and `round` are functions, and two of them are two different
functions — so it must reach a use site by exactly one path. `MulRefinement` and
`DivRefinement` carry only equations, and a class in `Prop` is a subsingleton: two
instances of one are the same instance, so they may be inherited, re-derived and
diamonded freely without a term ever depending on which arrived. Bundling the data
class into them would have traded a harmless duplication for a harmful one. What the
arrangement costs is binder length — a law about `/` names `[Carrier E] [Carrier S]
[Div E] [Div S] [ScalarCarrier E] [ScalarCarrier S] [CarrierRefinement E S]
[DivRefinement E S]` — and that is the price of the mixins staying mixins.

**Where the zero denominator goes.** The division law here is unconditional, and can
afford to be, because both sides share the specification carrier's total convention
for `x / 0`. That is an artifact of the *spec* rung, not a claim about machines: on a
real executable format a zero (or subnormal, or NaN) denominator is exactly where the
refinement stops holding. That hazard belongs one rung down, as an explicit
hypothesis on the executable carrier's own theorem — which is where
`Torch.Fp32` states it, and why `IEEE32Exec` is given no `CarrierRefinement`
instance at all.
-/

module

public import PropertyKindCalculus.QuantityClassification

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

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

/-! ## The multiplicative surface of the bridge -/

/-- **The bridge law for multiplication.** The same forgetful map and rounding that
`CarrierRefinement` supplies for `+` also relate the exec product to the spec product:
$$ \mathrm{toSpec}(x \cdot_E y) = \mathrm{round}\,(\mathrm{toSpec}\,x \cdot_S \mathrm{toSpec}\,y). $$
Held apart from `CarrierRefinement` rather than bundled into it, because `Carrier`
supplies only zero and addition — a carrier can refine additively without having a `*`
at all (and `Quantity.mul` likewise asks for `[Mul R] [ScalarCarrier R]` separately). -/
class MulRefinement (E S : Type) [Carrier E] [Carrier S] [Mul E] [Mul S]
    [CarrierRefinement E S] : Prop where
  /-- Forgetting an exec product equals rounding the spec product of the forgotten factors. -/
  toSpec_mul : ∀ x y : E,
    CarrierRefinement.toSpec (S := S) (x * y)
      = CarrierRefinement.round (E := E)
          (CarrierRefinement.toSpec (S := S) x * CarrierRefinement.toSpec (S := S) y)

/-- **The bridge law for division.** As for multiplication, with the caveat the module
docstring records: this is unconditional only because the exec and spec carriers agree on
what `x / 0` means, which a *specification* format can arrange and a machine format cannot.
An executable carrier whose division produces an infinity or a NaN has no instance of this
class; its refinement is a theorem with the denominator's nonzeroness as a hypothesis. -/
class DivRefinement (E S : Type) [Carrier E] [Carrier S] [Div E] [Div S]
    [CarrierRefinement E S] : Prop where
  /-- Forgetting an exec quotient equals rounding the spec quotient of the forgotten operands. -/
  toSpec_div : ∀ x y : E,
    CarrierRefinement.toSpec (S := S) (x / y)
      = CarrierRefinement.round (E := E)
          (CarrierRefinement.toSpec (S := S) x / CarrierRefinement.toSpec (S := S) y)

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

/-- **Exec refines spec across a kind product (R10).** The kind-crossing companion of
`add_refines`: for a licensed product `ProductKind k₁ k₂ k`, the executable product viewed
in the spec carrier is the rounding of the spec product.

`add_refines` preserves one kind throughout; this one does not, and that is the point. The
kinds move — `k₁`, `k₂` to `k` — but they move *under the product law*, the same law on
both sides of the bridge, so the refinement and the kind license are independent
obligations that compose. A rounding step cannot launder a product the kind calculus
refuses, and a licensed product does not lose its license by being computed in floats. -/
theorem mul_refines [Carrier E] [Carrier S] [Mul E] [Mul S] [ScalarCarrier E] [ScalarCarrier S]
    [CarrierRefinement E S] [MulRefinement E S] {k₁ k₂ k : KindOfProperty}
    (h : ProductKind k₁ k₂ k) (x : Quantity k₁ E) (y : Quantity k₂ E) :
    (Quantity.toSpec (Quantity.mul h x y) : Quantity k S)
      = Quantity.roundBy (CarrierRefinement.round (E := E))
          (Quantity.mul h (Quantity.toSpec x) (Quantity.toSpec y)) := by
  unfold Quantity.toSpec Quantity.roundBy Quantity.mul
  rw [MulRefinement.toSpec_mul]

/-- **Exec refines spec across a kind quotient (R10).** `mul_refines` for `QuotientKind` —
the rung a ratio, a conversion factor, or the denominator of a weighted mean rides. -/
theorem div_refines [Carrier E] [Carrier S] [Div E] [Div S] [ScalarCarrier E] [ScalarCarrier S]
    [CarrierRefinement E S] [DivRefinement E S] {k₁ k₂ k : KindOfProperty}
    (h : QuotientKind k₁ k₂ k) (x : Quantity k₁ E) (y : Quantity k₂ E) :
    (Quantity.toSpec (Quantity.div h x y) : Quantity k S)
      = Quantity.roundBy (CarrierRefinement.round (E := E))
          (Quantity.div h (Quantity.toSpec x) (Quantity.toSpec y)) := by
  unfold Quantity.toSpec Quantity.roundBy Quantity.div
  rw [DivRefinement.toSpec_div]

end Quantity

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
