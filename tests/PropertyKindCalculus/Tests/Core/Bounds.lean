/-
# Validation probes — direction-locked bounds and kind-indexed intervals

Inhabitation, boundary, and axiom-profile probes for `LowerBound`/`UpperBound`/`IccQ`
(`PropertyKindCalculus.Bounds`). The probes check the properties the module exists for:

  * role-typed endpoints cannot be swapped (an `⟨hi, lo⟩` construction is a type
    error), and the scale gate genuinely excludes a nominal kind;
  * the directional Prop formers state only their own orientation, and membership /
    orderedness are inhabited at concrete witnesses over `Int`;
  * `IccQ.clamp` computes with the deployed association `min (max x lo) hi` — pinned
    against the *other* association's tell-tale case so a silent switch to
    `Quantity.clamp`'s `max lo (min hi x)` would fail here.
-/

import PropertyKindCalculus

namespace PropertyKindCalculus.Tests.Bounds

open PropertyKindCalculus

/-- Length, a ratio kind (scale allows order). -/
def lengthK : KindOfProperty := { id := "length", scale := .ratio }
/-- Colour, a nominal kind (no order, so no bounds). -/
def colourK : KindOfProperty := { id := "colour", scale := .nominal }

/-- The box `[0, 10]` of lengths over the lawful carrier `Int`. -/
def box : IccQ lengthK Int := IccQ.of ⟨0⟩ ⟨10⟩

-- Inhabitation: the clamp eliminator computes — below, inside, and above the box.
example : (box.clamp ⟨-3⟩).magnitude = 0 := rfl
example : (box.clamp ⟨5⟩).magnitude = 5 := rfl
example : (box.clamp ⟨12⟩).magnitude = 10 := rfl

-- Association pin (load-bearing for bit-exact erasure): on the degenerate box
-- `lo > hi`, `min (max x lo) hi` pins to `hi` where `Quantity.clamp`'s
-- `max lo (min hi x)` would pin to `lo` — so a silent switch of association cannot
-- land. (Degenerate on purpose: the two associations agree on every proper box.)
example : ((IccQ.of (⟨10⟩ : Quantity lengthK Int) ⟨0⟩).clamp ⟨5⟩).magnitude = 0 := rfl
example : (Quantity.clamp (⟨10⟩ : Quantity lengthK Int) ⟨0⟩ ⟨5⟩).magnitude = 10 := rfl

-- Membership and orderedness are inhabited at concrete witnesses, through the
-- directional formers only (`show` reduces each former to its concrete `Int` fact).
example : box.Mem ⟨5⟩ := ⟨show (0 : Int) ≤ 5 by decide, show (5 : Int) ≤ 10 by decide⟩
example : box.Ordered := show (0 : Int) ≤ 10 by decide
example : (IccQ.ofLE (⟨0⟩ : Quantity lengthK Int) ⟨10⟩ (by decide)).Ordered :=
  IccQ.ofLE_ordered (by decide) OrderKind.ofScale

-- Boundary (Rule 2): role-typed endpoints cannot swap — an `IccQ` built with the upper
-- bound in the lower slot is a *type* error, which is the `Icc hi lo` hazard the module
-- exists to exclude.
def lb : LowerBound lengthK Int := ⟨⟨0⟩⟩
def ub : UpperBound lengthK Int := ⟨⟨10⟩⟩
example : IccQ lengthK Int := ⟨lb, ub⟩
#check_failure (⟨ub, lb⟩ : IccQ lengthK Int)

-- Boundary: the scale gate genuinely fires — a nominal kind has no order, so
-- `OrderKind colourK` is uninhabited and the smart constructor's autoParam cannot
-- discharge it: an interval of colours cannot be formed.
theorem colour_no_order : ¬ OrderKind colourK := fun h => h.allowsOrder
#check_failure (IccQ.of (⟨1⟩ : Quantity colourK Int) ⟨2⟩)

/-- info: 'PropertyKindCalculus.IccQ.ofLE_ordered' depends on axioms: [propext] -/
#guard_msgs in #print axioms IccQ.ofLE_ordered

/-- info: 'PropertyKindCalculus.IccQ.clamp_magnitude' does not depend on any axioms -/
#guard_msgs in #print axioms IccQ.clamp_magnitude

/-! ## Executable order deciders (host carriers with decidable order)

Inhabitation over `Int`: each decider computes, in its own direction only. -/

-- Same-kind comparisons compute …
#guard (⟨3⟩ : Quantity lengthK Int).leb ⟨5⟩ == true
#guard (⟨5⟩ : Quantity lengthK Int).ltb ⟨5⟩ == false
#guard (⟨5⟩ : Quantity lengthK Int).geb ⟨5⟩ == true
#guard (⟨5⟩ : Quantity lengthK Int).gtb ⟨3⟩ == true

-- … and are kind-gated: a cross-kind comparison is a type error, exactly as for `+`.
def massK : KindOfProperty := { id := "mass", scale := .ratio }
#check_failure (fun (x : Quantity lengthK Int) (y : Quantity massK Int) => x.leb y)

-- Bound hits are directional: the upper bound is hit at and beyond it, from below …
#guard ub.hitBy (⟨10⟩ : Quantity lengthK Int) == true
#guard ub.hitBy (⟨12⟩ : Quantity lengthK Int) == true
#guard ub.hitBy (⟨9⟩ : Quantity lengthK Int) == false
-- … the lower bound at and below it, from above.
#guard lb.hitBy (⟨0⟩ : Quantity lengthK Int) == true
#guard lb.hitBy (⟨-2⟩ : Quantity lengthK Int) == true
#guard lb.hitBy (⟨1⟩ : Quantity lengthK Int) == false

-- Directionality is API-shape, executably too: a `LowerBound` has no `≥`-style query
-- of its own — `hitBy` is its only Bool former, and it asks the one meaningful
-- question (saturation from above); there is no way to ask an upper-bound question
-- of a lower bound.
#check_failure (fun (x : Quantity lengthK Int) => lb.exceededBy x)

end PropertyKindCalculus.Tests.Bounds
