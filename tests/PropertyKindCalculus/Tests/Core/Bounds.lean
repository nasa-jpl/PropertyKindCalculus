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

module

public import PropertyKindCalculus
meta import PropertyKindCalculus
-- Private scope only: the checks below reduce through bodies sealed in the core
-- library; `import all` gives this file the reduction without exposing them.
import all PropertyKindCalculus.Bounds

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

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

-- Conformity is the OTHER non-strict question, and it is not `hitBy`: `leb`/`geb` ask
-- whether a value is admissible, `hitBy` whether it has reached the constraint. The two
-- coincide exactly at the endpoint and are opposites everywhere else, which is why both
-- exist and why neither is spelled as a bare `≤` on magnitudes.
#guard lb.leb (⟨0⟩ : Quantity lengthK Int) == true    -- at the bound: admissible …
#guard lb.hitBy (⟨0⟩ : Quantity lengthK Int) == true  -- … and saturated
#guard lb.leb (⟨5⟩ : Quantity lengthK Int) == true
#guard lb.hitBy (⟨5⟩ : Quantity lengthK Int) == false
#guard lb.leb (⟨-1⟩ : Quantity lengthK Int) == false
#guard ub.geb (⟨10⟩ : Quantity lengthK Int) == true
#guard ub.geb (⟨11⟩ : Quantity lengthK Int) == false

-- Executable membership is built from the two directional deciders, so a consumer testing
-- a value against a range never writes the comparison and cannot write it backwards.
#guard box.memb (⟨0⟩ : Quantity lengthK Int) == true
#guard box.memb (⟨10⟩ : Quantity lengthK Int) == true
#guard box.memb (⟨-1⟩ : Quantity lengthK Int) == false
#guard box.memb (⟨11⟩ : Quantity lengthK Int) == false

-- Directionality is API-shape, executably too: a `LowerBound` has no `≥`-style query
-- of its own — `leb` and `hitBy` are its only Bool formers, and both keep it on its own
-- side of the comparison; there is no way to ask an upper-bound question of a lower bound.
#check_failure (fun (_x : Quantity lengthK Int) => lb.exceededBy _x)
#check_failure (fun (_x : Quantity lengthK Int) => lb.geb _x)

/-! ## The representation cast

A carrier lift moves the numbers and leaves the roles alone. The probes below are what
that commits the module to: an interval lifted whole is the two endpoints lifted through
their own roles, so a lift cannot exchange them, and the cast takes no `OrderKind` — the
scale gate was discharged where the interval was formed and a representation change
cannot revoke it.

What the cast is *for* is visible only at the call site: a configuration box lifted
field-wise without it has to erase and re-mint every endpoint, and each of those is an
anonymous constructor the boundary audit reads as a mint. -/

-- The lift is definitional at each endpoint, so downstream analysis runs on the carrier
-- arithmetic without a rewriting step of its own.
example : (box.castCarrier Float.ofInt).lo.q.magnitude = Float.ofInt box.lo.q.magnitude := rfl
example : (box.castCarrier Float.ofInt).hi.q.magnitude = Float.ofInt box.hi.q.magnitude := rfl

#guard (box.castCarrier Float.ofInt).lo.q.magnitude == 0.0
#guard (box.castCarrier Float.ofInt).hi.q.magnitude == 10.0

-- The endpoints keep their roles across the cast, so the lifted box is still queried
-- through the directional formers and still clamps with the deployed association.
#guard (box.castCarrier Float.ofInt).memb (⟨5.0⟩ : Quantity lengthK Float) == true
#guard (box.castCarrier Float.ofInt).memb (⟨11.0⟩ : Quantity lengthK Float) == false
#guard ((box.castCarrier Float.ofInt).clamp ⟨12.0⟩).magnitude == 10.0

-- Each role casts on its own, and the result is still that role: a lifted lower bound
-- cannot be handed to an upper slot, so a field-wise lift of a box is swap-proof for the
-- same reason its construction is.
example : LowerBound lengthK Float := lb.castCarrier Float.ofInt
example : UpperBound lengthK Float := ub.castCarrier Float.ofInt
#check_failure (⟨lb.castCarrier Float.ofInt, lb.castCarrier Float.ofInt⟩ : IccQ lengthK Float)

-- The cast is kind-preserving by parametricity — there is no way to change `k` with it,
-- exactly as for `Quantity.castCarrier`.
example : IccQ lengthK Float := box.castCarrier Float.ofInt
#check_failure (box.castCarrier Float.ofInt : IccQ colourK Float)

end PropertyKindCalculus.Tests.Bounds

end -- pkc-blanket-expose
end -- pkc-blanket
