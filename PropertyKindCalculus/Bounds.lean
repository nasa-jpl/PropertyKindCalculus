/-
# Bounds — direction-locked endpoints and kind-indexed intervals

A configuration box like `(smMin, smMax)` carried as two naked magnitudes has two
failure modes the type system never sees: the *kind* conflation (clamping a
reflectivity against a water-content bound) and the *direction* swap (constructing the
interval with the endpoints reversed, so every clamp silently pins to the wrong end).
`Quantity k R` already fixes the first. This module fixes the second, by putting the
**role** of an endpoint — lower or upper — into its type:

  * `LowerBound k R` / `UpperBound k R` — one-field role wrappers over `Quantity k R`.
    Their Prop formers are **directional-only**: `LowerBound.le b x` ("the bound is at
    or below `x`") and `UpperBound.ge b x` ("the bound is at or above `x`") exist;
    there is deliberately *no* former placing `x` on the other side of a lower bound.
    A fact that would read "`x ≤ the lower bound`" cannot be stated through the bound's
    own API, so a max/min swap is unwritable, not merely unlikely.
  * `IccQ k R` — the closed interval as a *pair of roles* `{lo : LowerBound, hi :
    UpperBound}` (the kind-indexed counterpart of Mathlib's `Set.Icc`, carrier-generic
    and Mathlib-free). Given role-typed endpoints, constructing the interval swapped is
    a type error.

**Ordering stays out of `Quantity`.** There is — deliberately — no `LE`/`LT`/`Ord`
instance on `Quantity` itself: on a batched deployment carrier, "if it type-checks it
is one branch-free elementwise kernel" is a design law, and an ordering-to-`Bool`
operator would break it. Order facts about bounds are *Props*, stated at proof
carriers; the *executable* eliminator is `IccQ.clamp`, over the carrier's `Min`/`Max`.
For host-side per-scalar logic (quality flags, threshold audits), the executable
deciders at the end of this module (`Quantity.leb/ltb/geb/gtb`, `UpperBound.hitBy`,
`LowerBound.hitBy`) provide the same queries as `Bool`s, gated on the carrier having
*decidable* order — an instance batched carriers do not have, so the branchless law
survives by instance absence.

**Association of `clamp` (load-bearing).** `IccQ.clamp` computes
`min (max x lo) hi` — clamp-from-below first, then from above. This is the association
deployed batched kernels use, and it is *not* the same function as the function
calculus's `Quantity.clamp` (`max lo (min hi x)`): the two differ on NaN propagation
and on a degenerate `lo > hi` box, and they emit ops in different order on a tape
carrier. A kinded kernel authored with `IccQ.clamp` therefore erases *bit-exactly*,
op-for-op, to a naked `min (max x lo) hi` — which is what makes the kinded form
eligible to be the authored source of an already-deployed kernel.

**Roles survive representation change.** All three carry `castCarrier`, the counterpart
of `Quantity.castCarrier`: a floor is a floor and an interval is an interval at whichever
carrier the values they gate are held in, so lifting a host-side configuration box onto a
batched or tape carrier is a representation operation and nothing more. Stating it here is
what keeps a field-wise lift of a box of intervals from erasing and re-minting every
endpoint — each of which the boundary audit reads, correctly, as an anonymous mint.

The scale gate: an interval presupposes order, so forming one is licensed by the kind's
scale allowing `<`/`>` (ordinal or richer — Dybkær §12.16). `OrderKind k` records that
gate, uniform with `DifferenceKind` for `+`/`−` and `ProductKind` for `×`.
-/

import PropertyKindCalculus.Quantity

namespace PropertyKindCalculus

/-- **A kind-level order law.** A witness that `k`'s scale *allows order* — ordinal or
richer (Dybkær §12.16, `Scale.lean`'s `AllowsOrder`) — the precondition for bounds and
intervals of `k`-quantities. Uniform with `DifferenceKind` (the gate for `+`/`−`): the
metrology gate, recorded in the type. (A *nominal* kind has no order, hence no
meaningful bounds; this rules that out.) -/
structure OrderKind (k : KindOfProperty) : Prop where
  /-- `k`'s scale licenses `<`/`>` (ordinal, interval, or ratio). -/
  allowsOrder : k.scale.AllowsOrder

/-- **Smart constructor.** An order law for any kind whose scale concretely allows
order; the gate is discharged by `trivial` for a concrete non-nominal kind. -/
theorem OrderKind.ofScale {k : KindOfProperty} (h : k.scale.AllowsOrder := by trivial) :
    OrderKind k := ⟨h⟩

/-- **A lower endpoint, as a role.** A `k`-quantity whose *job* is to bound from below.
The role is in the type, so a `LowerBound` cannot be handed to an upper slot; the only
Prop former is the directional `LowerBound.le` — the bound on the *left* of `≤`. -/
structure LowerBound (k : KindOfProperty) (R : Type) where
  /-- The endpoint quantity. -/
  q : Quantity k R

/-- **An upper endpoint, as a role** — the dual of `LowerBound`. Its only Prop former is
the directional `UpperBound.ge` — the bound on the *right* of `≤`. -/
structure UpperBound (k : KindOfProperty) (R : Type) where
  /-- The endpoint quantity. -/
  q : Quantity k R

namespace LowerBound

/-- **The directional Prop former**: the lower bound is at or below `x`. This is the
*only* order relation statable through a `LowerBound` — there is deliberately no former
with `x` on the left — so the endpoint can never be used as if it bounded from above. -/
def le {k : KindOfProperty} {R : Type} [LE R] (b : LowerBound k R) (x : Quantity k R) :
    Prop :=
  b.q.magnitude ≤ x.magnitude

/-- **A role survives a representation cast** — the counterpart of `Quantity.castCarrier`
for this role. A floor is a floor at whichever carrier the value it gates is held in, so
lifting a host-side bound onto a batched or tape carrier changes the representation and
nothing else. Without it a lift has to open the role, erase the endpoint and re-mint it,
which is three anonymous constructors standing where one representation change belongs. -/
def castCarrier {k : KindOfProperty} {R S : Type} (f : R → S) (b : LowerBound k R) :
    LowerBound k S :=
  ⟨b.q.castCarrier f⟩

@[simp] theorem castCarrier_magnitude {k : KindOfProperty} {R S : Type} (f : R → S)
    (b : LowerBound k R) : (b.castCarrier f).q.magnitude = f b.q.magnitude := rfl

end LowerBound

namespace UpperBound

/-- **The directional Prop former**: the upper bound is at or above `x` — the only order
relation statable through an `UpperBound`. -/
def ge {k : KindOfProperty} {R : Type} [LE R] (b : UpperBound k R) (x : Quantity k R) :
    Prop :=
  x.magnitude ≤ b.q.magnitude

/-- **A role survives a representation cast** — `LowerBound.castCarrier`'s dual, and the
half that makes `IccQ.castCarrier` a lift of the interval rather than of two loose
endpoints. -/
def castCarrier {k : KindOfProperty} {R S : Type} (f : R → S) (b : UpperBound k R) :
    UpperBound k S :=
  ⟨b.q.castCarrier f⟩

@[simp] theorem castCarrier_magnitude {k : KindOfProperty} {R S : Type} (f : R → S)
    (b : UpperBound k R) : (b.castCarrier f).q.magnitude = f b.q.magnitude := rfl

end UpperBound

/-- **A kind-indexed closed interval** `[lo, hi]` — the carrier-generic, Mathlib-free
counterpart of `Set.Icc`, with the endpoints carried as *roles*. Given role-typed
endpoints, a swapped construction (`⟨hi, lo⟩`) is a type error, which is the `Icc hi lo`
hazard a naked pair of magnitudes cannot exclude. -/
structure IccQ (k : KindOfProperty) (R : Type) where
  /-- The lower endpoint (role-typed). -/
  lo : LowerBound k R
  /-- The upper endpoint (role-typed). -/
  hi : UpperBound k R

namespace IccQ

variable {k : KindOfProperty} {R : Type}

/-- **Smart constructor from raw endpoints**, scale-gated: forming an interval of `k` is
licensed by `k`'s scale allowing order (`OrderKind`, discharged by autoParam for a
concrete non-nominal kind). Use `IccQ.ofLE` where a carrier order is available to also
certify `lo ≤ hi` at construction. -/
def of (lo hi : Quantity k R) (_ord : OrderKind k := by exact OrderKind.ofScale) :
    IccQ k R :=
  ⟨⟨lo⟩, ⟨hi⟩⟩

/-- **The interval is genuinely ordered**: its lower endpoint is at or below its upper
endpoint — stated through the endpoints' own directional formers, so it is the *only*
orientation the API can even express. -/
def Ordered [LE R] (I : IccQ k R) : Prop := I.lo.le I.hi.q

/-- **Proof-carrying smart constructor**: certifies `lo ≤ hi` at construction, so a
swapped pair of literals is rejected by an unprovable side goal (at a proof carrier),
not discovered downstream. -/
def ofLE [LE R] (lo hi : Quantity k R) (_h : lo.magnitude ≤ hi.magnitude)
    (_ord : OrderKind k := by exact OrderKind.ofScale) : IccQ k R :=
  ⟨⟨lo⟩, ⟨hi⟩⟩

/-- An `ofLE`-built interval is `Ordered` — the construction proof is the fact. -/
theorem ofLE_ordered [LE R] {lo hi : Quantity k R} (h : lo.magnitude ≤ hi.magnitude)
    (ord : OrderKind k) : (IccQ.ofLE lo hi h ord).Ordered := h

/-- **The interval `centre ± halfWidth`** — the `[c − h, c + h]` form, as opposed to `of`'s
`[lo, hi]`. Both endpoints are derived from the same pair, so the two cannot disagree and the
orientation is fixed by construction for any non-negative half-width: this is the constructor to
reach for whenever the interval *is* a value with a symmetric allowance around it (a coverage
interval, an agreement interval, a mechanical tolerance written as `±`), where spelling out two
endpoints is an opportunity to get one of them wrong.

Both arguments are `k`-quantities: an allowance on a quantity is a quantity of that same kind. -/
def about [Add R] [Sub R] (centre halfWidth : Quantity k R)
    (_ord : OrderKind k := by exact OrderKind.ofScale) : IccQ k R :=
  ⟨⟨⟨centre.magnitude - halfWidth.magnitude⟩⟩, ⟨⟨centre.magnitude + halfWidth.magnitude⟩⟩⟩

@[simp] theorem about_lo [Add R] [Sub R] (centre halfWidth : Quantity k R) (ord : OrderKind k) :
    (IccQ.about centre halfWidth ord).lo.q.magnitude = centre.magnitude - halfWidth.magnitude :=
  rfl

@[simp] theorem about_hi [Add R] [Sub R] (centre halfWidth : Quantity k R) (ord : OrderKind k) :
    (IccQ.about centre halfWidth ord).hi.q.magnitude = centre.magnitude + halfWidth.magnitude :=
  rfl

/-- **Membership** `x ∈ [lo, hi]`, as the conjunction of the two directional facts —
each endpoint contributes only the orientation its role can state. -/
def Mem [LE R] (I : IccQ k R) (x : Quantity k R) : Prop := I.lo.le x ∧ I.hi.ge x

/-- **The executable eliminator**: clamp `x` into the interval, as
`min (max x lo) hi` — clamp-from-below first, then from above. This association (and
not `Quantity.clamp`'s `max lo (min hi x)`) is the one deployed batched kernels use;
keeping it lets a kinded kernel erase bit-exactly, op-for-op, to its naked form. -/
def clamp [Min R] [Max R] (I : IccQ k R) (x : Quantity k R) : Quantity k R :=
  ⟨Min.min (Max.max x.magnitude I.lo.q.magnitude) I.hi.q.magnitude⟩

@[simp] theorem clamp_magnitude [Min R] [Max R] (I : IccQ k R) (x : Quantity k R) :
    (I.clamp x).magnitude
      = Min.min (Max.max x.magnitude I.lo.q.magnitude) I.hi.q.magnitude := rfl

/-- **The interval survives a representation cast** — both endpoints moved by the same
carrier map, through their own roles. This is the whole of what a carrier lift of a
configuration box *is*, and stating it once is what keeps it from being re-authored per
box: a record of four intervals lifted field-wise erases and re-mints eight endpoints if
this is missing, and the boundary audit reads every one of those as a mint.

The cast needs no `OrderKind`: the interval already exists, so the scale gate was
discharged where it was formed, and a representation change cannot revoke it. It does
not preserve `Ordered` for an arbitrary `f` — an order-reversing or non-injective cast
is a real possibility — which is why the orientation fact travels as a proof about the
endpoints and not as an invariant of the structure. -/
def castCarrier {S : Type} (f : R → S) (I : IccQ k R) : IccQ k S :=
  ⟨I.lo.castCarrier f, I.hi.castCarrier f⟩

@[simp] theorem castCarrier_lo {S : Type} (f : R → S) (I : IccQ k R) :
    (I.castCarrier f).lo.q.magnitude = f I.lo.q.magnitude := rfl

@[simp] theorem castCarrier_hi {S : Type} (f : R → S) (I : IccQ k R) :
    (I.castCarrier f).hi.q.magnitude = f I.hi.q.magnitude := rfl

@[simp] theorem of_lo (lo hi : Quantity k R) (ord : OrderKind k) :
    (IccQ.of lo hi ord).lo.q = lo := rfl

@[simp] theorem of_hi (lo hi : Quantity k R) (ord : OrderKind k) :
    (IccQ.of lo hi ord).hi.q = hi := rfl

end IccQ

/-! ## Executable order deciders — the host-carrier counterparts of the Prop formers

The Prop formers above state order facts at proof carriers, and `Quantity` deliberately
has no `LE`/`Ord` instance — on a batched deployment carrier "if it type-checks it is one
branch-free elementwise kernel" is a design law. But host-side *per-scalar* logic
(quality flags, QC-level classification, threshold audits) is legitimately branchy, and
it needs the same order queries as `Bool`s. These deciders are the opt-in executable
counterparts, gated on the carrier having **decidable order**: host scalars (`Float`,
`Int`, `Rat`, …) have it, batched deployment carriers do not — so the branchless law
holds by *instance absence*, not by convention.

Two disciplines carry over from the Prop formers:

  * **Kind-gated**: both operands of a comparison share the kind `k`, so comparing a
    reflectivity against a water-content threshold is a type error, exactly as for `+`.
  * **Directional on bounds**: a bound is queried only from its own side — an
    `UpperBound` can be `hitBy` a quantity rising to meet it, a `LowerBound` by one
    falling to meet it; there is no former asking whether a quantity sits on a bound's
    *other* side, so a max/min swap remains unwritable through the bounds' API. -/

namespace Quantity

variable {k : KindOfProperty} {R : Type}

/-- Executable same-kind `≤` at a host carrier with decidable order. -/
def leb [LE R] [∀ x y : R, Decidable (x ≤ y)] (x y : Quantity k R) : Bool :=
  decide (x.magnitude ≤ y.magnitude)

/-- Executable same-kind `<` at a host carrier with decidable order. -/
def ltb [LT R] [∀ x y : R, Decidable (x < y)] (x y : Quantity k R) : Bool :=
  decide (x.magnitude < y.magnitude)

/-- Executable same-kind `≥` — `x.geb y` is `y.leb x`. -/
def geb [LE R] [∀ x y : R, Decidable (x ≤ y)] (x y : Quantity k R) : Bool := y.leb x

/-- Executable same-kind `>` — `x.gtb y` is `y.ltb x`. -/
def gtb [LT R] [∀ x y : R, Decidable (x < y)] (x y : Quantity k R) : Bool := y.ltb x

end Quantity

/-- **Does `x` satisfy this lower bound?** The `Bool` counterpart of `LowerBound.le`, and
like it the only orientation a `LowerBound` can be queried in: the bound stays on the left
of the `≤`, so an endpoint can never be used as if it bounded from above.

Distinct from `hitBy`, and the pair is worth keeping straight because both are non-strict
and they coincide exactly at the endpoint. `leb` is a **conformity** test — is this value
admissible — and is the one a calibration range, an acceptance limit or a validity check
asks. `hitBy` is a **saturation** test — has this value reached the constraint — and is the
one a clamped retrieval's QC asks. Same operands, opposite senses, and the reason a single
`≤` on magnitudes is not an adequate spelling of either. -/
def LowerBound.leb {k : KindOfProperty} {R : Type} [LE R] [∀ x y : R, Decidable (x ≤ y)]
    (b : LowerBound k R) (x : Quantity k R) : Bool :=
  decide (b.q.magnitude ≤ x.magnitude)

/-- **Does `x` satisfy this upper bound?** The `Bool` counterpart of `UpperBound.ge` — the
dual of `LowerBound.leb`, with the bound on the right of the `≤`. -/
def UpperBound.geb {k : KindOfProperty} {R : Type} [LE R] [∀ x y : R, Decidable (x ≤ y)]
    (b : UpperBound k R) (x : Quantity k R) : Bool :=
  decide (x.magnitude ≤ b.q.magnitude)

/-- **Executable membership** `x ∈ [lo, hi]` — the `Bool` counterpart of `IccQ.Mem`, built
from the two directional deciders so that each endpoint contributes only the orientation its
role can state. A consumer testing a value against a range never writes the comparison, and
therefore cannot write it backwards. -/
def IccQ.memb {k : KindOfProperty} {R : Type} [LE R] [∀ x y : R, Decidable (x ≤ y)]
    (I : IccQ k R) (x : Quantity k R) : Bool :=
  I.lo.leb x && I.hi.geb x

/-- **An upper bound is hit from below**: `x` sits at or beyond the bound — the
executable counterpart of the *negation* of strict interiority, and the only direction
an `UpperBound` can be queried in (the bound-hit test of a box-constrained fit's QC). -/
def UpperBound.hitBy {k : KindOfProperty} {R : Type} [LE R] [∀ x y : R, Decidable (x ≤ y)]
    (b : UpperBound k R) (x : Quantity k R) : Bool :=
  decide (b.q.magnitude ≤ x.magnitude)

/-- **A lower bound is hit from above**: `x` sits at or below the bound — the dual of
`UpperBound.hitBy`, and the only direction a `LowerBound` can be queried in (the
saturation test of a clamped retrieval's QC). -/
def LowerBound.hitBy {k : KindOfProperty} {R : Type} [LE R] [∀ x y : R, Decidable (x ≤ y)]
    (b : LowerBound k R) (x : Quantity k R) : Bool :=
  decide (x.magnitude ≤ b.q.magnitude)

/-! ## Rounding an endpoint — see `PropertyKindCalculus.Decimal`

Shortening a magnitude to fewer digits is a rounding, and **which way it may move is decided by
the role the magnitude plays, not by which neighbour is nearer**: a floor rounded up is no
longer under what it was constructed to sit under, and a ceiling rounded down no longer covers
it. The consequence is unbounded while the size of the change is arbitrarily small, so no
tolerance argument reaches it — direction is the whole question, and direction is exactly what
the two roles above carry.

`LowerBound.roundedDown` and `UpperBound.roundedUp` are therefore part of this family, but they
live in `PropertyKindCalculus.Decimal` and not here, so that the many consumers of a bound do
not acquire a dependency on decimal text to get one. That module also explains why neither it
nor this one offers a `roundToNearest`.

**The role above is not the whole of what fixes the direction**, and the limit is worth knowing
here rather than being discovered downstream. What these two types record is *which side* the
endpoint is on — enough to make a comparison written backwards unstateable, which is what they
were built for. It is not enough to say which way the endpoint may be shortened, because that
also depends on whether the bound is **asserted** about a quantity ("this holds at most `X`",
where raising `X` keeps the claim true) or **imposed** upon one ("`y` must be at most `L`",
where raising `L` admits values that should have failed). Same side, opposite safe direction.
`Decimal` carries both pairs for that reason, and the second is named `…AsRequirement`. -/

end PropertyKindCalculus
