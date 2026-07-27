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

**Association of `clamp` (load-bearing).** `IccQ.clamp` computes
`min (max x lo) hi` — clamp-from-below first, then from above. This is the association
deployed batched kernels use, and it is *not* the same function as the function
calculus's `Quantity.clamp` (`max lo (min hi x)`): the two differ on NaN propagation
and on a degenerate `lo > hi` box, and they emit ops in different order on a tape
carrier. A kinded kernel authored with `IccQ.clamp` therefore erases *bit-exactly*,
op-for-op, to a naked `min (max x lo) hi` — which is what makes the kinded form
eligible to be the authored source of an already-deployed kernel.

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

end LowerBound

namespace UpperBound

/-- **The directional Prop former**: the upper bound is at or above `x` — the only order
relation statable through an `UpperBound`. -/
def ge {k : KindOfProperty} {R : Type} [LE R] (b : UpperBound k R) (x : Quantity k R) :
    Prop :=
  x.magnitude ≤ b.q.magnitude

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

@[simp] theorem of_lo (lo hi : Quantity k R) (ord : OrderKind k) :
    (IccQ.of lo hi ord).lo.q = lo := rfl

@[simp] theorem of_hi (lo hi : Quantity k R) (ord : OrderKind k) :
    (IccQ.of lo hi ord).hi.q = hi := rfl

end IccQ

end PropertyKindCalculus
