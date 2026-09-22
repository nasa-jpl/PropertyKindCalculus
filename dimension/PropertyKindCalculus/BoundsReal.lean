/-
# The `Set`-theoretic view of a kind-indexed interval — `IccQ.toIcc`

`IccQ k R` (`PropertyKindCalculus.Bounds`) is the direction-locked, kind-indexed
closed interval, deliberately Mathlib-free: it carries its endpoints as `LowerBound` /
`UpperBound` roles and states order only through their directional formers. That core
is enough to *construct* intervals and clamp into them, but a theorem quantifying over
the points of an interval — well-posedness on `[lo, hi]`, a monotone map on a box —
wants Mathlib's `Set.Icc`, the standard object the analysis lemmas (`intermediate_value_Icc`,
`StrictMonoOn`, `ContinuousOn`) are stated against.

`toIcc` is that bridge, and it lives with the `Dimension` library for exactly the reason
`QuantityReal` does: `Set.Icc` needs Mathlib, the one dependency kept out of the core. It
is **not** ℝ-specific — the projection and the membership bridge hold for any `[Preorder R]`
(ℝ is the headline consumer, being the carrier the quantity laws are proved over). The
membership bridge `mem_toIcc` is `Iff.rfl`: `IccQ.Mem` is by construction the conjunction
of the two directional facts `lo ≤ x` and `x ≤ hi`, which is exactly `Set.Icc`'s membership,
so a downstream corollary keyed to a kinded box delegates to a Mathlib lemma with no
rewriting across the seam.
-/

module

public import PropertyKindCalculus.Bounds
public import Mathlib.Order.Interval.Set.Basic

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.IccQ

variable {k : KindOfProperty} {R : Type}

/-- **The kind-indexed interval as a Mathlib `Set.Icc`** — the bridge from the
direction-locked `IccQ` (core `Bounds`, Mathlib-free) to the set the order/analysis
lemmas quantify over. `Preorder`-generic; it lives in the Mathlib-backed `Dimension`
library because `Set.Icc` is the dependency the core omits. -/
def toIcc [Preorder R] (I : IccQ k R) : Set R :=
  Set.Icc I.lo.q.magnitude I.hi.q.magnitude

/-- **The membership bridge, definitional.** A magnitude lies in the projected `Set.Icc`
exactly when the quantity satisfies the box's own kinded membership `IccQ.Mem` — the
conjunction of the two directional formers `lo.le x` and `hi.ge x`. It is `Iff.rfl`
because `Set.Icc`'s membership unfolds to the same conjunction, so a corollary stated
through the kinded box discharges against a Mathlib lemma with no rewriting. -/
theorem mem_toIcc [Preorder R] (I : IccQ k R) (x : Quantity k R) :
    x.magnitude ∈ I.toIcc ↔ I.Mem x := Iff.rfl

end PropertyKindCalculus.IccQ

end -- pkc-blanket-expose
end -- pkc-blanket
