/-
# Agreement — "close enough", as a kinded interval rather than as a floating-point idiom

Every comparison of a computed number against an expected one needs a notion of *close enough*,
and the idiom it is usually written in —

    (a - b).abs ≤ 1e-6 * b.abs

— has three defects that this calculus exists to fix, all of them visible in that single line.
The **kind** is gone: `a` and `b` could be a reflectivity and a water content, and the comparison
would still typecheck and still return a `Bool`. The **tolerance** is a naked number that is
neither of their kinds and is not distinguishable, at the level of representation, from any other
ratio in the deployment — a usable fraction, an amplification, a coverage factor. And the
**interval** is implicit: the thing the comparison is really asking is whether `a` lies in
`[b − h, b + h]`, but that interval is never constructed, so it cannot be reported, inspected,
widened, or reasoned about. A test that fails prints `false`.

This module is that comparison, written once and correctly:

  * `relativeTolerance` — the tolerance as a **kind**. Dimension one, like every ratio here, and
    therefore indistinguishable from the others by representation alone; the kind is the whole
    instrument, and it is what stops a usable-memory fraction from being handed to a comparison
    as though it were an agreement tolerance.
  * `agreementInterval` — the **interval** the comparison is about, built with `IccQ.about` so
    that its two endpoints come from one centre and one half-width and cannot disagree. It is a
    value: report it, print it, take its width, feed it to a bound-hit test.
  * `Quantity.closeTo` — the `Bool`, as membership in that interval, through `IccQ.memb`'s
    directional deciders. Both arguments carry the measurand's kind, so a cross-kind comparison is
    a type error rather than a passing test.

**The half-width is `max(rel·|reference|, floor)`, and the floor is explicit.** A purely relative
tolerance is useless near zero — it demands exact equality at a reference of `0` — so the usual
idiom carries a hidden absolute epsilon (`… || d ≤ 1e-9 * (1 + |b|)`). That epsilon is a quantity
of the *measurand's* kind, not a ratio, and its value is a decision about the comparison rather
than a constant of nature. So it is an argument, at that kind, defaulting to zero: a caller who
needs a floor states it, and a caller who does not is not silently given one.

Mathlib-free core, `Float`-carried: this is host-side per-scalar logic, the tier `Bounds.lean`'s
executable deciders are for, and batched carriers deliberately cannot reach it.
-/

module

public import PropertyKindCalculus.Bounds
public import PropertyKindCalculus.QuantityClassification

public section Interface

namespace PropertyKindCalculus

/-- **The relative tolerance of an agreement** — how far a computed value may sit from a reference
value, as a fraction of the reference.

A ratio, so dimension one, so indistinguishable at the level of representation from every other
ratio a deployment handles — a usable-memory fraction, a residency amplification, a coverage
factor. The kind is the whole instrument: an amplification used as a tolerance, or a tolerance
deflating a budget, is arithmetic that typechecks and means nothing.

Deliberately *not* the same kind as a coverage factor (`Uncertainty.coverageFactor`). A coverage
factor multiplies a standard *uncertainty* and is a statement about a distribution; a relative
tolerance multiplies an *estimate* and is a statement about how much disagreement a comparison
will accept. They are both dimension one, they both appear in the neighbourhood of a measurement
record, and nothing but their kinds keeps them apart. -/
@[expose] def relativeTolerance : KindOfProperty :=
  { id := "relative agreement tolerance", scale := .ratio }

/-- **The law that scales a reference into an allowance**: a relative tolerance times a quantity
of the measurand's kind is a quantity of that same kind. This is what makes `rel·|reference|` a
construction rather than a re-stamp — the tolerance is dimension one *in the specific role of
scaling a reference into a half-width*, and that role is what the law records.

Requires the measurand's kind to be ratio-scale, which is the same precondition a *relative*
comparison needs on its own terms: "within 1 % of" presupposes that ratios of the quantity mean
something, which is exactly what a ratio scale is. -/
theorem toleranceLaw (k : KindOfProperty) (hk : k.IsRational) :
    ProductKind relativeTolerance k k :=
  ProductKind.ofRatio relativeTolerance k k rfl hk hk

/-- **The interval a comparison is really about**: `reference ± max(rel·|reference|, floor)`.

Built through `IccQ.about`, so both endpoints derive from one centre and one half-width and the
orientation cannot be written backwards; and through `Quantity.mul` on `toleranceLaw`, so the
half-width's kind is derived from a stated law. Being a *value* rather than a hidden step is the
point: it can be reported when a comparison fails, which is the difference between "false" and
"22.7 is outside [22.1, 22.5]".

The `floor` is an absolute allowance at the measurand's own kind, for the near-zero case a purely
relative tolerance cannot express. It defaults to zero — a caller who needs one states it. -/
@[expose] def agreementInterval {k : KindOfProperty} (reference : Quantity k Float)
    (rel : Quantity relativeTolerance Float) (floor : Quantity k Float := ⟨0.0⟩)
    (hk : k.IsRational := by rfl) : IccQ k Float :=
  let scaled := Quantity.mul (toleranceLaw k hk) rel ⟨reference.magnitude.abs⟩
  let halfWidth : Quantity k Float :=
    if scaled.magnitude ≥ floor.magnitude then scaled else floor
  IccQ.about reference halfWidth (OrderKind.ofScale (by rw [(hk : k.scale = .ratio)]; trivial))

/-- **Does `x` agree with `reference`, to within `rel` (and no closer than `floor`)?** Membership
in `agreementInterval`, through the interval's own directional deciders — so the comparison is
never written by hand and therefore cannot be written backwards, and both values carry the
measurand's kind, so comparing across kinds is a type error rather than a test that passes.

Every non-`NaN` value agrees with itself, and a `NaN` agrees with nothing — including another
`NaN` — because it satisfies neither directional decider. That is the wanted reading: a comparison
against a value that is not a number should fail, not pass by reflexivity. It is also why there is
no `closeTo_self` theorem here; the statement is false as written, and stating it with the
hypothesis that excludes `NaN` needs an order algebra a Mathlib-free core does not have. -/
@[expose] def Quantity.closeTo {k : KindOfProperty} (x reference : Quantity k Float)
    (rel : Quantity relativeTolerance Float) (floor : Quantity k Float := ⟨0.0⟩)
    (hk : k.IsRational := by rfl) : Bool :=
  (agreementInterval reference rel floor hk).memb x

/-- The width of an agreement interval, at the measurand's kind — what to print when a comparison
fails, beside the value that missed it. -/
@[expose] def IccQ.width {k : KindOfProperty} (I : IccQ k Float) : Quantity k Float :=
  ⟨I.hi.q.magnitude - I.lo.q.magnitude⟩

end PropertyKindCalculus

end Interface
