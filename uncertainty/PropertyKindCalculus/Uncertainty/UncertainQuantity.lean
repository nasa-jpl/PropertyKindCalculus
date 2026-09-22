/-
`PropertyKindCalculus.Uncertainty.UncertainQuantity` — a kinded quantity paired with its input
uncertainty descriptor.

This is *additive* metadata over the existing `Quantity k R` (exactly the pattern the roadmap
used for vector quantities): the carrier tower is untouched. The same descriptor feeds both the
UQ methods (Area 1) and the numerical-adequacy check (Area 2) — the architectural hinge of
`UNCERTAINTY.md`.
-/

module

public import PropertyKindCalculus.Quantity
public import PropertyKindCalculus.Uncertainty.InputDist

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Uncertainty

open PropertyKindCalculus

/-- **A quantity with a stated input uncertainty.** The kinded value plus its `InputDist`. The
value's magnitude and the descriptor's `mean` are independent data: `value` is the point
estimate, `dist.moments.mean` the distribution's expectation (they usually coincide). -/
structure UncertainQuantity (k : KindOfProperty) (R : Type) where
  /-- The kinded point value. -/
  value : Quantity k R
  /-- The input uncertainty descriptor. -/
  dist : InputDist R

/-- Build an uncertain quantity whose point value is the distribution's mean (the common case). -/
def UncertainQuantity.atMean {k : KindOfProperty} (d : InputDist Float) :
    UncertainQuantity k Float :=
  { value := ⟨d.moments.mean⟩, dist := d }

end PropertyKindCalculus.Uncertainty

end -- pkc-blanket-expose
end -- pkc-blanket
