/-
# Worked examples — the angle-augmented base (the reform PKC adopts)

Because PhysLib's `Dimension` is now parametric in its basis, PKC's canonical basis
`Base` promotes *plane angle* to a base dimension, with *solid angle* its square. These
checked examples exercise what that buys: the radian, steradian, and pure number are
dimensionally distinct; torque is energy *per angle*, so `torque ≠ energy` — the very
separation the five-generator sub-basis cannot draw (where `Dim.torque = Dim.energy`).
The angle-free catalogue lifts in unchanged, and the dimension-one confusions the kind
layer repairs survive the reform.

These live in the `DimensionExamples` library because they depend on PhysLib + Mathlib.
-/

module

public import PropertyKindCalculus.Interaction
public import PropertyKindCalculus.AngleReform

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Examples.AngleReform

open PropertyKindCalculus PropertyKindCalculus.AngleReform

/-! ## The five-generator sub-basis conflates; the angle-augmented base separates

The headline of the reform, side by side. Over PhysLib's five generators, torque and
energy are the *same* dimension — the classical `M·L²·T⁻²` identification. Over `Base`,
which carries `angle`, they are *different*: torque is energy per angle. Both are true;
the angle-augmented base is a strictly finer coordinatization. -/

/-- Sub-basis: torque and energy are dimensionally identified. -/
example : Dim.torque = Dim.energy := Dim.torque_eq_energy

/-- Angle-augmented base: torque and energy are dimensionally distinct. -/
example : AngleReform.torque ≠ AngleReform.energy := torque_ne_energy

/-- …yet the sanctioned product is still coherent — `torque · angle = energy`, by genuine
cancellation of the angle exponent rather than multiplication by a hidden `1`. -/
example : AngleReform.torque * planeAngle = AngleReform.energy := torque_mul_angle_eq_energy

/-! ## Radian, steradian, and number are three distinct dimensions -/

/-- The radian is not dimensionless. -/
example : planeAngle ≠ 1 := planeAngle_ne_one
/-- The steradian is not the radian. -/
example : solidAngle ≠ planeAngle := solidAngle_ne_planeAngle
/-- The steradian is the square of the radian: `sr = rad²`. -/
example : solidAngle = planeAngle * planeAngle := solidAngle_eq_sq

/-- As dimensioned kinds, the three are pairwise dimensionally distinct — a separation
the kind layer previously had to carry alone now also visible at the dimension layer. -/
example :
    radianKind.toDimension ≠ steradianKind.toDimension ∧
    radianKind.toDimension ≠ numberKind.toDimension ∧
    steradianKind.toDimension ≠ numberKind.toDimension :=
  radian_steradian_number_distinct

/-! ## The catalogue lifts in, kinds invariant — the base choice is invisible above

Re-coordinatizing a five-generator kind into the angle-augmented base leaves the *kind*
untouched (`extend_kind`) and preserves every original exponent (`extend`'s faithfulness
on the injective embedding). -/

/-- Lifting `lengthKind` fixes its kind. -/
example : (lengthKind.extend emb).kind = lengthKind.kind := lengthKind_lift_kind

/-- …and preserves its length exponent (`1`). -/
example :
    (lengthKind.extend emb).toDimension.exponent (emb .length)
      = lengthKind.toDimension.exponent .length :=
  lengthKind_lift_faithful

/-! ## The dimension-one conflation survives the reform

Promoting angle does not retire the kind layer. Volumetric and gravimetric water content
are angle-free, so over `Base` they are *still* one dimension yet distinct kinds — a
dimension-only classifier still cannot separate them, whatever the basis. -/

/-- Both lift to dimension one … -/
example : (vwc.extend emb).toDimension = (gwc.extend emb).toDimension :=
  waterContent_still_conflated.1
/-- … but remain distinct kinds. -/
example : (vwc.extend emb).kind ≠ (gwc.extend emb).kind :=
  waterContent_still_conflated.2

end PropertyKindCalculus.Examples.AngleReform

end -- pkc-blanket-expose
end -- pkc-blanket
