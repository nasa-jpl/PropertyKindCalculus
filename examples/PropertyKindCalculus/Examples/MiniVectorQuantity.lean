/-
# Worked examples — the vector quantity (R11)

ISO 80000-2 §18 reads a vector quantity as *a numerical vector times one scalar unit*: the
numbers are indexed, the unit is not. R11 is that sentence as a requirement, and this module
is the checked scenario for it — a rover's displacement across a three-axis grid, one kind,
one unit, three numbers.

Three claims are exercised, and the third is the one that carries R11's weight:

  1. **One kind, an indexed carrier.** `Quantity displacement (Fin 3 → Int)` is a quantity of
     a single kind whose magnitude happens to be an array. No kind is indexed by an axis.
  2. **The laws transfer for free.** The pointwise carrier is lawful whenever its scalars
     are, so `Quantity.add_comm` and `add_assoc` — proved once over any lawful carrier —
     apply at the vector carrier with no vector-specific proof.
  3. **The unit stays scalar, and the type system enforces it.** A pointwise product of two
     vector quantities is *not* a product of kinds: `Quantity.mul` is gated on
     `ScalarCarrier`, which the array carrier does not instantiate, so the multiplication a
     bare array would happily perform does not typecheck. What *is* licensed is a scalar
     quantity acting on a vector one (`Quantity.smulK`), which is §18's own reading of
     "a numerical vector times one scalar unit".

Mathlib-free. The frame side of §18 — that the quantity is independent of the choice of
coordinate system while its components are not — is R20, in
`PropertyKindCalculus.DimensionExamples.Frames`.
-/

import PropertyKindCalculus.QuantityVector

namespace PropertyKindCalculus.Examples.MiniVectorQuantity

open PropertyKindCalculus

/-! ## One kind for the whole vector -/

/-- Displacement: one kind, whatever the axis. -/
def displacement : KindOfProperty := { id := "displacement", scale := .ratio }

/-- A dimensionless scale factor, the scalar that will act on a displacement. -/
def factor : KindOfProperty := { id := "scale factor", scale := .ratio }

theorem hDisp : DifferenceKind displacement := .ofScale

/-- A three-axis displacement: **one** quantity, three numbers. Nothing here is indexed by
an axis except the carrier. (Written as a plain function rather than Mathlib's `![…]`, since
this tier is Mathlib-free.) -/
def east : Quantity displacement (Fin 3 → Int) := ⟨fun i => if i = 0 then 3 else 0⟩

/-- A second one, up the third axis. -/
def up : Quantity displacement (Fin 3 → Int) := ⟨fun i => if i = 2 then 7 else 0⟩

/-! ## The laws transfer, with no vector-specific proof -/

/-- Addition is componentwise, and it is the *same* `Quantity.add` the scalar carriers use. -/
example : (Quantity.add hDisp east up).magnitude 0 = 3 := by decide

/-- The third axis likewise — one addition, three components. -/
example : (Quantity.add hDisp east up).magnitude 2 = 7 := by decide

/-- Commutativity at the vector carrier, discharged by the law proved once over any lawful
carrier. The pointwise carrier is lawful because its scalars are. -/
theorem vector_add_comm (x y : Quantity displacement (Fin 3 → Int)) :
    Quantity.add hDisp x y = Quantity.add hDisp y x := Quantity.add_comm hDisp x y

/-- Associativity, likewise. -/
example (x y z : Quantity displacement (Fin 3 → Int)) :
    Quantity.add hDisp (Quantity.add hDisp x y) z
      = Quantity.add hDisp x (Quantity.add hDisp y z) := Quantity.add_assoc hDisp x y z

/-! ## The unit is scalar — the refusal that makes R11 a requirement rather than a habit -/

/-- The product law is available at the level of kinds: a scale factor times a displacement
is a displacement. -/
theorem hScale : ProductKind factor displacement displacement := .ofRatio _ _ _

/-- The pointwise scalar action the example uses. Lean core declares `SMul` but ships no
instance at a function type, and this tier is Mathlib-free, so the scenario supplies the one
it needs: multiply every component by the scalar. -/
instance : SMul Int (Fin 3 → Int) := ⟨fun a v i => a * v i⟩

/-- **Licensed**: a scalar quantity acting on a vector one. The numbers scale componentwise;
the kinds change exactly as the law says. This is §18's "numerical vector times one scalar
unit", with the scalar carrying a kind of its own. -/
def doubled : Quantity displacement (Fin 3 → Int) :=
  Quantity.smulK hScale (⟨2⟩ : Quantity factor Int) east

/-- The scaled displacement reads `6` along the first axis. -/
theorem doubled_east : doubled.magnitude 0 = 6 := by decide

/-- The scalar action satisfies its own classification certificate by construction (R12). -/
example : doubled.IsSMul hScale (⟨2⟩ : Quantity factor Int) east :=
  Quantity.smulK_isSMul hScale _ _

/-- A kind for the pointwise square a bare array would happily compute — named only so the
refusal below is about the *carrier* and not about a missing law. -/
def displacementSq : KindOfProperty := { id := "displacement squared", scale := .ratio }

theorem hSquare : ProductKind displacement displacement displacementSq := .ofRatio _ _ _

/-- A componentwise multiplication on the array carrier — supplied here so that the refusal
below is not merely "arrays cannot be multiplied". With this instance in scope the arithmetic
`Quantity.mul` would perform is perfectly available. -/
instance : Mul (Fin 3 → Int) := ⟨fun v w i => v i * w i⟩

-- **Refused**: two displacements multiplied pointwise. The kind law `hSquare` exists and the
-- pointwise `Mul` exists, so neither the kinds nor the arithmetic is missing; what stops it is
-- `Quantity.mul`'s `ScalarCarrier` gate, which `Fin 3 → Int` does not instantiate. The unit is
-- scalar, and there is no unit for which a componentwise square of a displacement is a
-- quantity — which is why R11 is a requirement and not a habit.
#check_failure Quantity.mul hSquare east east

end PropertyKindCalculus.Examples.MiniVectorQuantity
