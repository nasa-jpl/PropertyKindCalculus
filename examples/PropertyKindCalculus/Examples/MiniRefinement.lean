/-
# Worked example — the exec/spec refinement bridge (R10), on a toy carrier

A self-contained, Mathlib-free instance of `CarrierRefinement` exercising the
capstone `Quantity.add_refines`. The spec carrier is exact `Int`; the exec carrier
`Coarse` is an integer that *snaps to the even sublattice on every addition* — a
stand-in for binary truncation dropping the last bit. The refinement's `round` is
that same snap, so the bridge law holds by computation, and the capstone says: the
coarse (exec) sum, viewed back in `Int`, is the rounding of the exact (spec) sum.

The lawful `ℝ` instance of the same bridge is exercised in the Mathlib-backed
`PropertyKindCalculus.Examples.QuantityReal`; here `Int`-only keeps it in the
Mathlib-free `Examples` library.
-/

import PropertyKindCalculus.QuantityRefinement

namespace PropertyKindCalculus.Examples.MiniRefinement

open PropertyKindCalculus

/-- A toy **exec** carrier: an integer magnitude whose addition snaps to the even
sublattice (drops the last bit) — a stand-in for a lossy machine number. -/
structure Coarse where
  /-- The underlying integer. -/
  val : Int
deriving Repr

/-- Snap an integer to the even sublattice — the toy "round to representable". -/
def quantize (n : Int) : Int := 2 * (n / 2)

/-- `Coarse` is a `Carrier`: zero is exact, and addition rounds the integer sum. -/
instance : Carrier Coarse where
  zero := ⟨0⟩
  add x y := ⟨quantize (x.val + y.val)⟩

/-- `Coarse` **refines** exact `Int`: forget by `val`, round by `quantize`. The
bridge law `toSpec (x +ᴱ y) = round (toSpec x +ˢ toSpec y)` holds by computation —
both sides are `quantize (x.val + y.val)`. -/
instance : CarrierRefinement Coarse Int where
  toSpec := Coarse.val
  round := quantize
  toSpec_zero := rfl
  toSpec_add := fun _ _ => rfl

/-- A length kind to gate the quantities to (so the bridge is kind-indexed). -/
def lengthKind : KindOfProperty := { id := "length", scale := .ratio }

/-- `lengthKind` is ratio-scale, hence a `DifferenceKind` — the comparability
witness threaded explicitly into each `Quantity.add`/`add_refines`. -/
theorem hLen : DifferenceKind lengthKind := .ofScale

/-- Two coarse lengths: 3 and 2. -/
def a : Quantity lengthKind Coarse := ⟨⟨3⟩⟩
def b : Quantity lengthKind Coarse := ⟨⟨2⟩⟩

/-- The same two lengths forgotten to the exact spec carrier. -/
def aSpec : Quantity lengthKind Int := a.toSpec
def bSpec : Quantity lengthKind Int := b.toSpec

-- Rounding bites: the exact spec sum is 5, but the coarse exec sum snaps to 4.
#guard (Quantity.add hLen a b).magnitude.val == 4
#guard (Quantity.add hLen aSpec bSpec).magnitude == 5

/-- **The capstone, instantiated.** The coarse (exec) sum, viewed in the exact
carrier, is the rounding of the exact (spec) sum — `Quantity.add_refines` at the
toy carrier, threading the kind's comparability witness. -/
example :
    (Quantity.toSpec (Quantity.add hLen a b) : Quantity lengthKind Int)
      = Quantity.roundBy quantize (Quantity.add hLen aSpec bSpec) :=
  Quantity.add_refines hLen a b

/-- Zero refines exactly: no rounding at the additive unit. -/
example :
    Quantity.toSpec (Quantity.zero : Quantity lengthKind Coarse)
      = (Quantity.zero : Quantity lengthKind Int) :=
  Quantity.zero_refines

end PropertyKindCalculus.Examples.MiniRefinement
