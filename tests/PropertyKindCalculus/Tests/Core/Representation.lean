/-
# Validation probes — representation parametricity (R10, R11)

Inhabitation and axiom-profile probes for carrier parametricity: the exec/spec refinement bridge
(R10) and the vector carrier (R11).

R10's `add_refines` is easy to satisfy *vacuously* with a trivial (identity) refinement, which
would exercise no rounding. The Rule-2 boundary is therefore a **genuinely lossy** carrier: `Grid`
below is an executable carrier whose addition snaps sums to the even grid, refining `Int` with a
non-identity `round`. On it, `3 +Grid 2` forgets to `4`, not `5` — so the bridge is applied where
rounding actually happens.

R11's witness is a real `Fin 3` vector quantity, which forces the pointwise `LawfulCarrier`
instance to resolve and its additivity laws to hold by the same parametric proof used for scalars.
(Core is Mathlib-free, so the vector is built by an explicit function, not `![…]`.)

The array carrier's one honest default is probed both ways: `default` at `Array` *is* the empty
table (it asserts no magnitude), while a scalar `default` is **rejected** at compile time — a
default scalar quantity would be a fabricated magnitude, so no instance provides one.
-/

import PropertyKindCalculus

namespace PropertyKindCalculus.Tests.Representation

open PropertyKindCalculus

/-- Length, a ratio kind (its scale licenses `+`). -/
def lengthK : KindOfProperty := { id := "length", scale := .ratio }
theorem diffLen : DifferenceKind lengthK := DifferenceKind.ofScale

/-! ## R10 — a lawful ℝ-style spec descends to a lossy exec carrier as one rounding step -/

/-- A toy *executable* carrier: integers whose addition snaps the sum down to the even grid. It is
a `Carrier` but not a `LawfulCarrier` — exactly the exec/spec split R10 is about. -/
structure Grid where
  /-- The stored value. -/
  run : Int
deriving DecidableEq, Repr

instance : Carrier Grid where
  zero := ⟨0⟩
  add x y := ⟨2 * ((x.run + y.run) / 2)⟩

/-- `Grid` refines the exact spec carrier `Int`: forget with `run`, round by snapping to the even
grid. The bridge law holds by `rfl` — forgetting an exec addition *is* rounding the spec sum. -/
instance : CarrierRefinement Grid Int where
  toSpec e := e.run
  round s := 2 * (s / 2)
  toSpec_zero := rfl
  toSpec_add _ _ := rfl

/-- Two exec magnitudes, 3 and 2. -/
def gx : Quantity lengthK Grid := ⟨⟨3⟩⟩
def gy : Quantity lengthK Grid := ⟨⟨2⟩⟩

-- Inhabitation: the R10 capstone applied to concrete exec quantities over a *non-trivial*
-- refinement — the exec sum, viewed in the spec carrier, equals the rounded spec sum.
theorem r10_add_refines :
    (Quantity.toSpec (Quantity.add diffLen gx gy) : Quantity lengthK Int)
      = Quantity.roundBy (CarrierRefinement.round (E := Grid))
          (Quantity.add diffLen (Quantity.toSpec gx) (Quantity.toSpec gy)) :=
  Quantity.add_refines diffLen gx gy

-- and rounding is genuinely exercised: the spec sum is 5, but the exec sum forgets to 4.
#guard (Quantity.toSpec gx : Quantity lengthK Int).magnitude
        + (Quantity.toSpec gy : Quantity lengthK Int).magnitude == 5
#guard (Quantity.toSpec (Quantity.add diffLen gx gy) : Quantity lengthK Int).magnitude == 4

/-- info: 'PropertyKindCalculus.Quantity.add_refines' depends on axioms: [propext] -/
#guard_msgs in #print axioms Quantity.add_refines

/-! ### R10 across the multiplicative surface — the same bridge carries `×` and `÷`

An additive bridge lets nothing but the extensive mode cross. `Grid` is given the *same* even-grid
snap for `*` and `/` that it uses for `+`, so `MulRefinement`/`DivRefinement` hold by `rfl` over a
genuinely lossy rounding, and the two kind-crossing capstones are applied where rounding bites. -/

/-- `Grid`'s multiplication snaps to the even grid, exactly as its addition does. -/
instance : Mul Grid where mul x y := ⟨2 * ((x.run * y.run) / 2)⟩

/-- And so does its division. -/
instance : Div Grid where div x y := ⟨2 * ((x.run / y.run) / 2)⟩

/-- A `Grid` magnitude is one number, so its `*` is the multiplication of magnitudes. -/
instance : ScalarCarrier Grid := ⟨⟩

instance : MulRefinement Grid Int where toSpec_mul _ _ := rfl
instance : DivRefinement Grid Int where toSpec_div _ _ := rfl

/-- Area — the product kind of two lengths, so the bridge is applied across a kind change. -/
def areaK : KindOfProperty := { id := "area", scale := .ratio }

theorem prodLen : ProductKind lengthK lengthK areaK := .ofRatio _ _ _
theorem quotArea : QuotientKind areaK lengthK lengthK := .ofRatio _ _ _

/-- A unit exec length and a 9-unit exec area. -/
def gOne : Quantity lengthK Grid := ⟨⟨1⟩⟩
def gArea : Quantity areaK Grid := ⟨⟨9⟩⟩

-- Inhabitation: the exec product, viewed in the spec carrier, is the rounded spec product — and
-- the kinds move from `lengthK × lengthK` to `areaK` under the same license on both sides.
theorem r10_mul_refines :
    (Quantity.toSpec (Quantity.mul prodLen gx gx) : Quantity areaK Int)
      = Quantity.roundBy (CarrierRefinement.round (E := Grid))
          (Quantity.mul prodLen (Quantity.toSpec gx) (Quantity.toSpec gx)) :=
  Quantity.mul_refines prodLen gx gx

theorem r10_div_refines :
    (Quantity.toSpec (Quantity.div quotArea gArea gOne) : Quantity lengthK Int)
      = Quantity.roundBy (CarrierRefinement.round (E := Grid))
          (Quantity.div quotArea (Quantity.toSpec gArea) (Quantity.toSpec gOne)) :=
  Quantity.div_refines quotArea gArea gOne

-- and rounding is genuinely exercised at both: 3 × 3 is 9 exactly but forgets to 8, and
-- 9 ÷ 1 is 9 exactly but forgets to 8. Neither capstone is vacuous.
#guard (Quantity.toSpec gx : Quantity lengthK Int).magnitude
        * (Quantity.toSpec gx : Quantity lengthK Int).magnitude == 9
#guard (Quantity.toSpec (Quantity.mul prodLen gx gx) : Quantity areaK Int).magnitude == 8
#guard (Quantity.toSpec gArea : Quantity areaK Int).magnitude
        / (Quantity.toSpec gOne : Quantity lengthK Int).magnitude == 9
#guard (Quantity.toSpec (Quantity.div quotArea gArea gOne) : Quantity lengthK Int).magnitude == 8

-- Why `DivRefinement` can be unconditional here and cannot be on a machine: `Int` (like `ℝ`)
-- totalizes `x / 0` to `0`, so both sides of the law agree with nothing to exclude, whereas IEEE
-- division does not — which is why the executable rung carries `dy.significand ≠ 0` as a hypothesis
-- (`Quantity.div_refines_exec`) and `Float` is given no refinement instance at all.
#guard ((9 : Int) / 0) == 0
#guard (((⟨9⟩ : Grid) / ⟨0⟩ : Grid)).run == 0
#guard ((1.0 : Float) / 0.0) != 0.0

/-- info: 'PropertyKindCalculus.Quantity.mul_refines' does not depend on any axioms -/
#guard_msgs in #print axioms Quantity.mul_refines

/-- info: 'PropertyKindCalculus.Quantity.div_refines' does not depend on any axioms -/
#guard_msgs in #print axioms Quantity.div_refines

/-! ## R11 — a vector quantity is a numerical array under one scalar unit -/

/-- Two 3-vectors, `[1,2,3]` and `[4,5,6]`, as single kind-`lengthK` quantities over the pointwise
carrier `Fin 3 → Int` (built explicitly — no Mathlib `![…]`). -/
def vx : Quantity lengthK (Fin 3 → Int) := ⟨fun i => (i.val : Int) + 1⟩
def vy : Quantity lengthK (Fin 3 → Int) := ⟨fun i => (i.val : Int) + 4⟩

-- Inhabitation: the additivity laws hold at the *vector* carrier by the same parametric proof used
-- for scalars — applying `laws_parametric` here forces `LawfulCarrier (Fin 3 → Int)`
-- (= `instLawfulCarrierPi`) to resolve, so the instance is exercised, not merely declared.
theorem r11_vector_laws :
    Quantity.add diffLen vx vy = Quantity.add diffLen vy vx
      ∧ Quantity.add diffLen (Quantity.add diffLen vx vy) vx
          = Quantity.add diffLen vx (Quantity.add diffLen vy vx)
      ∧ Quantity.add diffLen Quantity.zero vx = vx
      ∧ Quantity.add diffLen vx Quantity.zero = vx :=
  Quantity.laws_parametric diffLen vx vy vx

-- and addition is pointwise: component 0 is 1+4=5, component 2 is 3+6=9 (one unit, whole vector).
#guard (Quantity.add diffLen vx vy).magnitude 0 == 5
#guard (Quantity.add diffLen vx vy).magnitude 2 == 9

/-- info: 'PropertyKindCalculus.instLawfulCarrierPi' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms instLawfulCarrierPi

-- The one honest default: at the executable array carrier, `default` is the EMPTY table — no
-- components, so no magnitude is asserted (the panic fallback `xs[i]!` needs on an array of
-- vector quantities) …
#guard (default : Quantity lengthK (Array Int)).magnitude == #[]
-- … while a scalar default stays rejected: a default scalar quantity would be a fabricated
-- magnitude, so no `Inhabited` instance provides one.
#check_failure (default : Quantity lengthK Int)

/-- info: 'PropertyKindCalculus.instInhabitedQuantityArray' does not depend on any axioms -/
#guard_msgs in #print axioms instInhabitedQuantityArray

-- Component access is ONE licensed form across representations: the boxed `Array` and the
-- packed `FloatArray` read through the same `Quantity.get!` (any `Nat`-indexed `GetElem?`
-- collection) — a packed column is a representation choice, not a different metrological
-- object, and each component is a quantity of the table's own kind.
def boxedLen : Quantity lengthK (Array Int) := ⟨#[7, 8, 9]⟩
def packedLen : Quantity lengthK FloatArray := ⟨FloatArray.mk #[7.5, 8.5]⟩
#guard (boxedLen.get! 1).magnitude == 8
#guard (packedLen.get! 0).magnitude == 7.5
-- the kind is the table's own — a component of a length table IS a length:
example : Quantity lengthK Int := boxedLen.get! 2
example : Quantity lengthK Float := packedLen.get! 1
-- and the packed table has the same one honest default the boxed one does — empty, asserting
-- no magnitude — so an array OF kinded packed columns can index with `xs[i]!`:
#guard (default : Quantity lengthK FloatArray).magnitude.size == 0

end PropertyKindCalculus.Tests.Representation
