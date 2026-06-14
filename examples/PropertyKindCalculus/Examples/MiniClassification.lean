/-
# Worked example: verified classification and instantiable kind-laws (R12)

Demonstrates, as *checked* facts, the difference between a quantity-kind used as a
*tag* and used as a *certificate* (R12):

  1. **Verified construction.** A length built as `speed × time` through the product
     kind-law is classified as a length *by construction*; its certificate holds by
     `rfl`, and (Int carrier) its magnitude computes (`60 × 2 = 120`).
  2. **Certificate, not assertion.** A bare-tagged length `⟨999⟩` cannot be certified
     against the same factors — the certificate is *provably false*.
  3. **Kind-laws instantiate at the quantity level.** The QK-level uniqueness and
     canonicity theorems apply to concrete quantities by ordinary application.

Mathlib-free; part of the `Examples` library.
-/

import PropertyKindCalculus

namespace PropertyKindCalculus.Examples.Classification

open PropertyKindCalculus

/-! ## Kinds and the product kind-law -/

/-- A ratio kind: speed. -/
def speed  : KindOfProperty := { id := "speed",  scale := .ratio }
/-- A ratio kind: time. -/
def time   : KindOfProperty := { id := "time",   scale := .ratio }
/-- A ratio kind: length. -/
def length : KindOfProperty := { id := "length", scale := .ratio }

/-- The kind-law `length = speed × time` (all three ratio-scale). -/
theorem length_is_speed_times_time : ProductKind speed time length := ⟨rfl, rfl, rfl⟩

/-! ## (1) Verified construction (the certificate holds by construction) -/

/-- A concrete speed, `60`. -/
def v : Quantity speed Int := ⟨60⟩
/-- A concrete time, `2`. -/
def τ : Quantity time Int := ⟨2⟩

/-- A length built through the kind-law — classified `length` *by construction*. -/
def d : Quantity length Int := Quantity.mul length_is_speed_times_time v τ

-- the magnitude computes: 60 × 2 = 120
#guard d.magnitude == 120

-- the classification is certified, not asserted
example : d.IsProduct length_is_speed_times_time v τ := rfl

-- canonicity: any certified product equals the smart-constructed one
example : d = Quantity.mul length_is_speed_times_time v τ :=
  Quantity.eq_mul_of_isProduct length_is_speed_times_time rfl

/-! ## (2) A bare tag cannot be certified -/

/-- A length asserted by fiat — no witness, magnitude arbitrary. -/
def dFake : Quantity length Int := ⟨999⟩

-- `999 ≠ 60 × 2`, so the certificate against these factors is provably false
example : ¬ dFake.IsProduct length_is_speed_times_time v τ := by
  unfold Quantity.IsProduct
  decide

/-! ## (3) A QK-level theorem instantiated at the Q level (by application) -/

-- two quantities certified as the same product are equal
example (q q' : Quantity length Int)
    (hq : q.IsProduct length_is_speed_times_time v τ)
    (hq' : q'.IsProduct length_is_speed_times_time v τ) : q = q' :=
  Quantity.isProduct_unique length_is_speed_times_time hq hq'

end PropertyKindCalculus.Examples.Classification
