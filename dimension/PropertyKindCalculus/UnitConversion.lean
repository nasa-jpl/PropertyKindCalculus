/-
# Unit conversion over ℝ — the numeric faithful round-trip (VIM4 §1.22)

The `Int`-exponent conversion round-trip (`PropertyKindCalculus.UnitPrefix`) is exact
and Mathlib-free: it moves a magnitude's power-of-radix *exponent* and recovers it
because `Int` is an additive group. This module gives the companion *numeric*
statement over the real carrier — the magnitude itself is multiplied by the conversion
factor `radix ^ (shift p q)` — and proves the same round-trip closes on the nose,
provided the two units share a radix (`SameRadix`).

The point is that the §1.22 factor is *structurally* a power of the radix, hence
structurally nonzero once the radix is (`radix ≠ 0`, free for `10` and `2`). So the
round-trip `convertReal (convertReal x) = x` follows from `zpow_add₀` alone — the
planned generic *chosen-reference* unit (a `Unit k` carrying an arbitrary nonzero
reference `Quantity k`) would additionally have to *carry and discharge* an arbitrary
nonzeroness; the prefix case gets it for free. Lives in the `Dimension` library
because `ℝ` needs Mathlib, the one dependency kept out of the core.
-/

import PropertyKindCalculus.UnitPrefix
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic

namespace PropertyKindCalculus.PrefixedUnit

open PropertyKindCalculus

/-- **§1.22 — the conversion factor as a real number**: the unit's `radix` raised to
the power-of-radix `shift p q` (so `km → cm` is `10 ^ 5`, `MiB → KiB` is `2 ^ 10`).
`zpow` over `ℝ` is total, so this is defined for every pair of prefixed units; it is a
faithful factor only when `p` and `q` share a radix. -/
noncomputable def realFactor (p q : PrefixedUnit) : ℝ := (p.radix : ℝ) ^ (p.shift q)

/-- The §1.22 factor is **structurally nonzero** — a power of the radix — so
invertibility needs only `radix ≠ 0` (free for `10` and `2`), no chosen-reference
side condition. -/
theorem realFactor_ne_zero {p : PrefixedUnit} (hr : p.radix ≠ 0) (q : PrefixedUnit) :
    p.realFactor q ≠ 0 :=
  zpow_ne_zero _ (Nat.cast_ne_zero.mpr hr)

/-- **§1.22 — convert a real magnitude `x` from `p`-units to `q`-units** by
multiplying by the power-of-radix conversion factor. -/
noncomputable def convertReal (p q : PrefixedUnit) (x : ℝ) : ℝ := x * p.realFactor q

/-- Converting a real magnitude within one unit is the identity (`radix ^ 0 = 1`). -/
@[simp] theorem convertReal_self (p : PrefixedUnit) (x : ℝ) : p.convertReal p x = x := by
  have hs : p.shift p = 0 := by simp only [shift]; omega
  simp only [convertReal, realFactor, hs, zpow_zero, mul_one]

/-- **Unit conversion is a faithful round-trip over ℝ.** For two units of the *same
radix*, converting a real magnitude from `p`-units to `q`-units and back multiplies by
`radix ^ (shift p q)` then `radix ^ (shift q p)`; the exponents sum to zero
(`shift_add_symm`), so the product is `radix ⁰ = 1` and the value returns *exactly*.
Because the factor is a power of the radix, it needs only `radix ≠ 0` — the numeric
analogue of the exact `Int`-exponent round-trip `PrefixedUnit.convertExp_roundtrip`,
and it covers SI decimal and IEC 80000-13 binary prefixes uniformly. -/
theorem convertReal_roundtrip (p q : PrefixedUnit) (hpq : p.SameRadix q) (hr : p.radix ≠ 0)
    (x : ℝ) : q.convertReal p (p.convertReal q x) = x := by
  have hpq' : p.radix = q.radix := hpq
  have hr' : (p.radix : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  simp only [convertReal, realFactor, mul_assoc]
  rw [← hpq', ← zpow_add₀ hr', shift_add_symm, zpow_zero, mul_one]

end PropertyKindCalculus.PrefixedUnit
