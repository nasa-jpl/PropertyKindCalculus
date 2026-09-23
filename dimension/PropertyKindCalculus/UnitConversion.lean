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
round-trip `convertReal (convertReal x) = x` follows from `zpow_add₀` alone. The generic
*chosen-reference* unit this note once called "planned" now exists **upstream**, as the
contributed unit twin of the basis-parametric dimension (`Physlib.Units.ParametricUnits`,
the same contribution line as `Dimension B` itself): `UnitScale B` carries a positive-real
reference per base dimension — the arbitrary nonzeroness the plan said such a unit "would
have to carry and discharge" is its `scale_pos` field — and `UnitScale.dimScale` is the
generic conversion-factor homomorphism. The final section exhibits §1.22 as its
single-generator instance. Lives in the `Dimension` library because `ℝ` needs Mathlib,
the one dependency kept out of the core.
-/

module

public import PropertyKindCalculus.UnitPrefix
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Physlib.Units.ParametricUnits
-- Private scope only: the checks below reduce through bodies sealed in the core
-- library; `import all` gives this file the reduction without exposing them.
import all PropertyKindCalculus.UnitPrefix

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

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

/-! ## §1.22 as an instance of the contributed generic unit twin (`UnitScale`)

The basis-parametric `Dimension B` has its *unit* twin upstream in PhysLib
(`Physlib.Units.ParametricUnits`, the same contribution line as the parametric dimension):
`UnitScale B` chooses a positive-real unit magnitude per base dimension, and
`UnitScale.dimScale u₁ u₂ : Dimension B →* ℝ≥0` is the generic conversion-factor
homomorphism `d ↦ ∏ b, (u₁ b / u₂ b) ^ d.exponent b`, with the round-trip carried by the
upstream cocycle (`UnitScale.dimScale_transitive` + `dimScale_self`).

The bridge below exhibits the §1.22 prefix conversion as the **single-generator instance**:
a prefixed unit induces the unit choice that scales one designated base dimension by its
prefix factor `radix ^ exponent` and leaves every other base dimension at the reference `1`;
`dimScale` of two such choices, at the generator dimension, *is* `realFactor`. The prefix
case stays special exactly as the header says — its factor is structurally a power of the
radix, so nonzeroness is free — while the generic case pays for its generality with the
`scale_pos` obligation the structure carries. -/

open scoped NNReal in
/-- The unit choice a prefixed unit induces over a basis `B`: at the designated base
dimension `b₀` the chosen unit is the prefix factor `radix ^ exponent`; every other base
dimension keeps the reference unit `1`. -/
noncomputable def toUnitScale {B : Type} [DimensionBasis B] [DecidableEq B] (p : PrefixedUnit) (b₀ : B)
    (hr : 0 < p.radix) : UnitScale B where
  scale b := if b = b₀ then (p.radix : ℝ≥0) ^ p.exponent else 1
  scale_pos b := by
    split
    · exact pos_iff_ne_zero.mpr
        (zpow_ne_zero _ (by exact_mod_cast hr.ne' : (p.radix : ℝ≥0) ≠ 0))
    · exact one_pos

/-- **§1.22 is `dimScale` at a generator.** For two prefixed units of the same radix, the
generic conversion factor of their induced unit choices, evaluated at the designated base
dimension `single b₀`, is exactly the §1.22 factor `radix ^ shift` — the prefix conversion
of `convertReal` is the single-generator instance of the contributed `UnitScale.dimScale`. -/
theorem dimScale_toUnitScale_single {B : Type} [DimensionBasis B] [Fintype B] [DecidableEq B]
    (p q : PrefixedUnit) (hpq : p.SameRadix q) (hr : 0 < p.radix) (b₀ : B) :
    ((p.toUnitScale b₀ hr).dimScale (q.toUnitScale b₀ (hpq ▸ hr))
        (Dimension.single b₀) : ℝ) = p.realFactor q := by
  have hq : q.radix = p.radix := hpq.symm
  simp only [UnitScale.dimScale, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Finset.prod_eq_single b₀
    (fun b _ hb => by simp [toUnitScale, hb, Dimension.single_exponent])
    (fun hb => absurd (Finset.mem_univ b₀) hb)]
  simp only [toUnitScale, Dimension.single_exponent, hq]
  push_cast
  rw [← zpow_sub₀ (Nat.cast_ne_zero.mpr hr.ne' : (p.radix : ℝ) ≠ 0), Real.rpow_one]
  rfl

end PropertyKindCalculus.PrefixedUnit

end -- pkc-blanket-expose
end -- pkc-blanket
