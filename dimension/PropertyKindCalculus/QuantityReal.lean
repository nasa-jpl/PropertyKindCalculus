/-
# The real-number carrier — `Quantity k ℝ`, the representation that proves (R10)

The third carrier for the representation-parametric `Quantity k R` (the `Int` and
`Float` carriers ship with the Mathlib-free core, in `PropertyKindCalculus.Quantity`).
Lean's `ℝ` — a complete ordered field — is the *specification* representation: the
continuous numbers against which the quantity laws are stated and proved. It lives
with the `Dimension` library because `ℝ` needs Mathlib, the one dependency kept out
of the core.

`ℝ` is a `LawfulCarrier`, so every `Quantity.add_*` law proved once over an
arbitrary lawful carrier holds verbatim at `R := ℝ` — no `ℝ`-specific proof. That
is the R10 payoff in one line: the kind machinery above the carrier is written
once and reused at the proof carrier exactly as it is at `Int`. (Worked examples
that exercise this transfer live in the `DimensionExamples` library.)
-/

import PropertyKindCalculus.Quantity
import Mathlib.Basic.Real.Basic

namespace PropertyKindCalculus

/-- `ℝ` is a numeric carrier (the proof representation). Noncomputable, like the
real-number operations it forwards to — it exists to *specify*, not to run. -/
noncomputable instance instCarrierReal : Carrier ℝ where
  zero := 0
  add := (· + ·)

/-- `ℝ` is a *lawful* carrier: the additive-monoid laws are exactly those of the
real field, so the representation-parametric additivity laws specialize to `ℝ`. -/
noncomputable instance : LawfulCarrier ℝ where
  toCarrier := instCarrierReal
  add_assoc := _root_.add_assoc
  add_comm := _root_.add_comm
  zero_add := _root_.zero_add
  add_zero := _root_.add_zero

/-- **`ℝ` is a *scalar* carrier**: a real magnitude is one number, and `ℝ`'s `*` is the
multiplication of magnitudes. This is what makes `Quantity.mul` available at the proof
representation — and, by its absence at `Fin n → ℝ`, what keeps the componentwise product
of two vector quantities from being signed as a product of kinds. -/
instance : ScalarCarrier ℝ := ⟨⟩

end PropertyKindCalculus
