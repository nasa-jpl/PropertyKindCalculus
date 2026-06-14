/-
# Worked examples — the `ℝ` quantity carrier (R10)

Checked facts exercising `Quantity k ℝ`: the additivity laws, proved once over any
lawful carrier in the core, transfer to the `ℝ` proof carrier with no `ℝ`-specific
argument — the R10 payoff. The `Int` and `Float` carriers are exercised in the
Mathlib-free `PropertyKindCalculus.Examples.MiniQuantity`; `ℝ` lands here because it
needs Mathlib (the `Carrier ℝ` instance lives in the `Dimension` library).
-/

import PropertyKindCalculus.QuantityReal
import Mathlib.Tactic.NormNum

namespace PropertyKindCalculus.Examples.QuantityReal

open PropertyKindCalculus

/-- Commutativity at the proof carrier — the generic `Quantity.add_comm`, with no
argument beyond `R := ℝ`. -/
example (k : KindOfProperty) (x y : Quantity k ℝ) :
    x.add y = y.add x :=
  Quantity.add_comm x y

/-- The whole additivity package at `ℝ`, straight from the parametric proof. -/
example (k : KindOfProperty) (x y z : Quantity k ℝ) :
    Quantity.add x y = Quantity.add y x
      ∧ Quantity.add (Quantity.add x y) z = Quantity.add x (Quantity.add y z)
      ∧ Quantity.add Quantity.zero x = x ∧ Quantity.add x Quantity.zero = x :=
  Quantity.laws_parametric x y z

/-- A concrete real-valued length: `1 m + 2 m` measures `3 m`, gated to the
`length` kind. -/
example :
    (Quantity.add (⟨1⟩ : Quantity { id := "length", scale := .ratio } ℝ) ⟨2⟩).magnitude
      = 3 := by
  show (1 : ℝ) + 2 = 3
  norm_num

end PropertyKindCalculus.Examples.QuantityReal
