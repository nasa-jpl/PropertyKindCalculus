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
argument beyond `R := ℝ` and the kind's comparability witness `h`. -/
example (k : KindOfProperty) (h : DifferenceKind k) (x y : Quantity k ℝ) :
    Quantity.add h x y = Quantity.add h y x :=
  Quantity.add_comm h x y

/-- The whole additivity package at `ℝ`, straight from the parametric proof. -/
example (k : KindOfProperty) (h : DifferenceKind k) (x y z : Quantity k ℝ) :
    Quantity.add h x y = Quantity.add h y x
      ∧ Quantity.add h (Quantity.add h x y) z = Quantity.add h x (Quantity.add h y z)
      ∧ Quantity.add h Quantity.zero x = x ∧ Quantity.add h x Quantity.zero = x :=
  Quantity.laws_parametric h x y z

/-- A concrete real-valued length: `1 m + 2 m` measures `3 m`, gated to the
`length` kind (ratio scale, so it is a `DifferenceKind`). -/
example :
    (Quantity.add (DifferenceKind.ofScale)
        (⟨1⟩ : Quantity { id := "length", scale := .ratio } ℝ) ⟨2⟩).magnitude
      = 3 := by
  show (1 : ℝ) + 2 = 3
  norm_num

end PropertyKindCalculus.Examples.QuantityReal
