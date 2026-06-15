/-
# Worked examples — scale-spanning units (requirement R13)

The third unit category of Finkelstein & Whitehead (Eur. J. Phys. 46 (2025) 035701),
exercised on the candela, mole, kelvin, and — for contrast — the ampere:

1. the candela and the mole are **mechanically reducible** (to power and to one), so the
   dimension layer can see they are not dimensionally independent;
2. the kelvin's scale-spanning character is **invisible to the dimension layer** (PhysLib
   keeps `Θ` independent), so scale-spanning is *not* a function of dimension;
3. the ampere is genuinely **dimensionally independent** — a physical base unit, not
   scale-spanning;
4. the R13 capstone: the base/derived dichotomy is insufficient.

These exercise `PropertyKindCalculus.ScaleSpanning` (the `Dimension`-library module).
-/

import PropertyKindCalculus.ScaleSpanning

namespace PropertyKindCalculus.Examples.ScaleSpanning

open PropertyKindCalculus
open PropertyKindCalculus.ScaleSpanning

/-! ## (1) The candela and the mole are mechanically reducible

The dimension layer *can* detect that luminous intensity (power) and amount of substance
(one) are dimensionally dependent on the physical base. -/

example : Dimension.MechanicallyReducible candela.reducesTo := candela_reduction_reducible
example : Dimension.MechanicallyReducible mole.reducesTo := mole_reduction_reducible
-- the candela reduces specifically to power; the mole to dimension one.
example : candela.reducesTo = Dim.power := rfl
example : mole.reducesTo = 1 := rfl

-- the human-selected coefficients are carried as citation locators.
#guard candela.coefficient == "K_cd"
#guard candela.coefficientValue == "683 lm/W"
#guard mole.coefficient == "N_A"
#guard kelvin.coefficient == "k_B"

/-! ## (2) The kelvin's scale-spanning character is invisible to the dimension layer

Its *proposed* reduction (energy, via `k_B`) is mechanically reducible, yet the
dimension this library assigns thermodynamic temperature (`Θ`) is *not* — so no
dimensional analysis reveals the kelvin to be scale-spanning. -/

example : Dimension.MechanicallyReducible kelvin.reducesTo
    ∧ ¬ Dimension.MechanicallyReducible Dim.temperature :=
  kelvin_reduction_invisible_to_dimension

/-! ## (3) The ampere is a physical base unit, not scale-spanning

Electric current carries the electromagnetic generator, so it is genuinely dimensionally
independent — the contrast that makes the third category distinct from the first. -/

example : ¬ Dimension.MechanicallyReducible Dim.current := ampere_is_physicalBase

/-! ## (4) R13 — scale-spanning is a third category, not a function of dimension

Two scale-spanning units (the candela, reducible; the kelvin, irreducible in this
library's algebra) disagree on mechanical reducibility, so one cannot decide
scale-spanning membership from the dimension. -/

example : ∃ a b : ScaleSpanningUnit,
    Dimension.MechanicallyReducible a.reducesTo
      ∧ ¬ Dimension.MechanicallyReducible Dim.temperature
      ∧ b.unit = kelvin.unit :=
  scaleSpanning_not_determined_by_dimension

-- every scale-spanning unit is, by construction, of the `scaleSpanning` category.
#guard candela.category == UnitCategory.scaleSpanning
#guard mole.category == UnitCategory.scaleSpanning
#guard kelvin.category == UnitCategory.scaleSpanning

end PropertyKindCalculus.Examples.ScaleSpanning
