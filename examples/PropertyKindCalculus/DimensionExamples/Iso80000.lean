/-
# Worked examples — the ISO/IEC 80000 catalogue and the §18 vector quantity

Three things, as checked facts:

1. **The references catalogue** renders citations by name and version, e.g.
   `IEC 80000-6, Edition 2.0, 2022-11` — no normative content, just the citable
   identity of each licensed part.
2. **The ISO 80000-3 seed** (Space and time): the dimensional algebra is checked
   (length is `L`, area is `L²`, speed is `L·T⁻¹`), the metre is a well-formed
   metrological unit, the metre and centimetre are commensurable while the metre
   and the second are not, and each kind carries its exact item citation as data.
3. **ISO 80000-2 §18** — a *vector* quantity is a numerical array multiplied by
   **one scalar unit**, not a per-coordinate collection of `(number × unit)`
   values; "all units are scalars"; the quantity is coordinate-independent while
   its numerical components are not. Here a displacement is a `Quantity` whose
   carrier is a numerical 3-vector, with a single scalar unit (the metre), and the
   additivity laws transfer to the vector carrier by the *same* parametric proof
   used for scalars. This is the carrier-parametric (R10) reading of §18, and it
   contrasts representation-rooted models that attach a unit to each coordinate
   value (the reading §18 advises against — the contrast this work draws with
   SysML v2).

These live in the Mathlib-backed `DimensionExamples` library (the quantity-kinds
carry PhysLib `Dimension`s, and the §18 example uses `ℝ`-valued components).
-/

import PropertyKindCalculus.Iso80000
import PropertyKindCalculus.QuantityReal
import Mathlib.Data.Fin.VecNotation

namespace PropertyKindCalculus.Examples.Iso80000

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open PropertyKindCalculus.Iso80000.Part3

/-! ## (1) The references catalogue (citation metadata only) -/

-- citations render in the conventional `body number-part, edition, date` form
#guard iec80000_6.cite == "IEC 80000-6, Edition 2.0, 2022-11"
#guard iso80000_3.cite == "ISO 80000-3, Second edition, 2019-10"
#guard iso80000_3.designation == "ISO 80000-3"
-- all twelve licensed parts are catalogued …
#guard catalogue.length == 12
-- … and part 6 (Electromagnetism) is the IEC-published one.
example : iec80000_6.body = StandardBody.IEC := rfl

/-! ## (2) ISO 80000-3 — Space and time (the seed) -/

-- the dimensional algebra is a checked computation, not an annotation
example : length.dim = Dim.length := length_dim
example : area.dim.length = 2 := area_dim_length
example : speed.dim = Dim.length / Dim.time := speed_dim

-- each kind carries its exact item citation as data
#guard lengthCK.item == "3-1.1"
#guard lengthCK.cite == "ISO 80000-3, Second edition, 2019-10 item 3-1.1"
#guard speedCK.item == "3-10.2"

-- the metre is a well-formed unit; commensurability is "of the same kind"
example : metre.WellFormed := metre_wellFormed
example : metre.Commensurable centimetre := metre_centimetre_commensurable
example : ¬ metre.Commensurable second := metre_second_not_commensurable

/-! ## (3) ISO 80000-2 §18 — a vector quantity as numerical array × scalar unit

A displacement (ISO 80000-3 item 3-1.11). §18's own example is a force,
`(Fₓ, F_y, F_z) = (−31.5, 43.2, 17.0) N` — one unit `N` for the whole vector. -/

/-- The displacement as a single kind-`displacement` quantity whose magnitude is a
*numerical* 3-vector — not three separate `(number × unit)` coordinate values. -/
noncomputable def d : Quantity displacement.kind (Fin 3 → ℝ) := ⟨![3.0, 4.0, 0.0]⟩

/-- The unit of a vector quantity is a single **scalar** of its kind (one metre for
the whole vector), and it is well-formed. -/
def displacementMetre : MetrologicalUnit := displacement.kind.unit "m"
example : displacementMetre.WellFormed := KindOfProperty.rational_bears_unit rfl

-- the additivity laws hold over the vector carrier `Fin 3 → ℝ` by the SAME
-- parametric proof used for scalars (adding displacements is componentwise)
example (x y : Quantity displacement.kind (Fin 3 → ℝ)) :
    Quantity.add x y = Quantity.add y x :=
  Quantity.add_comm x y

example (x y z : Quantity displacement.kind (Fin 3 → ℝ)) :
    Quantity.add x y = Quantity.add y x
      ∧ Quantity.add (Quantity.add x y) z = Quantity.add x (Quantity.add y z)
      ∧ Quantity.add Quantity.zero x = x ∧ Quantity.add x Quantity.zero = x :=
  Quantity.laws_parametric x y z

/-- An `Int`-valued displacement, for an executable witness: componentwise addition
computes (the middle component `5 + 5 = 10`). -/
def vInt : Quantity displacement.kind (Fin 3 → Int) := ⟨![4, 5, 6]⟩
#guard (Quantity.add vInt vInt).magnitude 1 == 10

end PropertyKindCalculus.Examples.Iso80000
