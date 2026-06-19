/-
# Worked examples — ISO 80000-4 (Mechanics)

Part-4 examples, mirroring the `Iso80000` library's own `Iso80000/Part4` layout:

1. the dimensional algebra and unit facts (mass is `M`, force is `M·L·T⁻²`, energy is
   `M·L²·T⁻²`; the kilogram well-formed; commensurability "of the same kind");
2. **ISO 80000-2 §18** — a *vector* quantity (force, item 4-9.1) as a numerical array
   × **one scalar unit**, using §18's own force example `(−31.5, 43.2, 17.0) N`, with
   the additivity laws transferring to the vector carrier by the *same* parametric
   proof used for scalars;
3. **the force family as a specialization lattice (R2)** — weight, the friction
   forces, drag, … as force species individuated **by measurement principle**;
   static and kinetic friction forces comparable yet distinct;
4. **dimension collisions** — same dimension, distinct kind: torque vs energy
   (N·m vs J, the textbook case), momentum vs impulse, and the dimension-one family;
5. **cross-part defining relations** — momentum = mass × velocity and pressure =
   force / area compose Part-4 kinds out of Part-3 kinds; efficiency is dimensionless
   because it is a ratio of two powers;
6. **catalogue coverage** — all 54 items carry their source as data.

Series-wide catalogue examples are in the sibling
`PropertyKindCalculus.DimensionExamples.Iso80000.References`.
-/

import PropertyKindCalculus.Iso80000
import PropertyKindCalculus.QuantityReal
import PropertyKindCalculus.QuantityVector
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

namespace PropertyKindCalculus.Examples.Iso80000.Part4

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open PropertyKindCalculus.Iso80000.Part4
open PropertyKindCalculus.Iso80000.Part4.DefiningRelations

-- force is ratio-scale, hence a `DifferenceKind` — the comparability witness
-- `Quantity.add` requires, threaded explicitly into the additivity examples.
private def hForce : DifferenceKind force.kind := .ofScale

/-! ## (1) ISO 80000-4 — Mechanics (the dimensional algebra and units) -/

-- the dimensional algebra is a checked computation, not an annotation
example : mass.dim = Dim.mass := mass_dim
example : force.dim.time = -2 := force_dim_time
example : mechanicalEnergy.dim.length = 2 := energy_dim_length
example : pressure.dim.length = -1 := pressure_dim_length
example : power.dim.time = -3 := power_dim_time

-- each kind carries its exact item citation as data
#guard massCK.item == "4-1"
#guard forceCK.item == "4-9.1"
#guard forceCK.cite == "ISO 80000-4, Second edition, 2019-08 item 4-9.1"
#guard torqueCK.item == "4-12.2"

-- the kilogram is a well-formed unit; commensurability is "of the same kind"
example : kilogram.WellFormed := kilogram_wellFormed
example : newton.WellFormed := newton_wellFormed
example : ¬ kilogram.Commensurable newton := kilogram_newton_not_commensurable

/-! ## (2) ISO 80000-2 §18 — a vector quantity as numerical array × scalar unit

§18's own example is a force, `(Fₓ, F_y, F_z) = (−31.5, 43.2, 17.0) N` — one unit `N`
for the whole vector, not three separate `(number × unit)` coordinate values. -/

/-- The §18 force as a single kind-`force` quantity whose magnitude is a *numerical*
3-vector. -/
noncomputable def f : Quantity force.kind (Fin 3 → ℝ) := ⟨![-31.5, 43.2, 17.0]⟩

/-- The unit of a vector quantity is a single **scalar** of its kind (one newton for
the whole vector), and it is well-formed. -/
def forceNewton : MetrologicalUnit := force.kind.unit "N"
example : forceNewton.WellFormed := KindOfProperty.rational_bears_unit rfl

-- the additivity laws hold over the vector carrier `Fin 3 → ℝ` by the SAME parametric
-- proof used for scalars (adding forces is componentwise)
example (x y : Quantity force.kind (Fin 3 → ℝ)) :
    Quantity.add hForce x y = Quantity.add hForce y x :=
  Quantity.add_comm hForce x y

example (x y z : Quantity force.kind (Fin 3 → ℝ)) :
    Quantity.add hForce x y = Quantity.add hForce y x
      ∧ Quantity.add hForce (Quantity.add hForce x y) z
          = Quantity.add hForce x (Quantity.add hForce y z)
      ∧ Quantity.add hForce Quantity.zero x = x ∧ Quantity.add hForce x Quantity.zero = x :=
  Quantity.laws_parametric hForce x y z

/-- An `Int`-valued force, for an executable witness: componentwise addition computes
(the first component `4 + 4 = 8`). -/
def fInt : Quantity force.kind (Fin 3 → Int) := ⟨![4, 5, 6]⟩
#guard (Quantity.add hForce fInt fInt).magnitude 0 == 8

/-! ## (3) The force family: a specialization lattice individuated by measurement
principle (requirement R2, on the real standard)

ISO 80000-4 lists weight (4-9.2), static friction force (4-9.3), kinetic friction
force (4-9.4), … as separate force items, all of dimension `M·L·T⁻²`, distinguished in
the standard only by prose. Here each is a *species* of the general force kind (4-9.1),
individuated **not by fiat but by an explicit measurement (examination) principle**. -/

-- (a) a weight specializes force.
example : Specializes Edge weight.kind force.kind := weight_specializes_force

-- (b) DISTINCTION NOT BY FIAT: static and kinetic friction forces are distinct kinds
--     *because they are examined under different conditions* (resistance before vs
--     during sliding) — proved via `distinct_of_examPrinciple`, not by `id` strings.
example : staticFrictionForce.kind ≠ kineticFrictionForce.kind :=
  staticFriction_ne_kineticFriction

-- the link from the kind back to its measurement principle is checked, too.
example : weight.kind.examinedBy ForcePrinciple.gravitational := weight_examinedBy

-- (c) COMPARABILITY PRESERVED: though distinct, weight and the drag force remain
--     mutually comparable — they share the super-kind force.
example : MutuallyComparable Edge weight.kind dragForce.kind := weight_dragForce_comparable

-- (d) and the dimension cannot tell them apart: same dimension `M·L·T⁻²`, distinct kinds.
example : weight.dim = dragForce.dim := rfl

/-! ## (4) Dimension collisions: same dimension, distinct kind

The {dimension functor} identifies these pairs; the kind layer keeps them apart —
including their units. -/

-- torque and energy: both `M·L²·T⁻²`, distinct kinds, distinct units (N·m vs J).
-- The textbook case that a dimension does not determine a unit.
example : torque.dim = mechanicalEnergy.dim := torque_dim_eq_energy_dim
example : torque.kind ≠ mechanicalEnergy.kind := torque_ne_energy
example : ¬ newtonMetre.Commensurable joule := newtonMetre_joule_not_commensurable

-- momentum and impulse: both `M·L·T⁻¹`, distinct kinds (kg·m/s vs N·s).
example : momentum.dim = impulse.dim := momentum_dim_eq_impulse_dim
example : momentum.kind ≠ impulse.kind := momentum_ne_impulse

-- the torque/energy collision and the dimension-1 collision, on standard quantities.
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  iso80000_4_dim_collision
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  iso80000_4_dim_one_collision

/-! ## (5) Cross-part defining relations: mechanics built from space and time

Momentum is mass × velocity and pressure is force / area — each composing a Part-4
kind out of Part-3 (space-and-time) kinds; efficiency is dimensionless because it is a
ratio of two powers. -/

-- DIM FROM RELATION (cross-part): momentum's `M·L·T⁻¹` follows from mass × velocity.
example : momentum.dim = mass.dim * Part3.velocity.dim := momentum_dim_from_mass_velocity
-- and pressure's force/area, mass density's mass/volume (both crossing to Part 3).
example : massDensity.dim = mass.dim / Part3.volume.dim := massDensity_dim_from_mass_volume

-- ALGEBRAIC REMARK (item 4-29): efficiency is dimension one *because* it is a ratio of
-- two powers (`η = P_out/P_in`) — the dimensionlessness is computed from the relation,
-- the mechanics analogue of a plane angle being a ratio of two lengths.
example : efficiency.dim = power.dim / power.dim := efficiency_dim_from_power_ratio

-- VERIFIED CONSTRUCTION (item 4-8): a momentum built as mass × velocity carries its
-- classification certificate by construction, over `ℝ`.
example (m : Quantity mass.kind ℝ) (v : Quantity Part3.velocity.kind ℝ) :
    (momentumOf m v).IsProduct momentum_prod_mass_velocity m v :=
  momentumOf_isProduct m v

-- the product kind-law instantiates at a *different* carrier (`Int`), where the
-- construction also computes: `2 kg × 3 m/s = 6 kg·m/s` (cross-part, at `Int`).
def momentumInt : Quantity momentum.kind Int :=
  Quantity.mul momentum_prod_mass_velocity
    (⟨2⟩ : Quantity mass.kind Int) (⟨3⟩ : Quantity Part3.velocity.kind Int)
#guard momentumInt.magnitude == 6

/-! ## (6) Catalogue coverage — all 54 items carry their source as data -/

-- every ISO 80000-4 item is catalogued, in item order …
#guard PropertyKindCalculus.Iso80000.Part4.catalogue.length == 54
-- … with the item designations …
#guard forceCK.item == "4-9.1"
#guard mechanicalEnergyCK.item == "4-28.3"
#guard actionCK.item == "4-32"
-- … each citing its full source …
#guard forceCK.cite == "ISO 80000-4, Second edition, 2019-08 item 4-9.1"
-- … and recording its coherent SI unit symbol as a locator.
#guard pressureCK.coherentUnit == "Pa"
#guard torqueCK.coherentUnit == "N·m"
#guard mechanicalEnergyCK.coherentUnit == "J"

end PropertyKindCalculus.Examples.Iso80000.Part4
