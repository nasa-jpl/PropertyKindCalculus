/-
# Validation probes — operation gating (R4, R6)

Inhabitation and axiom-profile probes for the *operation-gating* group: same-kind additivity
(R4) and the monotonic scale-gating of operators (R6). Each requirement theorem is applied to a
concrete witness, and — the Rule-2 *boundary* probe — the gate is shown to genuinely *exclude*
the degenerate case (a nominal kind bears no additivity; a poorer scale does not dominate a
richer one), so the premise is a real gate, not a formality.
-/

import PropertyKindCalculus

namespace PropertyKindCalculus.Tests.OperationGating

open PropertyKindCalculus

/-! ## R4 — operations are gated by kind (the additive law) -/

/-- Length, a ratio kind (so its scale licenses `+`/`−`). -/
def lengthK : KindOfProperty := { id := "length", scale := .ratio }
/-- Colour, a nominal kind (no magnitude, so no additivity). -/
def colourK : KindOfProperty := { id := "colour", scale := .nominal }

/-- The scale gate for `lengthK`: ratio allows differences, discharged by `trivial`. -/
theorem diffLength : DifferenceKind lengthK := DifferenceKind.ofScale

-- Inhabitation: the R10/R4 additivity laws applied to *concrete* length quantities over the
-- lawful carrier `Int` — the universally-quantified conjunction is instantiated at real values,
-- so it is not vacuously quantified over an empty carrier.
theorem r4_laws_at_length (x y z : Quantity lengthK Int) :
    Quantity.add diffLength x y = Quantity.add diffLength y x
      ∧ Quantity.add diffLength (Quantity.add diffLength x y) z
          = Quantity.add diffLength x (Quantity.add diffLength y z)
      ∧ Quantity.add diffLength Quantity.zero x = x
      ∧ Quantity.add diffLength x Quantity.zero = x :=
  Quantity.laws_parametric diffLength x y z

-- and it computes: 3 + 4 = 7 over the executable carrier.
example : (Quantity.add diffLength (⟨3⟩ : Quantity lengthK Int) ⟨4⟩).magnitude = 7 := rfl

-- Boundary (Rule 2): the gate genuinely *fires* on a nominal kind — `DifferenceKind colourK` is
-- uninhabited, so same-kind addition of colours cannot even be formed. A gate that admitted
-- everything would prove nothing.
theorem r4_colour_no_additivity : ¬ DifferenceKind colourK := fun h => h.allowsDifference

/-- info: 'PropertyKindCalculus.Quantity.laws_parametric' depends on axioms: [propext] -/
#guard_msgs in #print axioms Quantity.laws_parametric

/-! ## R6 — operator availability is gated by scale, monotonically -/

-- Inhabitation: `interval ≤ ratio` holds (`decide`), and `allows_mono` lifts every operator a
-- poorer scale allows into the richer one — here, that `+`/`−` (allowed at interval) is allowed
-- at ratio. Applied to the concrete order, then to a concrete `AllowsDifference` witness.
theorem r6_interval_le_ratio : ScaleType.interval ≤ ScaleType.ratio :=
  ScaleType.le_def.mpr (by decide)

theorem r6_difference_lifts :
    ScaleType.AllowsDifference ScaleType.interval → ScaleType.AllowsDifference ScaleType.ratio :=
  (ScaleType.allows_mono r6_interval_le_ratio).2.1

example : ScaleType.AllowsDifference ScaleType.ratio :=
  r6_difference_lifts (by trivial)

-- Boundary (Rule 2): the order `≤` is a real gate — a richer scale does *not* sit below a poorer
-- one, so monotonicity has nothing to say in that direction (there is no such implication to
-- misuse). A monotonicity lemma over a trivial order would be vacuous.
theorem r6_ratio_not_le_nominal : ¬ (ScaleType.ratio ≤ ScaleType.nominal) :=
  fun h => absurd (ScaleType.le_def.mp h) (by decide)

/-- info: 'PropertyKindCalculus.ScaleType.allows_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms ScaleType.allows_mono

end PropertyKindCalculus.Tests.OperationGating
