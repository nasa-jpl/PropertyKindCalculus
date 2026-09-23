/-
# Validation probes — operation gating (R4, R6)

Inhabitation and axiom-profile probes for the *operation-gating* group: same-kind additivity
(R4) and the monotonic scale-gating of operators (R6). Each requirement theorem is applied to a
concrete witness, and — the Rule-2 *boundary* probe — the gate is shown to genuinely *exclude*
the degenerate case (a nominal kind bears no additivity; a poorer scale does not dominate a
richer one), so the premise is a real gate, not a formality.
-/

module

public import PropertyKindCalculus
meta import PropertyKindCalculus

@[expose] public section Blanket

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

/-! ## The count carrier

A count is the canonical dimension-one ratio-scale quantity, and `Nat` is what one is held in.
The probes below are what the `Carrier Nat` instance commits the library to: a counter starts
from the kind's own zero and grows by same-kind addition, so neither operation needs an
anonymous `⟨…⟩` — which is what an accumulator written over a bare `Nat` under a quantity's
name has to use for both. -/

/-- A count kind — ratio scale, so it licenses differences. -/
def tallyK : KindOfProperty := { id := "operation gating probe tally", scale := .ratio }

/-- The scale gate for `tallyK`. -/
theorem diffTally : DifferenceKind tallyK := DifferenceKind.ofScale

-- The same R4/R10 laws hold at `Nat`, so a count is not a second-class quantity: it is lawful
-- for the same reason `Int` is, and differs only in lacking an additive inverse the laws never
-- ask for.
theorem r4_laws_at_tally (x y z : Quantity tallyK Nat) :
    Quantity.add diffTally x y = Quantity.add diffTally y x
      ∧ Quantity.add diffTally (Quantity.add diffTally x y) z
          = Quantity.add diffTally x (Quantity.add diffTally y z)
      ∧ Quantity.add diffTally Quantity.zero x = x
      ∧ Quantity.add diffTally x Quantity.zero = x :=
  Quantity.laws_parametric diffTally x y z

-- The accumulator idiom, with no mint in it: start at the kind's zero, add kinded increments.
#guard ((Quantity.zero : Quantity tallyK Nat)).magnitude == 0
#guard (Quantity.add diffTally (Quantity.zero : Quantity tallyK Nat) ⟨3⟩).magnitude == 3
example : (Quantity.add diffTally (⟨2⟩ : Quantity tallyK Nat) ⟨5⟩).magnitude = 7 := rfl

-- The zero is the *kind's* zero, so it cannot be handed to a neighbouring count: what the
-- instance supplies is a magnitude, and the kind index still separates two tallies.
#check_failure (Quantity.add diffLength (Quantity.zero : Quantity tallyK Nat) (⟨1⟩ : Quantity lengthK Int))

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

end Blanket
