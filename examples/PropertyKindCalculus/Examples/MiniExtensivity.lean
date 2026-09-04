/-
# Worked example: extensive aggregation and its failure (Dybkær §13.5)

Demonstrates, as *checked* facts, the theses of the extensivity layer:

  1. **Mass is extensive.** A measurement that sums over parts satisfies the
     `Extensive` law, so the extensive-aggregation capstone applies: the mass of a
     three-part assembly equals the sum of its parts' masses (3 + 5 + 7 = 15).
  2. **Volume on mixing is not.** 50 mL of water and 50 mL of ethanol mix to ≈ 96 mL,
     strictly less than 100 mL — `volume` is sub-additive on that decomposition, so
     it is *not* extensive, and assuming additivity would be unsound.
  3. **Density is intensive.** Parcels of one homogeneous fluid compose to a parcel of
     the same density — 1000 kg/m³, not 2000 — so the intensive capstone applies and
     the extensive one is refuted by the same measurement.
  4. **A normal-mode frequency is neither.** Two oscillators at 10 rad/s couple into a
     pair whose upper mode is at 14 rad/s: not their sum, not their shared value, and
     not produced from them at all.

Like the other minis, this module is part of the separate `Examples` library and
imports only the Mathlib-free core.
-/

import PropertyKindCalculus.Extensivity

namespace PropertyKindCalculus.Examples.MiniExtensivity

open PropertyKindCalculus

/-! ## Mass is extensive -/

/-- Mass, a ratio kind. -/
def mass : KindOfProperty := { id := "mass", scale := .ratio }

/-- An additive mass measurement built from a per-atom mass `w`: a leaf reads its
own mass, a union reads the sum of its parts. -/
def massMeasure (w : System → Int) : Measurement System
  | .atom s => { kind := mass, numeral := w s, reference := "kg" }
  | .union a b =>
      { kind := mass,
        numeral := (massMeasure w a).numeral + (massMeasure w b).numeral,
        reference := "kg" }

/-- Mass is extensive for any per-atom assignment: every part is of kind `mass`,
and the union value is the sum of the parts' values by construction. -/
theorem mass_extensive (w : System → Int) : Extensive mass (massMeasure w) :=
  ⟨fun d => by cases d <;> rfl, fun _ _ => rfl⟩

/-- Three rock samples (A, B, C) with masses 3, 5, 7. -/
def sampleMass : System → Int := fun s =>
  if s.id = "A" then 3 else if s.id = "B" then 5 else if s.id = "C" then 7 else 0

/-- The assembly: A together with (B together with C). -/
def assembly : Decomposition System :=
  .union (.atom ⟨"A"⟩) (.union (.atom ⟨"B"⟩) (.atom ⟨"C"⟩))

-- The mass of the whole assembly is read directly as 15 …
example : (massMeasure sampleMass assembly).numeral = 15 := by decide

-- … and the sum over the atomic parts is the same 15 …
example : leafSum (massMeasure sampleMass) assembly = 15 := by decide

-- … and these two agree *as a law*, by the extensive-aggregation capstone — no
-- arithmetic, for any masses, to any depth.
example :
    (massMeasure sampleMass assembly).numeral
      = leafSum (massMeasure sampleMass) assembly :=
  extensive_additive (mass_extensive sampleMass) assembly

/-! ## Volume on mixing is not extensive -/

-- The mixture is strictly sub-additive (96 < 100) and `volume` is not extensive.
example :
    (volMix mixture).numeral
        < (volMix waterPart).numeral + (volMix ethanolPart).numeral
      ∧ ¬ Extensive volume volMix :=
  mixing_subadditive

-- The measured volumes spelled out: 50, 50, and 96 for the mixture.
example : (volMix waterPart).numeral = 50 := by decide
example : (volMix ethanolPart).numeral = 50 := by decide
example : (volMix mixture).numeral = 96 := by decide

-- The mixture value (96) is *not* the leaf sum (100): the gap that makes volume
-- non-extensive, which the capstone would wrongly assert if `volume` were assumed
-- extensive.
example : (volMix mixture).numeral ≠ leafSum volMix mixture := by decide

/-! ## Density is intensive — which is not "extensive, but weaker"

Two parcels of the same water compose to water of the same density. The intensive capstone
says that for any carving, to any depth, given only that the leaves agree; the *same*
measurement refutes additivity, which is what makes §13.5.1 and §13.5.4 a division rather
than a ladder. -/

-- The two parcels and their composition all read 1000 kg/m³ …
example : (densityHomogeneous waterParcelA).numeral = 1000 := by decide
example : (densityHomogeneous (.union waterParcelA waterParcelB)).numeral = 1000 := by decide

-- … and that reading of the whole is the capstone's, not arithmetic's: the leaves agree,
-- so the whole reads what they read.
example : (densityHomogeneous (.union waterParcelA waterParcelB)).numeral = 1000 :=
  intensive_uniform densityHomogeneous_intensive _ ⟨rfl, rfl⟩

-- The leaf sum, by contrast, is 2000 — a number no parcel of water has.
example : leafSum densityHomogeneous (.union waterParcelA waterParcelB) = 2000 := by decide

-- So density is not extensive, and the two branches exclude each other here.
example : ¬ Extensive fluidDensity densityHomogeneous := density_not_extensive

/-! ## A normal-mode frequency is whole-proper — neither law applies

Two oscillators at ω₀ = 10 rad/s, coupled; the pair's upper mode is at ω₊ = 14 rad/s. That
is not 10 + 10 and it is not 10, and no third aggregation would help: a lone oscillator has
no normal mode to contribute. The pair's frequency is a quantity *of the pair*. -/

example : (normalModeFreq oscillatorA).numeral = 10 := by decide
example : (normalModeFreq (.union oscillatorA oscillatorB)).numeral = 14 := by decide

-- Summing would report 20 rad/s for a mode at 14 …
example : leafSum normalModeFreq (.union oscillatorA oscillatorB) = 20 := by decide

-- … so neither law holds of it, and both refutations are the witness's own.
example : ¬ Extensive oscillatorFrequency normalModeFreq := normalMode_wholeProper.not_extensive
example : ¬ Intensive oscillatorFrequency normalModeFreq := normalMode_wholeProper.not_intensive

end PropertyKindCalculus.Examples.MiniExtensivity
