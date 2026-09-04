/-
# Validation probes — the real-valued unit (R17)

A round-trip law is the easiest kind of theorem to prove about a definition that does nothing,
so the probe measures a real quantity in two *different* units of one kind and checks that the
numbers differ: 2 metres reads 2 in metres and 200 in centimetres, with the conversion factor
100 read off the ratio of the references. Only then are the round-trips applied.

The boundary is the license: `RealUnit` admits no reference of magnitude zero, and its
well-formedness is the symbolic layer's — a nominal kind bears no unit here either.
-/

import PropertyKindCalculus.UnitReal

namespace PropertyKindCalculus.Tests.UnitReal

open PropertyKindCalculus

/-- Length, a ratio kind. -/
def lengthK : KindOfProperty := { id := "length", scale := .ratio }

/-- Colour, a nominal kind — no magnitude, so no unit. -/
def colourK : KindOfProperty := { id := "colour", scale := .nominal }

/-- The metre: the reference of magnitude 1. -/
noncomputable def metre : RealUnit lengthK := ⟨⟨1⟩, one_ne_zero⟩

/-- The centimetre: the reference of magnitude 1/100 — a different unit of the same kind. -/
noncomputable def centimetre : RealUnit lengthK := ⟨⟨1 / 100⟩, by norm_num⟩

/-- Two metres, as a quantity. -/
noncomputable def twoMetres : Quantity lengthK ℝ := ⟨2⟩

-- Boundary — the unit is load-bearing: one quantity, two units, two numbers.
theorem r17_measure_metre : RealUnit.measure twoMetres metre = 2 := by
  norm_num [RealUnit.measure, metre, twoMetres]

theorem r17_measure_centimetre : RealUnit.measure twoMetres centimetre = 200 := by
  norm_num [RealUnit.measure, centimetre, twoMetres]

-- … and the factor between them is the ratio of the references.
theorem r17_ratio : metre.ratio centimetre = 100 := by
  norm_num [RealUnit.ratio, metre, centimetre]

-- Inhabitation: both round-trips, at a real unit and a real quantity.
theorem r17_ofNumber_measure : metre.ofNumber (RealUnit.measure twoMetres metre) = twoMetres :=
  metre.ofNumber_measure twoMetres

theorem r17_measure_ofNumber (n : ℝ) : RealUnit.measure (centimetre.ofNumber n) centimetre = n :=
  centimetre.measure_ofNumber n

-- Inhabitation: conversion is faithful for an arbitrary chosen reference, not only for a power
-- of ten — the two factors between metre and centimetre are reciprocal.
theorem r17_ratio_roundtrip : metre.ratio centimetre * centimetre.ratio metre = 1 :=
  metre.ratio_mul_ratio_symm centimetre

-- Boundary — the refinement inherits the §9.13.4 exclusion: a nominal kind bears no unit here
-- either, so a `RealUnit colourK` cannot be well-formed.
theorem r17_nominal_not_wellFormed (u : RealUnit colourK) : ¬ u.WellFormed :=
  RealUnit.not_wellFormed_of_nominal rfl

/-- info: 'PropertyKindCalculus.RealUnit.measure_ofNumber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RealUnit.measure_ofNumber

/-- info: 'PropertyKindCalculus.RealUnit.ofNumber_measure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RealUnit.ofNumber_measure

/-- info: 'PropertyKindCalculus.RealUnit.ratio_mul_ratio_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RealUnit.ratio_mul_ratio_symm

/-- info: 'PropertyKindCalculus.RealUnit.measure_eq_measure_mul_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RealUnit.measure_eq_measure_mul_ratio

/-- info: 'PropertyKindCalculus.RealUnit.measure_ofNumber_eq_symbolic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RealUnit.measure_ofNumber_eq_symbolic

end PropertyKindCalculus.Tests.UnitReal
