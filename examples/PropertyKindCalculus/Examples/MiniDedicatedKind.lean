/-
# Worked example: dedicated kinds — Soil — Water ; volume fraction

Dybkær Ch. 20. A *dedicated* kind binds a generic kind-of-property to the system
it characterizes and the pertinent component, giving the IUPAC/IFCC
`System — Component ; kind-of-property` designation.

This example shows the **principled** form of the soil-moisture distinctness:
volumetric and gravimetric water content are the *same* measurement target
(soil — water) examined as two different kinds-of-property, so they are distinct
dedicated kinds **because the kinds-of-property differ** — not because of any
hand-chosen identity string.

This module is part of the separate `Examples` library; it imports the core
`PropertyKindCalculus` library like any downstream consumer would.
-/

import PropertyKindCalculus

namespace PropertyKindCalculus.Examples.Dedicated

open PropertyKindCalculus

/-- The system under examination. -/
def soil : System := { id := "soil" }
/-- The pertinent component. -/
def water : Component := { id := "water" }

/-- A generic kind-of-property: a volume fraction (water volume / soil volume). -/
def volumeFraction : KindOfProperty :=
  { id := "volume fraction", scale := .ratio, examPrinciple := some "ratio of volumes" }
/-- A generic kind-of-property: a mass fraction (water mass / dry-soil mass). -/
def massFraction : KindOfProperty :=
  { id := "mass fraction", scale := .ratio, examPrinciple := some "ratio of masses" }

/-- Volumetric water content = the volume-fraction kind dedicated to Soil — Water. -/
def vwc : DedicatedKind := volumeFraction.dedicatedTo soil water
/-- Gravimetric water content = the mass-fraction kind dedicated to Soil — Water. -/
def gwc : DedicatedKind := massFraction.dedicatedTo soil water

-- (1) both are dedicated to the SAME system and the SAME component …
example : vwc.system = gwc.system := rfl
example : vwc.component = gwc.component := rfl

-- (2) … yet they are DISTINCT dedicated kinds, because the kinds-of-property differ.
example : vwc.kind ≠ gwc.kind := by decide
example : vwc ≠ gwc := DedicatedKind.distinct_of_kind (by decide)

-- (3) both are dedicated kinds-of-quantity (ratio scale ⇒ has magnitude).
example : vwc.IsQuantity := KindOfProperty.rational_isQuantity rfl

-- (4) the systematic term reads in the IUPAC/IFCC `System — Component ; kind` syntax.
#guard vwc.systematicTerm == "soil — water ; volume fraction"
#guard gwc.systematicTerm == "soil — water ; mass fraction"

-- (5) a DIFFERENT component of the same soil is a distinct dedicated kind, too:
--     the air content shares the system and the kind-of-property, differing only
--     in the component.
def air : Component := { id := "air" }
def airContent : DedicatedKind := volumeFraction.dedicatedTo soil air
example : vwc ≠ airContent := DedicatedKind.distinct_of_component (by decide)

/-! ## (6) Object identity on quantities, first-class (R19)

`DedicatedKind` distinguishes kinds by system (§5). `IndividualQuantity` carries the object in
the *quantity type* itself, so a measured water content that characterizes one soil sample
cannot be combined with that of another — a compile-time type error, the object-aware
refinement of `Quantity`. -/

/-- Two distinct soil samples (objects, Dybkær Ch. 3). -/
def sample1 : Object := { id := "sample-1" }
def sample2 : Object := { id := "sample-2" }

private theorem hVF : DifferenceKind volumeFraction := .ofScale

/-- The volumetric water content of sample-1 — an individual quantity that *characterizes*
sample-1: the object rides in the type. -/
def wc1 : IndividualQuantity sample1 volumeFraction Int := ⟨30⟩
/-- A second reading of sample-1. -/
def wc1' : IndividualQuantity sample1 volumeFraction Int := ⟨2⟩
/-- The volumetric water content of a *different* sample, sample-2. -/
def wc2 : IndividualQuantity sample2 volumeFraction Int := ⟨45⟩

-- same-object addition type-checks and computes (two readings of the *same* sample) …
#guard (IndividualQuantity.add hVF wc1 wc1').magnitude == 32

-- … but adding a reading of sample-1 to a reading of sample-2 does NOT type-check: the object is
-- in the type. Uncommenting the next line is a compile-time error (different objects) — the
-- cross-sample mix a bare numeric model would silently accept:
--   #guard (IndividualQuantity.add hVF wc1 wc2).magnitude == 75

end PropertyKindCalculus.Examples.Dedicated
