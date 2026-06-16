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

end PropertyKindCalculus.Examples.Dedicated
