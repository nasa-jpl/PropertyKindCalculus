/-
# Worked example: dedicated kinds — Soil — Water ; volume fraction

Dybkær Ch. 20. A *dedicated* kind binds a generic kind-of-property to the **sort
of system** it is about — the definition's "given sort of system" — and the
pertinent component, giving the IUPAC/IFCC `System — Component ; kind-of-property`
designation. The *particular* system (this sample, that sample) is not the
catalogue's to carry: it is the object index of an `IndividualQuantity`, and §6
below shows the two layers dividing that labor.

This example shows the **principled** form of the soil-moisture distinctness:
volumetric and gravimetric water content are the *same* measurement target
(soil — water) examined as two different kinds-of-property, so they are distinct
dedicated kinds **because the kinds-of-property differ** — not because of any
hand-chosen identity string.

This module is part of the separate `Examples` library; it imports the core
`PropertyKindCalculus` library like any downstream consumer would.
-/

module

public import PropertyKindCalculus
meta import PropertyKindCalculus
-- Private scope only: the checks below reduce through bodies sealed in the core
-- library; `import all` gives this file the reduction without exposing them.
import all PropertyKindCalculus.Mereology

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Examples.Dedicated

open PropertyKindCalculus

/-- The sort of system under examination — *soil*, as against any particular sample. -/
def soil : SortOfSystem := { id := "soil" }
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

-- (1) both are dedicated to the SAME sort and the SAME component …
example : vwc.sort = gwc.sort := rfl
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
--     the air content shares the sort and the kind-of-property, differing only
--     in the component.
def air : Component := { id := "air" }
def airContent : DedicatedKind := volumeFraction.dedicatedTo soil air
example : vwc ≠ airContent := DedicatedKind.distinct_of_component (by decide)

/-! ## (6) Dedication to the sort, individuation by the object (R19)

The catalogue entry `vwc` is dedicated to the *sort* — one entry for every soil sample
there will ever be. Which sample a measured value characterizes is carried one layer
down, by `IndividualQuantity`'s object index, so a water content of one sample cannot be
combined with that of another — a compile-time type error, the object-aware refinement
of `Quantity`. -/

/-- Soil samples — particulars (objects, Dybkær Ch. 3) of the sort `soil`. -/
structure Sample where
  /-- Which sample. -/
  n : Nat
deriving DecidableEq, Repr

/-- The model's sort claim, made once: every `Sample` instantiates `soil`. -/
instance : Sorted Sample := ⟨fun _ => soil⟩

def sample1 : Sample := ⟨1⟩
def sample2 : Sample := ⟨2⟩

-- dedicating THROUGH either sample lands on the same catalogue entry: the dedicated kind
-- cannot tell the samples apart, and is not supposed to …
example : volumeFraction.dedicatedFor sample1 water
        = volumeFraction.dedicatedFor sample2 water := rfl
example : volumeFraction.dedicatedFor sample1 water = vwc := rfl

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

end -- pkc-blanket-expose
end -- pkc-blanket
