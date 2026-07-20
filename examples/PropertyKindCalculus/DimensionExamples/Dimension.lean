/-
# Worked examples — the dimension layer

Checked facts exercising `dim` (the forgetful functor into PhysLib's
`Dimension`): the dimension-1 collapse on a soil-moisture / radiative quartet,
the dimensional algebra in the target group, and the forgetful-functor
coherence laws.

These live in the `DimensionExamples` library (not the Mathlib-free `Examples`
library), because they depend on PhysLib + Mathlib.
-/
import PropertyKindCalculus.Dimension

namespace PropertyKindCalculus.Examples.Dimension

open PropertyKindCalculus

/-! ## The four dimensionless kinds all forget to `1`

Volumetric water content, gravimetric water content, relative permittivity, and
reflectivity are physically distinct kinds that are *all* dimension one — the
exact confusions a dimension-only model cannot prevent. -/

example : vwc.toDimension = 1 := rfl
example : gwc.toDimension = 1 := rfl
example : permittivity.toDimension = 1 := rfl
example : reflectivity.toDimension = 1 := rfl

/-- They share a dimension … -/
example : vwc.toDimension = gwc.toDimension := rfl
example : permittivity.toDimension = reflectivity.toDimension := rfl

/-! ## … yet are pairwise distinct *kinds*

The kind layer is exactly the discriminator the dimension layer lacks. -/

example : vwc.kind ≠ gwc.kind := by decide
example : vwc.kind ≠ permittivity.kind := by decide
example : gwc.kind ≠ reflectivity.kind := by decide
example : permittivity.kind ≠ reflectivity.kind := by decide

/-- A dimensionful kind is distinguished even at the dimension layer: length is
not dimension one. -/
example : lengthKind.toDimension ≠ vwc.toDimension := by
  intro h
  have : (Dim.length).length = (1 : Dimension PhyslibBase).length := congrArg Dimension.length h
  simp [Dim.length] at this

/-! ## The dimensional algebra computes in the PhysLib group -/

example : Dim.area.length = 2 := Dim.area_length
example : Dim.speed = Dim.length / Dim.time := Dim.speed_eq
example : Dim.speed.length = 1 := by
  norm_num [Dim.speed, Dimension.div_length, Dimension.L𝓭_length, Dimension.T𝓭_length]
example : Dim.speed.time = -1 := by
  norm_num [Dim.speed, Dimension.div_time, Dimension.L𝓭_time, Dimension.T𝓭_time]

/-! ## Forgetful-functor coherence on a concrete product

The dimension of a product is the product of the dimensions: composing two
lengths gives an area, and `dim` carries the composition to `L²`. -/

example : (lengthKind.times lengthKind).toDimension = Dim.area := rfl
example : (lengthKind.times lengthKind).toDimension
    = lengthKind.toDimension * lengthKind.toDimension :=
  DimensionedKind.toDimension_times lengthKind lengthKind
example : (DimensionedKind.unitless (B := PhyslibBase)).toDimension = 1 :=
  DimensionedKind.toDimension_unitless

end PropertyKindCalculus.Examples.Dimension
