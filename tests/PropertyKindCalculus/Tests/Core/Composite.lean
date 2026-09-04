/-
# Validation probes — composite objects and licensed assembly

Inhabitation, boundary, and axiom-profile probes for `Composite`, `Assembles` and `assemble`
(`PropertyKindCalculus.Composite`), and for the object-type parameterization they rest on
(`IndividualQuantity`, `Foundations.Designated`).

The probes check the properties the module exists for:

  * the object **gate** needs nothing from the object type — it holds at an arbitrary `P`
    about which no instance whatever is available, which is the claim that lets the layer be
    applied to a host library's own objects;
  * the **whole is not a part** (MR22): the assembled quantity and a part's quantity are of
    different objects and do not combine;
  * the **license is opt-in and has content**: an unlicensed kind has no `assemble`, and a
    kind whose scale forbids differences cannot be licensed at all;
  * assembly **is** §13.5 aggregation — `assemble_eq_measured` against a real `Extensive`
    witness, on a nested decomposition so the inductive step is exercised;
  * `Designated` is **injective by obligation**, so the collapsing instance an author would
    otherwise reach for is not writable.
-/

import PropertyKindCalculus

namespace PropertyKindCalculus.Tests.Composite

open PropertyKindCalculus

/-- Mass — the archetypal assembling kind. -/
def massK : KindOfProperty := { id := "composite probe mass", scale := .ratio }
/-- A ratio kind deliberately left off the assembly registry. -/
def angVelK : KindOfProperty := { id := "composite probe angular velocity", scale := .ratio }
/-- An *ordinal* kind — the scale gate's target: no sum is meaningful, so no license exists. -/
def hardnessK : KindOfProperty := { id := "composite probe hardness", scale := .ordinal }

instance : Assembles massK := ⟨DifferenceKind.ofScale⟩

/-! ## The gate needs nothing from the object type -/

section BareObject
variable {P : Type} {p q : P}

-- Inhabitation: same object, same kind, over a type variable with no instances at all.
example (x y : IndividualQuantity p massK Int) : IndividualQuantity p massK Int :=
  IndividualQuantity.add DifferenceKind.ofScale x y

-- Boundary: two distinct objects of that same type do not combine.
#check_failure fun {P : Type} {p q : P} (x : IndividualQuantity p massK Int)
    (y : IndividualQuantity q massK Int) => IndividualQuantity.add DifferenceKind.ofScale x y

-- Boundary: an object type with no designation cannot name its individual property, which is
-- the one thing in the layer that reads the object.
#check_failure (inferInstance : Designated P)

end BareObject

/-! ## Assembly over a composite -/

/-- Four parts, indexed. -/
abbrev Part4 := Fin 4

/-- A nested decomposition of the four parts — depth 3, so the fold's recursion is exercised
rather than a single atom. -/
def four : Decomposition Part4 := Decomposition.ofParts 0 [1, 2, 3]

/-- Two kilograms per part, each characterizing its own part. -/
def partMass (c : Part4) : IndividualQuantity (Composite.part c) massK Int := ⟨2⟩

/-- The whole's mass, assembled. -/
def wholeMass : IndividualQuantity (Composite.whole (P := Part4)) massK Int :=
  assemble Composite.whole Composite.part four partMass

-- Inhabitation: four parts of two kilograms assemble to eight.
#guard wholeMass.magnitude == 8

-- Boundary (MR22): the whole's mass and a part's mass are quantities of different objects.
#check_failure IndividualQuantity.add (k := massK) DifferenceKind.ofScale wholeMass (partMass 0)

-- Boundary: the license is opt-in — `angVelK` is a ratio kind, so nothing about its *scale*
-- stops the sum; what stops it is that no one registered it as assembling.
#check_failure fun (f : (c : Part4) → IndividualQuantity (Composite.part c) angVelK Int) =>
  assemble (k := angVelK) Composite.whole Composite.part four f

-- Boundary: the license has content — an ordinal kind cannot be licensed at all, because
-- `Assembles` carries the same scale gate `add` demands.
#check_failure (⟨DifferenceKind.ofScale⟩ : Assembles hardnessK)

/-! ## Assembly is §13.5 aggregation -/

/-- The number of atomic parts under a decomposition — a genuinely additive reading. -/
def countLeaves : Decomposition Part4 → Int
  | .atom _ => 1
  | .union a b => countLeaves a + countLeaves b

/-- A mass measurement that is additive by construction, so the `Extensive` witness is real. -/
def leafMass : Measurement Part4 :=
  fun d => { kind := massK, numeral := countLeaves d, reference := "kg" }

/-- `leafMass` is extensive for `massK` — both fields by `rfl`. -/
theorem leafMass_extensive : Extensive massK leafMass := ⟨fun _ => rfl, fun _ _ => rfl⟩

-- Inhabitation of the bridge: the assembled magnitude *is* the value the measurement reports
-- for the whole, on the nested decomposition — the license cashed against a real witness.
theorem assembled_is_measured :
    (assemble (k := massK) (Composite.whole (P := Part4)) Composite.part four
      (fun p => ⟨(leafMass (.atom p)).numeral⟩)).magnitude = (leafMass four).numeral :=
  assemble_eq_measured _ _ leafMass_extensive four

#guard (leafMass four).numeral == 4

/-! ## Designation is an obligation, not a formality -/

/-- Two named systems, to have something a collapsing designation would confuse. -/
def sysA : Object := ⟨"probe system A"⟩
/-- The second. -/
def sysB : Object := ⟨"probe system B"⟩

-- Boundary: the instance an author reaches for when the object type has no identity — send
-- everything to one name — does not satisfy the class, because injectivity is a field.
#check_failure (⟨fun _ => sysA, fun _ => rfl⟩ : Designated (Fin 4))

/-- The nominal object type designates itself, and injectively. -/
example : Designated.designation sysA = sysA ∧ (Designated.designation sysA ≠ sysB) :=
  ⟨rfl, by decide⟩

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.assemble_eq_measured' depends on axioms: [propext] -/
#guard_msgs in #print axioms assemble_eq_measured

/-- info: 'PropertyKindCalculus.Tests.Composite.assembled_is_measured' depends on axioms: [propext] -/
#guard_msgs in #print axioms assembled_is_measured

end PropertyKindCalculus.Tests.Composite
