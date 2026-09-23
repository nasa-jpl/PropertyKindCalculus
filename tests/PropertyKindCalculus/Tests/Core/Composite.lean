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

module

public import PropertyKindCalculus
meta import PropertyKindCalculus
-- Private scope only: the checks below reduce through bodies sealed in the core
-- library; `import all` gives this file the reduction without exposing them.
import all PropertyKindCalculus.Bounds

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.Composite

open PropertyKindCalculus

/-- Mass — the archetypal assembling kind. -/
def massK : KindOfProperty := { id := "composite probe mass", scale := .ratio }
/-- A ratio kind deliberately left off the assembly registry. -/
def angVelK : KindOfProperty := { id := "composite probe angular velocity", scale := .ratio }
/-- An *ordinal* kind — the scale gate's target: no sum is meaningful, so no license exists. -/
def hardnessK : KindOfProperty := { id := "composite probe hardness", scale := .ordinal }

/-- The sort of whole the probes assemble. -/
def probeS : SortOfSystem := ⟨"composite probe assembly"⟩

instance : Assembles probeS massK := ⟨DifferenceKind.ofScale⟩

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
def partMass (c : Part4) : IndividualQuantity (Composite.part (σ := probeS) c) massK Int := ⟨2⟩

/-- The whole's mass, assembled. -/
def wholeMass : IndividualQuantity (Composite.whole : Composite probeS Part4) massK Int :=
  assemble probeS Composite.whole Composite.part four partMass

-- Inhabitation: four parts of two kilograms assemble to eight.
#guard wholeMass.magnitude == 8

-- Boundary (MR22): the whole's mass and a part's mass are quantities of different objects.
#check_failure IndividualQuantity.add (k := massK) DifferenceKind.ofScale wholeMass (partMass 0)

-- Boundary: the license is opt-in — `angVelK` is a ratio kind, so nothing about its *scale*
-- stops the sum; what stops it is that no one registered it as assembling.
#check_failure fun (f : (c : Part4) →
      IndividualQuantity (Composite.part (σ := probeS) c) angVelK Int) =>
  assemble (k := angVelK) probeS Composite.whole Composite.part four f

-- Boundary: the license has content — an ordinal kind cannot be licensed at all, because
-- `Assembles` carries the same scale gate `add` demands.
#check_failure (⟨DifferenceKind.ofScale⟩ : Assembles probeS hardnessK)

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
    (assemble (k := massK) probeS (Composite.whole : Composite probeS Part4) Composite.part
      four (fun p => ⟨(leafMass (.atom p)).numeral⟩)).magnitude = (leafMass four).numeral :=
  assemble_eq_measured probeS _ _ leafMass_extensive four

#guard (leafMass four).numeral == 4

/-! ## The license is sort-relative — the volume split

One kind, two sorts of whole, opposite verdicts, and both backed by a witness. Volume over
the parts of a rigid assembly is additive by construction and is licensed; volume over the
parts of a mixture contracts — the source's own ethanol/water counterexample — and no
license exists to look up. A registry keyed by the kind alone would have to give one answer
to both, and either answer is wrong. -/

/-- The rigid sort of whole: volumes of disjoint rigid parts aggregate. -/
def rigidS : SortOfSystem := ⟨"rigid assembly"⟩
/-- The mixed sort of whole: volumes of miscible parts do not. -/
def mixtureS : SortOfSystem := ⟨"liquid mixture"⟩

/-- A rigid-assembly volume reading — additive by construction, one unit per leaf. -/
def rigidVolume : Measurement Part4 :=
  fun d => { kind := volume, numeral := countLeaves d, reference := "L" }

/-- The `Extensive` witness that backs the rigid license — real, not assumed. -/
theorem rigidVolume_extensive : Extensive volume rigidVolume := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- Volume assembles into a *rigid* whole. -/
instance : Assembles rigidS volume := ⟨DifferenceKind.ofScale⟩

-- The mixture's refusal is not a missing registration; it has a *negative* witness — the
-- source's ethanol/water contraction (96 < 50 + 50).
theorem mixture_volume_not_extensive : ¬ Extensive volume volMix := mixing_subadditive.2

-- Boundary: same kind, other sort — no license to look up, so the assembled mixture volume
-- is not a term.
#check_failure (inferInstance : Assembles mixtureS volume)

-- Inhabitation: the rigid assembly's volume is a term, and it is the measured whole.
theorem rigid_volume_assembles :
    (assemble (k := volume) rigidS (Composite.whole : Composite rigidS Part4) Composite.part
      four (fun p => ⟨(rigidVolume (.atom p)).numeral⟩)).magnitude
      = (rigidVolume four).numeral :=
  assemble_eq_measured rigidS _ _ rigidVolume_extensive four

/-! ## Two wholes over one part type — the statue and the lump

The sort index on `Composite` is what lets both stand: same parts, different sorts, different
types, so a quantity of the one whole does not combine with a quantity of the other. Which
whole a total belongs to is part of what the total is. -/

/-- A statue, as a sort of whole over the probe parts. -/
def statueS : SortOfSystem := ⟨"statue"⟩
/-- The mere lump over the very same parts. -/
def lumpS : SortOfSystem := ⟨"lump of clay"⟩

-- Boundary: the statue's mass and the lump's mass do not add, though the parts are the same
-- and the kind is the same.
#check_failure fun
    (x : IndividualQuantity (Composite.whole : Composite statueS Part4) massK Int)
    (y : IndividualQuantity (Composite.whole : Composite lumpS Part4) massK Int) =>
  IndividualQuantity.add DifferenceKind.ofScale x y

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

/-! ## The license refused — a whole-proper kind assembled anyway

`Assembles` licenses the sum to be *written*, and writing it is not what makes it true. Here
the registry entry is made deliberately wrong — the coupled pair's normal-mode frequency is a
kind no aggregation produces (`normalMode_wholeProper`, `Extensivity.lean`) — and the term
still elaborates, so the probe can exhibit the carving on which it reports the wrong number.
This is the negative twin of `rigid_volume_assembles` above. -/

/-- The sort of the coupled pair, registered for a kind that does not aggregate at it. The
mistake has to be writable for the probe to catch it. -/
def pairS : SortOfSystem := ⟨"composite probe oscillator pair"⟩

instance : Assembles pairS oscillatorFrequency := ⟨DifferenceKind.ofScale⟩

-- Boundary: with the license in hand the sum elaborates, and is not the pair's frequency —
-- 10 + 10 against a normal mode at 14.
theorem pair_frequency_assembles_wrongly :
    ∃ d : Decomposition System,
      (assemble (k := oscillatorFrequency) (R := Int) pairS
        (Composite.whole : Composite pairS System) Composite.part d
        (fun p => ⟨(normalModeFreq (.atom p)).numeral⟩)).magnitude
        ≠ (normalModeFreq d).numeral :=
  assemble_ne_measured pairS _ _ normalMode_wholeProper

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.assemble_eq_measured' depends on axioms: [propext] -/
#guard_msgs in #print axioms assemble_eq_measured

/-- info: 'PropertyKindCalculus.Tests.Composite.assembled_is_measured' depends on axioms: [propext] -/
#guard_msgs in #print axioms assembled_is_measured

/-- info: 'PropertyKindCalculus.assemble_ne_measured' depends on axioms: [propext] -/
#guard_msgs in #print axioms assemble_ne_measured

/-- info: 'PropertyKindCalculus.Tests.Composite.pair_frequency_assembles_wrongly' depends on axioms: [propext] -/
#guard_msgs in #print axioms pair_frequency_assembles_wrongly

end PropertyKindCalculus.Tests.Composite

end Blanket
