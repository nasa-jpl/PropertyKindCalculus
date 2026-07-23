/-
# Validation probes — the ISQ base (base-agnosticism + citation fidelity)

Inhabitation and axiom-profile probes for `IsqBase`, which realizes ISO 80000-1's
seven-generator, *current*-based ISQ and settles what each departure of PKC's canonical
charge-based `LTMCTDimensionBase` costs. Each result is applied to concrete witnesses. The Rule-2
boundaries are (a) the charge → current change of basis is a genuine *product*-valued
homomorphism `charge ↦ current · time`, not a generator reindexing, and it is injective
(lossless); and (b) the mole/candela reduction is a modeling *stance*, not a lack — it
survives the lift into a base that *offers* the two generators, which the catalogue then
declines. The Mathlib-backed proofs legitimately use `[propext, Classical.choice,
Quot.sound]`; the gate confirms **no `sorryAx`** creeps in.
-/

import PropertyKindCalculus.IsqBase

namespace PropertyKindCalculus.Tests.IsqBase

open PropertyKindCalculus PropertyKindCalculus.IsqBase Dimension

/-! ## The charge → current change of basis, done as a genuine hom -/

-- Inhabitation: charge is the ISQ *derived* current·time, and PhysLib's internal ampere
-- `C·T⁻¹` collapses to the bare current generator — the citation-faithful base dimension.
theorem isq_charge_and_ampere :
    toISQ Dim.charge = single .current * single .time ∧
    toISQ Dim.current = single .current :=
  ⟨toISQ_charge, toISQ_current⟩

-- Boundary: the change of basis is injective — no dimensional information is lost passing
-- from the charge basis to the current basis (`extend`'s generator reindexing could not
-- express `charge ↦ current · time` in the first place).
theorem isq_lossless : Function.Injective toISQ := toISQ_injective

/-! ## The mole/candela reduction is a stance, not a lack -/

-- Boundary: `ISQBase` provides `amount` and `luminousIntensity` generators, yet PKC's
-- catalogue declines both — the mole stays dimension one and the candela stays power under
-- the lift, so the reductions are a modeling choice, not an artefact of `LTMCTDimensionBase`.
theorem isq_reduction_is_a_stance :
    toISQ Dim.amountOfSubstance = 1 ∧
    single (.amount : ISQBase) ≠ toISQ Dim.amountOfSubstance ∧
    single (.luminousIntensity : ISQBase) ≠ toISQ Dim.luminousIntensity :=
  ⟨toISQ_amountOfSubstance, isq_amount_generator_declined, isq_luminous_generator_declined⟩

/-! ## The catalogue lifts into ISQ, kind invariant -/

-- Inhabitation: re-expressing a dimensioned kind over ISQ fixes its kind (base-agnosticism)
-- and the ampere reads as a base quantity (citation fidelity).
theorem isq_lift_kind_invariant :
    (electricCurrentKind.mapDim toISQ).kind = electricCurrentKind.kind ∧
    (electricCurrentKind.mapDim toISQ).toDimension = single .current :=
  ⟨electricCurrentKind_lift_kind, electricCurrentKind_lift_dim⟩

/-- info: 'PropertyKindCalculus.IsqBase.toISQ_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toISQ_charge

/-- info: 'PropertyKindCalculus.IsqBase.toISQ_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toISQ_injective

/-- info: 'PropertyKindCalculus.IsqBase.isq_luminous_generator_declined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isq_luminous_generator_declined

-- Kind invariance under any re-dimensioning is *definitional* (`rfl`) — axiom-free.
/-- info: 'PropertyKindCalculus.DimensionedKind.mapDim_kind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms DimensionedKind.mapDim_kind

end PropertyKindCalculus.Tests.IsqBase
