/-
# Validation probes — the ISQ base (base-agnosticism + citation fidelity)

Inhabitation and axiom-profile probes for `IsqBase`, which consumes PhysLib's contributed
`ISQDimensionBase`/`ISQBridge` (the upstreamed strengthening of PKC's original local ISQ
realization) and keeps the catalogue's residue: preserved-generator laws, citation fidelity,
and the mole/candela stance. The Rule-2 boundaries are (a) the charge → current change of
basis is a genuine *product*-valued homomorphism `charge ↦ current · time`, not a generator
reindexing; it is injective (upstream `Dimension.toISQHom_injective`) and now moreover a
**retraction** — the contributed projection recovers every PhysLib dimension exactly; and
(b) the mole/candela reduction is a modeling *stance*, not a lack — it survives the lift into
a base that *offers* the two generators, which the catalogue then declines. The Mathlib-backed
proofs legitimately use `[propext, Classical.choice, Quot.sound]`; the gate confirms
**no `sorryAx`** creeps in.
-/

module

public import PropertyKindCalculus.IsqBase

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Tests.IsqBase

open PropertyKindCalculus PropertyKindCalculus.IsqBase Dimension

/-! ## The charge → current change of basis, consumed from the contributed bridge -/

-- Inhabitation: charge is the ISQ *derived* current·time (the upstream-named
-- `ISQDimensionBase.charge`), and PhysLib's internal ampere `C·T⁻¹` collapses to the bare
-- current generator — the citation-faithful base dimension.
theorem isq_charge_and_ampere :
    toISQHom Dim.charge = ISQDimensionBase.charge ∧
    toISQHom Dim.current = single ISQDimensionBase.current :=
  ⟨toISQHom_charge, toISQHom_current⟩

-- Boundary: the change of basis is injective — no dimensional information is lost passing
-- from the charge basis to the current basis — and, strengthened upstream, a *retraction*:
-- the contributed projection `fromISQHom` recovers every PhysLib dimension on the nose.
theorem isq_lossless_and_retracts :
    Function.Injective toISQHom ∧ ∀ d, fromISQHom (toISQHom d) = d :=
  ⟨toISQHom_injective, fromISQHom_toISQHom⟩

/-! ## The mole/candela reduction is a stance, not a lack -/

-- Boundary: `ISQDimensionBase` provides `amount` and `luminousIntensity` generators, yet
-- PKC's catalogue declines both — the mole stays dimension one and the candela stays power
-- under the lift, so the reductions are a modeling choice, not an artefact of
-- `LTMCTDimensionBase`.
theorem isq_reduction_is_a_stance :
    toISQHom Dim.amountOfSubstance = 1 ∧
    single (.amount : ISQDimensionBase) ≠ toISQHom Dim.amountOfSubstance ∧
    single (.luminousIntensity : ISQDimensionBase) ≠ toISQHom Dim.luminousIntensity :=
  ⟨toISQHom_amountOfSubstance, isq_amount_generator_declined,
    isq_luminous_generator_declined⟩

/-! ## The catalogue lifts into ISQ, kind invariant -/

-- Inhabitation: re-expressing a dimensioned kind over ISQ fixes its kind (base-agnosticism)
-- and the ampere reads as a base quantity (citation fidelity).
theorem isq_lift_kind_invariant :
    (electricCurrentKind.mapDim toISQHom).kind = electricCurrentKind.kind ∧
    (electricCurrentKind.mapDim toISQHom).toDimension = single ISQDimensionBase.current :=
  ⟨electricCurrentKind_lift_kind, electricCurrentKind_lift_dim⟩

/-- info: 'PropertyKindCalculus.IsqBase.toISQHom_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toISQHom_charge

/-- info: 'Dimension.toISQHom_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Dimension.toISQHom_injective

/-- info: 'PropertyKindCalculus.IsqBase.fromISQHom_toISQHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fromISQHom_toISQHom

/-- info: 'PropertyKindCalculus.IsqBase.isq_luminous_generator_declined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isq_luminous_generator_declined

-- Kind invariance under any re-dimensioning is *definitional* (`rfl`) — axiom-free.
/-- info: 'PropertyKindCalculus.DimensionedKind.mapDim_kind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms DimensionedKind.mapDim_kind

end PropertyKindCalculus.Tests.IsqBase

end -- pkc-blanket-expose
end -- pkc-blanket
