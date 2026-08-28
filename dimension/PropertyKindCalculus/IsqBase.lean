/-
# The ISQ base — consumed from PhysLib's contributed bridge, the catalogue's stance kept here

PhysLib's `Dimension` is parametric in its basis, and PKC fixes the five-generator
*charge*-based `LTMCTDimensionBase` as canonical (see `Dimension`). ISO 80000-1's own basis is the
seven-generator **ISQ**, which differs in two ways: it takes electric *current* as base
(charge derived, `Q = I·T`) and it adds *amount of substance* and *luminous intensity*.

**Provenance.** This module originally *realized* ISQ itself — a local `ISQBase` inductive and a
hand-built injective hom — because PhysLib's ISQ material was example-only and not importable.
That layer has since been contributed **upstream** (the same contribution line as the
basis-parametric `Dimension B` itself, PR #1447 and follow-ons): `Physlib.Units.ISQDimensionBase`
is the seven-generator basis, and `Physlib.Units.ISQBridge` is the bridge, *strengthened* — not
just the injective embedding `Dimension.toISQHom : Dimension LTMCTDimensionBase →* Dimension
ISQDimensionBase` (charge ↦ current·time), but also the reverse projection
`Dimension.fromISQHom` and the retraction law `fromISQHom ∘ toISQHom = id`, packaged as the
`Dimension.Embedding`/`Dimension.Projection` pair `ltmctToISQ`/`isqToLTMCT`. PKC now consumes
that bridge; the local mirror is retired.

What remains *here* is exactly what is PKC's to say, not the bridge's:

* **The preserved-generator laws and citation fidelity.** Length, mass and temperature carry
  over unchanged; PhysLib's charge generator maps to the upstream *derived* ISQ charge
  (`ISQDimensionBase.charge = I·T`); and PhysLib's internal ampere `C·T⁻¹` collapses to the
  bare `current` generator — which is exactly why the catalogue can *cite* electromagnetic
  dimensions in current (`Iso80000.renderDimension`).
* **The mole/candela reduction is a stance, not a lack.** `ISQDimensionBase` *offers* the
  `amount` and `luminousIntensity` generators, yet PKC's reduction declines them: the mole
  stays dimension one and the candela stays power even over a basis that could carry them.
  The reduction is a modeling choice preserved under the lift, and the distinctions it drops
  are carried by the kind layer.
* **The catalogue is base-agnostic.** Re-expressing a dimensioned kind over ISQ leaves its
  kind fixed (`DimensionedKind.mapDim`, `mapDim_kind`) — the base choice lives below the
  kind layer.

Library module (theorems only), mirroring `AngleReform`: it does *not* import the ISO
catalogue (a downstream library), so the lift is demonstrated on a local witness kind.
Built by `lake build Dimension`.
-/
import PropertyKindCalculus.Dimension
import Physlib.Units.ISQBridge

open Dimension

namespace PropertyKindCalculus
namespace IsqBase

/-! ## The change of basis, consumed from upstream

`Dimension.toISQHom` is the genuine group homomorphism `charge ↦ current · time` — the map a
mere generator reindexing (`Dimension.extend`) cannot express, since a generator goes to a
*product*. Injectivity (`Dimension.toISQHom_injective`) is upstream too; the strengthening the
contribution added over the original local hom is the reverse direction, surfaced here as the
pointwise retraction. -/

/-- **The bridge is a retraction, pointwise.** Every PhysLib dimension survives the round trip
through ISQ — the projection `fromISQHom` recovers it exactly (upstream
`Dimension.fromISQHom_comp_toISQHom`, applied). The reverse composite is *not* the identity:
`amount` and `luminousIntensity` cannot be recovered once dropped. -/
theorem fromISQHom_toISQHom (d : Dimension LTMCTDimensionBase) :
    fromISQHom (toISQHom d) = d := by
  simpa using DFunLike.congr_fun fromISQHom_comp_toISQHom d

/-! ## The reform's laws: mass/length preserved, charge derived, the ampere a base quantity -/

/-- Length is preserved by the change of basis. -/
theorem toISQHom_length : toISQHom Dim.length = single ISQDimensionBase.length := by
  ext b
  cases b <;> simp [toISQHom_apply, toISQFun, Dim.length, Dimension.L𝓭,
    Dimension.ofLTMCTDimensionBase, single_exponent, Dimension.length, Dimension.time,
    Dimension.mass, Dimension.charge, Dimension.temperature]

/-- Mass is preserved by the change of basis. -/
theorem toISQHom_mass : toISQHom Dim.mass = single ISQDimensionBase.mass := by
  ext b
  cases b <;> simp [toISQHom_apply, toISQFun, Dim.mass, Dimension.M𝓭,
    Dimension.ofLTMCTDimensionBase, single_exponent, Dimension.length, Dimension.time,
    Dimension.mass, Dimension.charge, Dimension.temperature]

/-- Temperature is preserved by the change of basis. -/
theorem toISQHom_temperature :
    toISQHom Dim.temperature = single ISQDimensionBase.temperature := by
  ext b
  cases b <;> simp [toISQHom_apply, toISQFun, Dim.temperature, Dimension.Θ𝓭,
    Dimension.ofLTMCTDimensionBase, single_exponent, Dimension.length, Dimension.time,
    Dimension.mass, Dimension.charge, Dimension.temperature]

/-- **Charge is derived in the ISQ: `Q = I·T`.** The generator PhysLib takes as base maps to
the upstream-named derived charge `ISQDimensionBase.charge` (defined there as
`current · time`). Restates upstream `Dimension.toISQHom_C𝓭` at the catalogue's `Dim.charge`
spelling. -/
theorem toISQHom_charge : toISQHom Dim.charge = ISQDimensionBase.charge :=
  toISQHom_C𝓭

/-- **Over ISQ the ampere is a base quantity.** PhysLib's internal ampere `C·T⁻¹` collapses
to the bare current generator: its charge and time factors cancel, leaving `single .current`
— the citation-faithful electromagnetic base dimension of ISO 80000-6. -/
theorem toISQHom_current : toISQHom Dim.current = single ISQDimensionBase.current := by
  ext b
  cases b <;> simp [toISQHom_apply, toISQFun, Dim.current, Dimension.C𝓭, Dimension.T𝓭,
    Dimension.ofLTMCTDimensionBase, Dimension.div_exponent, single_exponent, Dimension.length, Dimension.time,
    Dimension.mass, Dimension.charge, Dimension.temperature]

/-! ## The mole/candela reduction is a stance, not a lack

`ISQDimensionBase` provides an independent generator for each of amount of substance and
luminous intensity — yet PKC's catalogue declines both. The reductions
`Dim.amountOfSubstance = 1` and `Dim.luminousIntensity = Dim.power` survive the lift into a
basis that *could* carry them, so they are a modeling choice, not an artefact of
`LTMCTDimensionBase`. -/

/-- Over ISQ the mole is still dimension one: PKC's reduction is preserved by the lift, even
though ISQ offers an independent `amount` generator. -/
theorem toISQHom_amountOfSubstance : toISQHom Dim.amountOfSubstance = 1 := by
  rw [Dim.amountOfSubstance_eq_one, map_one]

/-- ISQ *offers* an amount-of-substance generator that PKC declines: the bare `mol` generator
is not the (dimension-one) image of the mole (delegates to upstream
`ISQDimensionBase.single_amount_ne_one`). -/
theorem isq_amount_generator_declined :
    single (.amount : ISQDimensionBase) ≠ toISQHom Dim.amountOfSubstance := by
  rw [toISQHom_amountOfSubstance]
  exact ISQDimensionBase.single_amount_ne_one

/-- Over ISQ the candela is still power — its luminous-intensity exponent is zero: the
reduction `Dim.luminousIntensity = Dim.power` survives the lift, though ISQ offers a
luminous-intensity generator. -/
theorem toISQHom_luminousIntensity_luminous_free :
    (toISQHom Dim.luminousIntensity).exponent .luminousIntensity = 0 := by
  simp [toISQHom_apply, toISQFun]

/-- ISQ *offers* a luminous-intensity generator that PKC declines: the bare `cd` generator is
not the (power-valued) image of the candela. -/
theorem isq_luminous_generator_declined :
    single (.luminousIntensity : ISQDimensionBase) ≠ toISQHom Dim.luminousIntensity := by
  intro h
  have := congrArg (fun d => Dimension.exponent d ISQDimensionBase.luminousIntensity) h
  simp [single_exponent, toISQHom_luminousIntensity_luminous_free] at this

/-! ## The catalogue lifts into ISQ, kinds invariant

A dimensioned kind re-expressed over ISQ is the *same kind* (the base choice is invisible
one layer up), and the ampere reads as a genuine base quantity — the base-agnosticism and
citation-fidelity headline, on a witness kind (the ISO catalogue is a downstream library, so
the witness is local, exactly as `AngleReform` lifts `lengthKind`). -/

/-- A witness catalogued kind — electric current — dimensioned over the canonical
`LTMCTDimensionBase` (PhysLib's charge generator, `A = C·T⁻¹`). -/
def electricCurrentKind : DimensionedKind :=
  { kind := { id := "electric current", scale := .ratio }, dim := Dim.current }

/-- **The lift fixes the kind.** Re-expressing the kind over ISQ leaves its kind identical —
the catalogue is base-agnostic. -/
theorem electricCurrentKind_lift_kind :
    (electricCurrentKind.mapDim toISQHom).kind = electricCurrentKind.kind := rfl

/-- **Over ISQ the lifted ampere reads as a base quantity.** The lifted electric-current kind
carries the bare `current` generator — the citation-faithful ISO 80000-6 dimension, recovered
from PhysLib's internal charge encoding. -/
theorem electricCurrentKind_lift_dim :
    (electricCurrentKind.mapDim toISQHom).toDimension = single ISQDimensionBase.current := by
  show toISQHom Dim.current = single ISQDimensionBase.current
  exact toISQHom_current

end IsqBase
end PropertyKindCalculus
