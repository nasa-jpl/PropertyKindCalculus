/-
# The ISQ base — the catalogue is base-agnostic and cites faithfully in current

PhysLib's `Dimension` is parametric in its basis, and PKC fixes the five-generator
*charge*-based `LTMCTDimensionBase` as canonical (see `Dimension`). ISO 80000-1's own basis is the
seven-generator **ISQ**, which differs in two ways: it takes electric *current* as base
(charge derived, `Q = I·T`) and it adds *amount of substance* and *luminous intensity*.
This module realizes ISQ as `ISQBase` and settles, as theorems, what each difference costs.

* **The charge → current change of basis is a genuine group homomorphism** `toISQ :
  Dimension LTMCTDimensionBase →* Dimension ISQBase` sending `charge ↦ current · time`. This is
  *not* a reindexing of generators (`Dimension.extend`): a generator maps to a *product*,
  which `extend` cannot express — so it needs a real hom, built and proved injective
  (lossless) here.
* **Over ISQ the ampere is a base quantity.** `toISQ Dim.current = single .current`: the
  charge/time factors of PhysLib's internal ampere cancel to the bare current generator —
  which is exactly why the catalogue can *cite* electromagnetic dimensions in current
  (`Iso80000.renderDimension`).
* **The catalogue is base-agnostic.** Re-expressing a dimensioned kind over ISQ leaves its
  kind fixed (`DimensionedKind.mapDim`, `mapDim_kind`) — the base choice lives below the
  kind layer.
* **The mole/candela reduction is a stance, not a lack.** `ISQBase` *offers* the `amount`
  and `luminousIntensity` generators, yet PKC's reduction declines them: the mole stays
  dimension one and the candela stays power even here. The reduction is a modeling choice
  preserved under the lift, and the distinctions it drops are carried by the kind layer.

Library module (theorems only), mirroring `AngleReform`: it does *not* import the ISO
catalogue (a downstream library), so the lift is demonstrated on a local witness kind.
Built by `lake build Dimension`.
-/
import PropertyKindCalculus.Dimension

open Dimension

namespace PropertyKindCalculus

/-- **The ISO/IEC 80000-1 base quantities (ISQ)** — the seven-generator, *current*-based
basis: length, time, mass, electric **current**, temperature, **amount of substance**,
**luminous intensity**. Contrast PKC's canonical `LTMCTDimensionBase`, which is charge-based and
omits the last two (see `Dimension`). -/
inductive ISQBase
  | length | time | mass | current | temperature | amount | luminousIntensity
  deriving DecidableEq, Fintype

namespace IsqBase

/-! ## The charge → current change of basis, as a group homomorphism -/

/-- The underlying map of the change of basis `LTMCTDimensionBase → ISQBase`. Because the coulomb
is the ampere-second, `C = I·T`, a charge exponent `q` becomes a current exponent `q`
together with an added time exponent `q`; the mass/length/temperature axes carry over
unchanged, and the amount/luminous-intensity axes that ISQ adds start at zero. -/
def ofPhyslib (d : Dimension LTMCTDimensionBase) : Dimension ISQBase :=
  ⟨fun
    | .length => d.length
    | .time => d.time + d.charge
    | .mass => d.mass
    | .current => d.charge
    | .temperature => d.temperature
    | .amount => 0
    | .luminousIntensity => 0⟩

@[simp] theorem ofPhyslib_length (d : Dimension LTMCTDimensionBase) :
    (ofPhyslib d).exponent .length = d.length := rfl
@[simp] theorem ofPhyslib_time (d : Dimension LTMCTDimensionBase) :
    (ofPhyslib d).exponent .time = d.time + d.charge := rfl
@[simp] theorem ofPhyslib_mass (d : Dimension LTMCTDimensionBase) :
    (ofPhyslib d).exponent .mass = d.mass := rfl
@[simp] theorem ofPhyslib_current (d : Dimension LTMCTDimensionBase) :
    (ofPhyslib d).exponent .current = d.charge := rfl
@[simp] theorem ofPhyslib_temperature (d : Dimension LTMCTDimensionBase) :
    (ofPhyslib d).exponent .temperature = d.temperature := rfl
@[simp] theorem ofPhyslib_amount (d : Dimension LTMCTDimensionBase) :
    (ofPhyslib d).exponent .amount = 0 := rfl
@[simp] theorem ofPhyslib_luminousIntensity (d : Dimension LTMCTDimensionBase) :
    (ofPhyslib d).exponent .luminousIntensity = 0 := rfl

/-- **The charge → current change of basis is a group homomorphism** `Dimension LTMCTDimensionBase
→* Dimension ISQBase`: it carries the dimensionless `1` to `1` and products to products, so
the whole dimensional algebra transports. Each output exponent is a fixed ℤ-linear
combination of input exponents, which is exactly what makes it a hom. -/
def toISQ : Dimension LTMCTDimensionBase →* Dimension ISQBase where
  toFun := ofPhyslib
  map_one' := by ext b; cases b <;> simp
  map_mul' a c := by
    ext b
    cases b <;> simp [Dimension.mul_exponent]
    ring

@[simp] theorem toISQ_apply (d : Dimension LTMCTDimensionBase) : toISQ d = ofPhyslib d := rfl

/-! ## The reform's laws: mass/length preserved, charge derived, the ampere a base quantity

The mechanical generators carry over unchanged; charge is the ISQ *derived* `current · time`;
and PhysLib's internal ampere becomes the bare ISQ current generator. -/

/-- Length is preserved by the change of basis. -/
theorem toISQ_length : toISQ Dim.length = single .length := by
  ext b; cases b <;> simp [Dim.length, single_exponent]

/-- Mass is preserved by the change of basis. -/
theorem toISQ_mass : toISQ Dim.mass = single .mass := by
  ext b; cases b <;> simp [Dim.mass, Dimension.M𝓭, single_exponent]

/-- Temperature is preserved by the change of basis. -/
theorem toISQ_temperature : toISQ Dim.temperature = single .temperature := by
  ext b; cases b <;> simp [Dim.temperature, Dimension.Θ𝓭, single_exponent]

/-- **Charge is derived in the ISQ: `Q = I·T`.** The generator PhysLib takes as base maps to
the ISQ *product* current · time — the map a mere generator reindexing (`Dimension.extend`)
cannot express. -/
theorem toISQ_charge : toISQ Dim.charge = single .current * single .time := by
  ext b; cases b <;>
    simp [Dim.charge, Dimension.C𝓭, single_exponent, Dimension.mul_exponent]

/-- **Over ISQ the ampere is a base quantity.** PhysLib's internal ampere `C·T⁻¹` collapses
to the bare current generator: its charge and time factors cancel, leaving `single .current`
— the citation-faithful electromagnetic base dimension of ISO 80000-6. -/
theorem toISQ_current : toISQ Dim.current = single .current := by
  ext b; cases b <;> simp [Dim.current, Dimension.C𝓭, single_exponent]

/-- **The change of basis is injective — lossless.** No dimensional information is discarded
in passing from the charge basis to the current basis: charge is recovered from the current
exponent, and time from the time exponent net of it. -/
theorem toISQ_injective : Function.Injective toISQ := by
  intro a b h
  have hcur : a.charge = b.charge := by
    have := congrArg (fun d => Dimension.exponent d ISQBase.current) h; simpa using this
  have htime : a.time + a.charge = b.time + b.charge := by
    have := congrArg (fun d => Dimension.exponent d ISQBase.time) h; simpa using this
  have hlen : a.length = b.length := by
    have := congrArg (fun d => Dimension.exponent d ISQBase.length) h; simpa using this
  have hmass : a.mass = b.mass := by
    have := congrArg (fun d => Dimension.exponent d ISQBase.mass) h; simpa using this
  have htemp : a.temperature = b.temperature := by
    have := congrArg (fun d => Dimension.exponent d ISQBase.temperature) h; simpa using this
  have htime' : a.time = b.time := by rw [hcur] at htime; linarith
  ext x
  cases x
  · exact hlen
  · exact htime'
  · exact hmass
  · exact hcur
  · exact htemp

/-! ## The mole/candela reduction is a stance, not a lack

`ISQBase` provides an independent generator for each of amount of substance and luminous
intensity — yet PKC's catalogue declines both. The reductions `Dim.amountOfSubstance = 1`
and `Dim.luminousIntensity = Dim.power` survive the lift into a basis that *could* carry
them, so they are a modeling choice, not an artefact of `LTMCTDimensionBase`. -/

/-- Over ISQ the mole is still dimension one: PKC's reduction is preserved by the lift, even
though ISQ offers an independent `amount` generator. -/
theorem toISQ_amountOfSubstance : toISQ Dim.amountOfSubstance = 1 := by
  rw [Dim.amountOfSubstance_eq_one, map_one]

/-- ISQ *offers* an amount-of-substance generator that PKC declines: the bare `mol` generator
is not the (dimension-one) image of the mole. -/
theorem isq_amount_generator_declined :
    single (.amount : ISQBase) ≠ toISQ Dim.amountOfSubstance := by
  rw [toISQ_amountOfSubstance]
  intro h
  have := congrArg (fun d => Dimension.exponent d ISQBase.amount) h
  simp [single_exponent] at this

/-- Over ISQ the candela is still power — its luminous-intensity exponent is zero: the
reduction `Dim.luminousIntensity = Dim.power` survives the lift, though ISQ offers a
luminous-intensity generator. -/
theorem toISQ_luminousIntensity_luminous_free :
    (toISQ Dim.luminousIntensity).exponent .luminousIntensity = 0 := by
  simp

/-- ISQ *offers* a luminous-intensity generator that PKC declines: the bare `cd` generator is
not the (power-valued) image of the candela. -/
theorem isq_luminous_generator_declined :
    single (.luminousIntensity : ISQBase) ≠ toISQ Dim.luminousIntensity := by
  intro h
  have := congrArg (fun d => Dimension.exponent d ISQBase.luminousIntensity) h
  simp [single_exponent] at this

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
    (electricCurrentKind.mapDim toISQ).kind = electricCurrentKind.kind := rfl

/-- **Over ISQ the lifted ampere reads as a base quantity.** The lifted electric-current kind
carries the bare `current` generator — the citation-faithful ISO 80000-6 dimension, recovered
from PhysLib's internal charge encoding. -/
theorem electricCurrentKind_lift_dim :
    (electricCurrentKind.mapDim toISQ).toDimension = single .current := by
  show toISQ Dim.current = single .current
  exact toISQ_current

end IsqBase
end PropertyKindCalculus
