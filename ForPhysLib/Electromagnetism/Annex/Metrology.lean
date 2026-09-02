/-
# Stage 1 — the metrology annex of the RF/AC vocabulary

The dimensional layer over `Kinds.lean`, in the Kinematics pattern: every Stage-0
literal is proved to agree with PKC's IEC 80000-6 catalogue by `decide`; every
pairing's dimension is the catalogue's by `rfl`; and the kind algebra is authored as
edge laws with `#kind_dimensional_coverage` pinned over it.

**Most of the algebra ships with the standard.** Five of the ten edges below are
*consumed* from the catalogue's own `Part6.DefiningRelations` — Ohm's law, the
reciprocal pairs, `P = U·I`, the power factor's quotient — because the annex's
vocabulary is the standard's home ground (the Stage-0 finding, one rung up). The
authored five are the phasor spellings: the complex Ohm's law and the complex power,
which the catalogue states as remarks and this file states as kind laws.

**The registry shows the collisions.** Three kinds at the ohm's dimension, two at
the siemens, six at the watt, two at dimension one, and each phasor at its base
quantity's dimension — every one visible as a repeated `dim` below, and every one
separated by a Stage-0 `decide`.
-/

import ForPhysLib.Electromagnetism.Annex.Kinds
import PropertyKindCalculus.Dimension
import PropertyKindCalculus.DimensionalCoverage
import PropertyKindCalculus.Iso80000.Part6
import PropertyKindCalculus.Iso80000.Part6.DefiningRelations

namespace ForPhysLib.Electromagnetism.Annex.Metrology

open PropertyKindCalculus
open ForPhysLib.Electromagnetism.Annex.Kinds

/-! ## The pairings — every kind at its catalogue dimension -/

/-- Electric current is `C·T⁻¹` (the ampere). -/
def electricCurrentDK : DimensionedKind :=
  { kind := electricCurrent, dim := Dim.current }
/-- Voltage is `M·L²·T⁻²·C⁻¹` (the volt). -/
def voltageDK : DimensionedKind :=
  { kind := voltage, dim := Iso80000.Part6.EDim.voltage }
/-- Resistance is `M·L²·T⁻¹·C⁻²` (the ohm). -/
def resistanceDK : DimensionedKind :=
  { kind := resistance, dim := Iso80000.Part6.EDim.resistance }
/-- Conductance is `M⁻¹·L⁻²·T·C²` (the siemens). -/
def conductanceDK : DimensionedKind :=
  { kind := conductance, dim := Iso80000.Part6.EDim.conductance }
/-- Impedance is the *same* ohm — a distinct kind at a repeated dimension. -/
def impedanceDK : DimensionedKind :=
  { kind := impedance, dim := Iso80000.Part6.EDim.resistance }
/-- Reactance is the *same* ohm again — three kinds, one dimension. -/
def reactanceDK : DimensionedKind :=
  { kind := reactance, dim := Iso80000.Part6.EDim.resistance }
/-- Admittance is the *same* siemens as conductance. -/
def admittanceDK : DimensionedKind :=
  { kind := admittance, dim := Iso80000.Part6.EDim.conductance }
/-- The phase difference is dimension one (an angle). -/
def phaseDifferenceDK : DimensionedKind :=
  { kind := phaseDifference, dim := Dim.one }
/-- The current phasor is the ampere — the phasor collision. -/
def electricCurrentPhasorDK : DimensionedKind :=
  { kind := electricCurrentPhasor, dim := Dim.current }
/-- The voltage phasor is the volt. -/
def voltagePhasorDK : DimensionedKind :=
  { kind := voltagePhasor, dim := Iso80000.Part6.EDim.voltage }
/-- Power is `M·L²·T⁻³` (the watt) — the genus. -/
def powerDK : DimensionedKind :=
  { kind := power, dim := Iso80000.Part6.EDim.power }
/-- Active power — the same watt (`W`). -/
def activePowerDK : DimensionedKind :=
  { kind := activePower, dim := Iso80000.Part6.EDim.power }
/-- Apparent power — the same watt (unit string `VA`). -/
def apparentPowerDK : DimensionedKind :=
  { kind := apparentPower, dim := Iso80000.Part6.EDim.power }
/-- Complex power — the same watt (`VA`). -/
def complexPowerDK : DimensionedKind :=
  { kind := complexPower, dim := Iso80000.Part6.EDim.power }
/-- Reactive power — the same watt (unit string `var`). -/
def reactivePowerDK : DimensionedKind :=
  { kind := reactivePower, dim := Iso80000.Part6.EDim.power }
/-- Non-active power — the same watt (`VA`). -/
def nonActivePowerDK : DimensionedKind :=
  { kind := nonActivePower, dim := Iso80000.Part6.EDim.power }
/-- The power factor is dimension one — by its own defining relation
(`powerFactor_dim_from_powers`). -/
def powerFactorDK : DimensionedKind :=
  { kind := powerFactor, dim := Dim.one }

/-! ## Stage 0 is the catalogue — proved, not asserted -/

example : electricCurrent = Iso80000.Part6.electricCurrent.kind := by decide
example : voltage = Iso80000.Part6.voltage.kind := by decide
example : resistance = Iso80000.Part6.resistance.kind := by decide
example : conductance = Iso80000.Part6.conductance.kind := by decide
example : impedance = Iso80000.Part6.impedance.kind := by decide
example : reactance = Iso80000.Part6.reactance.kind := by decide
example : admittance = Iso80000.Part6.admittance.kind := by decide
example : phaseDifference = Iso80000.Part6.phaseDifference.kind := by decide
example : electricCurrentPhasor = Iso80000.Part6.electricCurrentPhasor.kind := by decide
example : voltagePhasor = Iso80000.Part6.voltagePhasor.kind := by decide
example : power = Iso80000.Part6.power.kind := by decide
example : activePower = Iso80000.Part6.activePower.kind := by decide
example : apparentPower = Iso80000.Part6.apparentPower.kind := by decide
example : powerFactor = Iso80000.Part6.powerFactor.kind := by decide
example : complexPower = Iso80000.Part6.complexPower.kind := by decide
example : reactivePower = Iso80000.Part6.reactivePower.kind := by decide
example : nonActivePower = Iso80000.Part6.nonActivePower.kind := by decide

/-- The catalogue *identifies* 6-46 with 6-51.3 — resistance and the real part of
impedance are one kind, by the standard's own id. Not a defect: the collision that
is not one. -/
example : Iso80000.Part6.resistance.kind = Iso80000.Part6.resistanceAC.kind := by decide

example : electricCurrentDK.dim = Iso80000.Part6.electricCurrent.dim := rfl
example : voltageDK.dim = Iso80000.Part6.voltage.dim := rfl
example : resistanceDK.dim = Iso80000.Part6.resistance.dim := rfl
example : conductanceDK.dim = Iso80000.Part6.conductance.dim := rfl
example : impedanceDK.dim = Iso80000.Part6.impedance.dim := rfl
example : reactanceDK.dim = Iso80000.Part6.reactance.dim := rfl
example : admittanceDK.dim = Iso80000.Part6.admittance.dim := rfl
example : phaseDifferenceDK.dim = Iso80000.Part6.phaseDifference.dim := rfl
example : electricCurrentPhasorDK.dim = Iso80000.Part6.electricCurrentPhasor.dim := rfl
example : voltagePhasorDK.dim = Iso80000.Part6.voltagePhasor.dim := rfl
example : powerDK.dim = Iso80000.Part6.power.dim := rfl
example : activePowerDK.dim = Iso80000.Part6.activePower.dim := rfl
example : apparentPowerDK.dim = Iso80000.Part6.apparentPower.dim := rfl
example : complexPowerDK.dim = Iso80000.Part6.complexPower.dim := rfl
example : reactivePowerDK.dim = Iso80000.Part6.reactivePower.dim := rfl
example : nonActivePowerDK.dim = Iso80000.Part6.nonActivePower.dim := rfl
example : powerFactorDK.dim = Iso80000.Part6.powerFactor.dim := rfl

/-! ## The kind algebra — five consumed, five authored

The consumed edges restate the catalogue's `DefiningRelations` theorems in the
annex's namespace (the proof *is* the catalogue's — the Stage-0 literals are
definitionally the catalogue's kinds); the authored edges are the phasor spellings
the catalogue leaves as remarks. -/

/-- **Ohm's law** (6-46: `R = U/I`) — consumed from the catalogue. -/
theorem voltage_div_electricCurrent :
    QuotientKind voltage electricCurrent resistance :=
  Iso80000.Part6.DefiningRelations.resistance_quot_voltage_current

/-- **Power is voltage times current** (6-45: `P = U·I`) — consumed. -/
theorem voltage_mul_electricCurrent :
    ProductKind voltage electricCurrent power :=
  Iso80000.Part6.DefiningRelations.power_prod_voltage_current

/-- **The power factor** (6-58: `λ = P/S`) — consumed. -/
theorem activePower_div_apparentPower :
    QuotientKind activePower apparentPower powerFactor :=
  Iso80000.Part6.DefiningRelations.powerFactor_quot_active_apparent

/-- **Conductance is the reciprocal of resistance** (6-47) — consumed. -/
theorem resistance_recip_conductance :
    ReciprocalKind resistance conductance :=
  Iso80000.Part6.DefiningRelations.conductance_recip_resistance

/-- **Admittance is the reciprocal of impedance** (6-52.1) — consumed. -/
theorem impedance_recip_admittance :
    ReciprocalKind impedance admittance :=
  Iso80000.Part6.DefiningRelations.admittance_recip_impedance

/-- `Z = Û/Î` — the **complex Ohm's law**: a voltage phasor per current phasor is an
impedance. The catalogue's 6-51.1 remark, as a kind law; `Circuits.lean` registers
it in the operator table at the complex carrier. -/
theorem voltagePhasor_div_electricCurrentPhasor :
    QuotientKind voltagePhasor electricCurrentPhasor impedance :=
  QuotientKind.ofRatio _ _ _

/-- `Û = Z·Î` — the same law, multiplied out: the circuit analyst's direction. -/
theorem impedance_mul_electricCurrentPhasor :
    ProductKind impedance electricCurrentPhasor voltagePhasor :=
  ProductKind.ofRatio _ _ _

/-- `S̲ = Û·Î*` — the **complex power** (6-59): the phasor product lands at the
complex power. Conjugation is carrier-level and kind-preserving (`Circuits.lean`'s
attested crossing); the kind law sees only the product. -/
theorem voltagePhasor_mul_electricCurrentPhasor :
    ProductKind voltagePhasor electricCurrentPhasor complexPower :=
  ProductKind.ofRatio _ _ _

/-- `I = U/R` — Ohm's law solved for the current: the DC direction a circuit file
actually computes. -/
theorem voltage_div_resistance :
    QuotientKind voltage resistance electricCurrent :=
  QuotientKind.ofRatio _ _ _

/-- `P = λ·S` — the power factor scales the apparent power back to the active: the
factor's defining quotient, multiplied out. -/
theorem powerFactor_mul_apparentPower :
    ProductKind powerFactor apparentPower activePower :=
  ProductKind.ofRatio _ _ _

/--
info: dimensional coverage:
[coherent] 1 / impedance → admittance
[coherent] 1 / resistance → conductance
[coherent] activePower / apparentPower → powerFactor
[coherent] impedance · electricCurrentPhasor → voltagePhasor
[coherent] powerFactor · apparentPower → activePower
[coherent] voltage / electricCurrent → resistance
[coherent] voltage / resistance → electricCurrent
[coherent] voltage · electricCurrent → power
[coherent] voltagePhasor / electricCurrentPhasor → impedance
[coherent] voltagePhasor · electricCurrentPhasor → complexPower
10 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage ForPhysLib.Electromagnetism.Annex.Metrology

end ForPhysLib.Electromagnetism.Annex.Metrology
