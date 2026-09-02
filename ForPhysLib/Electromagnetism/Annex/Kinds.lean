/-
# Stage 0 — the kind vocabulary of the RF/AC annex

The green-field member of the campaign's second directory (see
[`PLAN.md`](../../PLAN.md)): **PhysLib has no AC or RF physics**, so unlike the
Kinematics chain there is no upstream module to mirror — this annex is capability on
physics the library does not yet have, in the ladder form the mirrored directories
use. Exhibit E built the probes; this directory is their promotion to catalogue
rigor.

**Every kind is a lookup — zero mints.** The RF/AC vocabulary is *entirely* in
IEC 80000-6: impedance and its family (6-51.1/6-51.4), admittance (6-52.1), the
phasors (6-49/6-50), the phase difference (6-48), and the whole AC power family
(6-56 … 6-61) with the examination principles that individuate it. The Kinematics
chain minted eight kinds because the standard does not catalogue frame- or
gauge-relative readings; the annex mints none because AC circuit practice *is* the
standard's home ground. That asymmetry is the finding.

**The collisions are the densest in the campaign.** Two kinds at the ohm (impedance,
reactance — and the catalogue *identifies* 6-46 resistance with 6-51.3, one id, one
kind), six kinds at the watt (power and its five species, three coherent-unit strings:
`W`, `VA`, `var`), two at dimension one (phase difference, power factor), and each
phasor at its base quantity's dimension. Every separation below is a `decide`; none
is dimensional.

**The refused join is the curation contrast.** The pilot's energy family registers
`T + V` at its join; the AC power family registers *no* join sum, because `P + Q` is
the domain error — powers are orthogonal, `S² = P² + Q²` (`Circuits.lean` pins both
sides). The same table saying yes and no on the same page is the proof that the join
table is curation, not a loophole.
-/

import PropertyKindCalculus

namespace ForPhysLib.Electromagnetism.Annex.Kinds

open PropertyKindCalculus

/-! ## The lookups — IEC 80000-6, verbatim -/

/-- Electric current — item 6-1 (`I`, A): the DC/RMS current, the phasor's root. -/
def electricCurrent : KindOfProperty := { id := "electric current", scale := .ratio }

/-- Voltage — item 6-11.3 (`U`, V): the DC/RMS voltage. -/
def voltage : KindOfProperty := { id := "voltage", scale := .ratio }

/-- Resistance — item 6-46 (`R`, Ω): Ohm's law's quotient. The catalogue gives
6-51.3 (the real part of impedance) the *same* id — one kind, deliberately. -/
def resistance : KindOfProperty := { id := "resistance", scale := .ratio }

/-- Conductance — item 6-47 (`G`, S): resistance's reciprocal. -/
def conductance : KindOfProperty := { id := "conductance", scale := .ratio }

/-- Impedance — item 6-51.1 (`Z`, Ω): the phasor quotient `U/I` — complex-carried
below, the ohm-dimensioned kind that is *not* resistance. -/
def impedance : KindOfProperty := { id := "impedance", scale := .ratio }

/-- Reactance — item 6-51.4 (`X`, Ω): the imaginary part of impedance — the third
ohm-dimensioned reading. -/
def reactance : KindOfProperty := { id := "reactance", scale := .ratio }

/-- Admittance — item 6-52.1 (`Y`, S): impedance's reciprocal. -/
def admittance : KindOfProperty := { id := "admittance", scale := .ratio }

/-- Phase difference — item 6-48 (`φ`, rad): dimension one, and not a power factor
(the other dimension-one kind here); `cos φ` relates them at the carrier, not the
table. -/
def phaseDifference : KindOfProperty := { id := "phase difference", scale := .ratio }

/-- Electric current phasor — item 6-49 (`Î`, A): the complex-valued current — the
catalogue's own item, not a convenience; the carrier is where the complexity lives
(MR14). -/
def electricCurrentPhasor : KindOfProperty :=
  { id := "electric current phasor", scale := .ratio }

/-- Voltage phasor — item 6-50 (`Û`, V). -/
def voltagePhasor : KindOfProperty := { id := "voltage phasor", scale := .ratio }

/-- Power — item 6-45 (`P`, W): the broad genus the five AC species specialize. -/
def power : KindOfProperty := { id := "power", scale := .ratio }

/-- Active power — item 6-56 (`P`, W): the time-averaged real component. The
examination principle is the catalogue's own — the species are individuated by *how
they are examined*. -/
def activePower : KindOfProperty :=
  { id := "active power", scale := .ratio, examPrinciple := some "time-averaged-real" }

/-- Apparent power — item 6-57 (`S`, VA): RMS voltage times RMS current. -/
def apparentPower : KindOfProperty :=
  { id := "apparent power", scale := .ratio, examPrinciple := some "rms-product" }

/-- Power factor — item 6-58 (`λ`, 1): active over apparent — dimension one by its
own defining relation. -/
def powerFactor : KindOfProperty := { id := "power factor", scale := .ratio }

/-- Complex power — item 6-59 (`S̲`, VA): `P + jQ`. -/
def complexPower : KindOfProperty :=
  { id := "complex power", scale := .ratio, examPrinciple := some "complex-P-jQ" }

/-- Reactive power — item 6-60 (`Q`, var): the imaginary component. -/
def reactivePower : KindOfProperty :=
  { id := "reactive power", scale := .ratio, examPrinciple := some "reactive-imaginary" }

/-- Non-active power — item 6-61 (`Q`, VA): the residual `√(S² − P²)`. -/
def nonActivePower : KindOfProperty :=
  { id := "non-active power", scale := .ratio, examPrinciple := some "non-active-residual" }

/-! ## Distinctness — the densest collisions in the campaign -/

/-- **Impedance is not resistance** — one ohm, two kinds: the complex quotient vs
the real one. -/
theorem impedance_ne_resistance : impedance ≠ resistance := by decide

/-- **Reactance is not resistance** — same ohm again; the imaginary part is not the
real part. -/
theorem reactance_ne_resistance : reactance ≠ resistance := by decide

/-- **Reactance is not impedance** — a part is not the whole, at one dimension. -/
theorem reactance_ne_impedance : reactance ≠ impedance := by decide

/-- **Admittance is not conductance** — the siemens pair, same separation. -/
theorem admittance_ne_conductance : admittance ≠ conductance := by decide

/-- **A phasor is not its RMS quantity** — same volt; the phasor is examined as a
complex amplitude. -/
theorem voltagePhasor_ne_voltage : voltagePhasor ≠ voltage := by decide

/-- The current pair, likewise. -/
theorem electricCurrentPhasor_ne_electricCurrent :
    electricCurrentPhasor ≠ electricCurrent := by decide

/-- **Active is not reactive** — one watt-dimension, individuated by examination
principle: the in-phase mean vs the quadrature component. -/
theorem activePower_ne_reactivePower : activePower ≠ reactivePower := by decide

/-- **Apparent is not active** — `S` bounds `P`; they are not the same reading. -/
theorem apparentPower_ne_activePower : apparentPower ≠ activePower := by decide

/-- **Apparent is not complex** — `|S̲|` vs `S̲`: the magnitude reading and the
complex reading are distinct kinds at one dimension. -/
theorem apparentPower_ne_complexPower : apparentPower ≠ complexPower := by decide

/-- **No species is its genus** — the specialization is proper. -/
theorem activePower_ne_power : activePower ≠ power := by decide

/-- **The two dimension-one kinds are two kinds** — a phase angle is not a power
factor, though `λ = cos φ` links their magnitudes. -/
theorem phaseDifference_ne_powerFactor : phaseDifference ≠ powerFactor := by decide

/-! ## The specialization lattice — five species, one genus, no join

The catalogue's own placement: 6-45 is "the broad genus" of the AC power family.
What is deliberately **absent** is any `KindJoin` over these edges: `P + Q` has no
licensed sum (`Circuits.lean` pins the refusal), because the domain adds powers in
quadrature. Compare the pilot's energy family, which registers its join — the same
machinery, curated in the opposite direction. -/

/-- The AC power family's direct-parent edges — the five species of 6-45. -/
inductive PowerEdge : KindOfProperty → KindOfProperty → Prop
  /-- Active power is a power. -/
  | active : PowerEdge activePower power
  /-- Apparent power is a power. -/
  | apparent : PowerEdge apparentPower power
  /-- Complex power is a power. -/
  | complexP : PowerEdge complexPower power
  /-- Reactive power is a power. -/
  | reactive : PowerEdge reactivePower power
  /-- Non-active power is a power. -/
  | nonActive : PowerEdge nonActivePower power

/-- Active and reactive power are comparable *as powers* while staying two kinds —
comparability without identity, and without a licensed sum. -/
theorem activePower_comparable_reactivePower :
    MutuallyComparable PowerEdge activePower reactivePower :=
  ⟨power, .of_edge .active, .of_edge .reactive⟩

/-- Apparent and active likewise — the pair `S² = P² + Q²` relates in quadrature. -/
theorem apparentPower_comparable_activePower :
    MutuallyComparable PowerEdge apparentPower activePower :=
  ⟨power, .of_edge .apparent, .of_edge .active⟩

end ForPhysLib.Electromagnetism.Annex.Kinds
