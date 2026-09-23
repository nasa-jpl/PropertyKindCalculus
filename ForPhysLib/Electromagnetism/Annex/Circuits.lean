/-
# Stage 2/3 — phasor circuits through the operator table

The annex's working layer: the complex Ohm's law and the complex power *registered*
in the operator table at the complex carrier (MR14 — the complexity lives in the
carrier, the kinds are the catalogue's), the AC power lattice with its **refused
join**, and the quadrature constructions that are what the domain licenses instead.

The registrations are the annex's Stage 3: four table entries, each backed by a
Stage-1 edge law. The refusals are pinned beside the acceptances — the same table
answers yes (`Û / Î`, `λ·S`) and no (`Û · Û`, `P + Q`) on one page.
-/

module

public import ForPhysLib.Electromagnetism.Annex.Metrology
meta import ForPhysLib.Electromagnetism.Annex.Metrology
public import PropertyKindCalculus.OperatorTable
meta import PropertyKindCalculus.OperatorTable
public import PropertyKindCalculus.Complex
meta import PropertyKindCalculus.Complex
public import PropertyKindCalculus.QuantityReal
meta import PropertyKindCalculus.QuantityReal
public import Mathlib.Analysis.Real.Sqrt
meta import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace ForPhysLib.Electromagnetism.Annex.Circuits

open PropertyKindCalculus
open ForPhysLib.Electromagnetism.Annex.Kinds
open ForPhysLib.Electromagnetism.Annex.Metrology
open scoped PropertyKindCalculus.OperatorTable

/-- The phasor carrier: PKC's complex pair over the proof carrier `ℝ`. The same
construction serves `Float` for the executable twin (MR14) — the kind layer is
carrier-generic. -/
abbrev Phasor : Type := PropertyKindCalculus.Complex ℝ

/-! ## Stage 3 — the table registrations, each on its Stage-1 law -/

/-- `Û / Î` — the complex Ohm's law, registered. -/
instance : KindDiv voltagePhasor electricCurrentPhasor impedance :=
  ⟨voltagePhasor_div_electricCurrentPhasor⟩

/-- `Z · Î` — the analyst's direction, registered. -/
instance : KindMul impedance electricCurrentPhasor voltagePhasor :=
  ⟨impedance_mul_electricCurrentPhasor⟩

/-- `Û · Î*` — the complex power, registered (conjugation is carrier-level). -/
instance : KindMul voltagePhasor electricCurrentPhasor complexPower :=
  ⟨voltagePhasor_mul_electricCurrentPhasor⟩

/-- `λ · S` — the power factor scaling back to active power, registered. -/
instance : KindMul powerFactor apparentPower activePower :=
  ⟨powerFactor_mul_apparentPower⟩

/-! ## The phasor readings -/

/-- A voltage phasor, read at 6-50. -/
@[kindIngest]
def voltagePhasorQ (u : Phasor) : Quantity voltagePhasor Phasor :=
  .attest "a voltage phasor — the complex amplitude at the catalogue's own item" u

/-- A current phasor, read at 6-49. -/
@[kindIngest]
def currentPhasorQ (i : Phasor) : Quantity electricCurrentPhasor Phasor :=
  .attest "a current phasor" i

/-- `Î*` — complex conjugation: carrier-level, kind-preserving. The complex power's
`Û·Î*` rides the product edge with the conjugate in the current's slot. -/
@[kindCrossing]
def conjQ (i : Quantity electricCurrentPhasor Phasor) :
    Quantity electricCurrentPhasor Phasor :=
  .attest "Î* — conjugation changes the phase's sign, not the kind"
    ⟨i.magnitude.re, -i.magnitude.im⟩

/-- **Impedance as a table quotient**: `Z = Û/Î` elaborates through the registered
entry — `Quantity.div` at the complex carrier, certificate carried. -/
noncomputable def impedanceOf (u : Quantity voltagePhasor Phasor)
    (i : Quantity electricCurrentPhasor Phasor) : Quantity impedance Phasor :=
  u / i

/-- **Complex power as a table product**: `S̲ = Û·Î*`. -/
noncomputable def complexPowerOf (u : Quantity voltagePhasor Phasor)
    (i : Quantity electricCurrentPhasor Phasor) : Quantity complexPower Phasor :=
  u * conjQ i

-- Two voltage phasors have no registered product — `Û·Û` is not a circuit quantity,
-- and the table refuses it at the complex carrier exactly as at ℝ.
#check_failure fun (u v : Quantity voltagePhasor Phasor) => u * v

/-! ## The AC power lattice — the refused join, and the licensed quadrature -/

-- **The refusal.** No `KindJoin` is registered over `PowerEdge`, so `P + Q` never
-- elaborates: comparability (Stage 0's `MutuallyComparable`) did not license the
-- sum, because the domain says the sum is wrong — powers add in quadrature.
#check_failure fun (P : Quantity activePower ℝ) (Q : Quantity reactivePower ℝ) => P + Q

/-- What *is* licensed: `S = √(P² + Q²)` — the quadrature combination, with the law
in its attestation. -/
@[kindCrossing]
noncomputable def apparentFromQ (P : Quantity activePower ℝ)
    (Q : Quantity reactivePower ℝ) : Quantity apparentPower ℝ :=
  .attest "S² = P² + Q² — powers orthogonal, combined in quadrature"
    (Real.sqrt (P.magnitude ^ 2 + Q.magnitude ^ 2))

/-- The catalogue's own residual — 6-61: `Q = √(S² − P²)`, the non-active power. -/
@[kindCrossing]
noncomputable def nonActiveFromQ (S : Quantity apparentPower ℝ)
    (P : Quantity activePower ℝ) : Quantity nonActivePower ℝ :=
  .attest "√(S² − P²) — 6-61's defining residual"
    (Real.sqrt (S.magnitude ^ 2 - P.magnitude ^ 2))

/-- **The power factor through the table**: `λ = P/S` rides the consumed 6-58 edge
(the quotient is registered by its Stage-1 law). -/
noncomputable def powerFactorOf (P : Quantity activePower ℝ)
    (S : Quantity apparentPower ℝ) : Quantity powerFactor ℝ :=
  Quantity.div activePower_div_apparentPower P S

/-- **And back**: `P = λ·S` through the registered product — the round trip the
table licenses while `P + Q` stays unwritable. -/
noncomputable def activeFromFactor (l : Quantity powerFactor ℝ)
    (S : Quantity apparentPower ℝ) : Quantity activePower ℝ :=
  l * S

/-- The round trip erases to the carrier's arithmetic: `λ·S = (P/S)·S` at the
magnitudes. -/
theorem activeFromFactor_powerFactorOf (P : Quantity activePower ℝ)
    (S : Quantity apparentPower ℝ) :
    (activeFromFactor (powerFactorOf P S) S).magnitude
      = P.magnitude / S.magnitude * S.magnitude := rfl

end ForPhysLib.Electromagnetism.Annex.Circuits

