/-
# Stage 3 — the operator table of `Physlib/QuantumMechanics/HarmonicOscillator`

The fourth rung of [the adoption ladder](../../PLAN.md#stage-3-the-operator-table) for
the pilot directory: the kind algebra registered once as `KindMul`/`KindDiv` instances,
so that with `open scoped PropertyKindCalculus.OperatorTable` the ordinary `*` and `/`
elaborate through the table — and an unregistered pair **fails to elaborate**.

**Three entries predate this file, and that is the pilot's own history.** The
feasibility probe needed the table before the ladder existed: `kind_algebra` registered
the two radicand-chain quotients and F4 registered `ℏ·ω → energy` in
`Feasibility.lean`, which is why `xiSqQd` and `modeEnergyQ` already elaborate through
`*` and `/`. This file registers the directory's remaining seven edges, each backed by
the Stage-1 law it re-states — the same `#kind_dimensional_coverage` discipline then
re-pins over the *operator* registrations, so the table cannot drift from the
dimensional audit.

**Instance heads are spelled at the kinds the quantities carry.** The directory has two
spellings of each kind — Feasibility's catalogue lookups (`energyK`, `lengthK`) and
Stage 0's literals (`mechanicalEnergy`, `characteristicLength`) — proved one vocabulary
by `rfl` in `Kinded.lean`. That equality is *definitional*, not syntactic, and instance
search does not unfold plain `def`s: a table entry is found only at the spelling its
head is written in. So each head below uses the spelling of the quantities that will
consume it (`xiQd` is at `lengthK`, so `ξ·ξ` registers at `lengthK`), and the Stage-1
law backs it across the `rfl` bridge.

**The table is curated per kind, not per dimension.** Energy · energy is registered;
mechanical energy · kinetic energy is not — same dimension `M²·L⁴·T⁻⁴`, no sanctioned
product — and the probe below shows it refused. Dimensional admissibility is necessary;
the registration is the design decision.
-/

module

public import ForPhysLib.QuantumMechanics.HarmonicOscillator.Measurand
public import PropertyKindCalculus.DimensionalCoverage

@[expose] public section

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator.Operators

open PropertyKindCalculus Constants
open ForPhysLib.QuantumMechanics.HarmonicOscillator
open ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinds
open ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded
open scoped PropertyKindCalculus.OperatorTable

local notation "PhysHO" => _root_.QuantumMechanics.HarmonicOscillator

variable {d : ℕ}

/-! ## The registrations — seven edges, each on its Stage-1 law -/

/-- `ξ · ξ → ξ² radicand` — the root's re-entry (PhysLib's own `ξ_sq`), at the kinds
`xiQd` carries. -/
instance : KindMul lengthK lengthK xiSqK :=
  ⟨Metrology.characteristicLength_mul_self⟩

/-- `energy · energy → energy squared` — the variance's kind, at the kinds the
Hamiltonian measurand's σ carries. -/
instance : KindMul energyK energyK energySquared :=
  ⟨Metrology.mechanicalEnergy_mul_self⟩

/-- `length / ξ → dimensionless coordinate` — the Hermite argument `x i / Q.ξ i`,
divisor at `xiQd`'s kind. -/
instance : KindDiv length lengthK dimensionlessCoordinate :=
  ⟨Metrology.length_div_characteristicLength⟩

/-- `p · p → momentum squared` — the squared-momentum law, for scalar consumers (the
operator `p̂` composes through `LinearPMap` where no table sees it — F1d's tier). -/
instance : KindMul momentum momentum momentumSquared :=
  ⟨Metrology.momentum_mul_self⟩

/-- `p² / mass → kinetic energy` — the law behind `kineticOperator = (2m)⁻¹ • p̂²`. -/
instance : KindDiv momentumSquared mass kineticEnergy :=
  ⟨Metrology.momentumSquared_div_mass⟩

/-- `length · length → length squared` — the potential's `x²`, and a position
variance's radicand. -/
instance : KindMul length length xiSqK :=
  ⟨Metrology.length_mul_length⟩

/-- `length · momentum → action` — the uncertainty product, landing at ℏ's own kind so
`σ_x · σ_p` and `ℏ/2` are same-kind comparable. -/
instance : KindMul length momentum actionK :=
  ⟨Metrology.length_mul_momentum⟩

/-! ## The operator idiom — `*` and `/` through the table (MR28) -/

/-- The kinded ξ squares straight back to the radicand; the result kind is *computed*
by the table (an `outParam`), not annotated. -/
noncomputable def xiSqFromTable (Q : PhysHO d) (i : Fin d) : Quantity xiSqK ℝ :=
  xiQd Q i * xiQd Q i

/-- **PhysLib's own `ξ_sq` closes the kinded goal**: the table product's magnitude is
the product of the magnitudes (definitionally), the magnitudes are the erasure
(`xiQd_magnitude`), and the rest is the source's lemma verbatim. -/
theorem xiSqFromTable_magnitude (Q : PhysHO d) (i : Fin d) :
    (xiSqFromTable Q i).magnitude = (ℏ : ℝ) / (Q.m * Q.ω i) := by
  show (xiQd Q i).magnitude * (xiQd Q i).magnitude = _
  rw [xiQd_magnitude, ← pow_two]
  exact Q.ξ_sq i

/-- The Hamiltonian measurand's σ squares back to the variance's kind — the round trip
`Measurand.lean`'s attested root exists to license, now one `*`. -/
noncomputable example (Q : PhysHO d) (hsa : IsSelfAdjoint Q.hamiltonian)
    (ψ : (hamiltonianOpQ Q).magnitude.domain) : Quantity energySquared ℝ :=
  (hamiltonianMeasurand Q hsa).sigma ψ * (hamiltonianMeasurand Q hsa).sigma ψ

/-- The Hermite argument: a coordinate over the kinded ξ is a dimensionless
coordinate, through the table's quotient entry. -/
noncomputable example (x : Quantity length ℝ) (Q : PhysHO d) (i : Fin d) :
    Quantity dimensionlessCoordinate ℝ := x / xiQd Q i

/-- An uncertainty product lands at action — same-kind comparable with `ℏ/2`. -/
noncomputable example (σx : Quantity length ℝ) (σp : Quantity momentum ℝ) :
    Quantity actionK ℝ := σx * σp

/-- The kinetic-energy law, consumable by a scalar consumer. -/
noncomputable example (psq : Quantity momentumSquared ℝ) (m : Quantity mass ℝ) :
    Quantity kineticEnergy ℝ := psq / m

/-- The probe-era entry is live: `ℏ · ωᵢ` is an energy (F4's registration). -/
noncomputable example (Q : PhysHO d) (i : Fin d) : Quantity energyK ℝ :=
  hbarQ * ωQ Q i

/-! ## What the table refuses -/

-- Refused: mechanical energy · kinetic energy — dimensionally an energy squared, but
-- the table is curated per kind and only energy · *energy* was sanctioned as the
-- variance's edge. Necessity vs design.
#check_failure fun (E : Quantity energyK ℝ) (T : Quantity kineticEnergyK ℝ) => E * T

-- Refused: an eigenvalue times a characteristic length — (energy, length) is no entry.
#check_failure fun (Q : PhysHO 3) (n : Fin 3 → ℕ) (i : Fin 3) =>
  eigenEnergyQ Q n * xiQd Q i

-- Refused twice over: `T̂ * V̂` at the operator carrier. (kinetic, potential) is no
-- table entry — and the carrier itself has no `Mul`/`ScalarCarrier` for the table's
-- `*` to ride: operators compose through `LinearPMap.comp`, which no table sees
-- (F1d's tier). The table serves the directory's scalar consumers.
#check_failure fun (Q : PhysHO 3) => kineticOpQ Q * potentialOpQ Q

/-! ## The dimensional audit, re-pinned over the operator registrations -/

/--
info: dimensional coverage:
[coherent] [table] energyK · energyK → energySquared
[coherent] [table] length / lengthK → dimensionlessCoordinate
[coherent] [table] length · length → xiSqK
[coherent] [table] length · momentum → actionK
[coherent] [table] lengthK · lengthK → xiSqK
[coherent] [table] momentum · momentum → momentumSquared
[coherent] [table] momentumSquared / mass → kineticEnergy
7 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage ForPhysLib.QuantumMechanics.HarmonicOscillator.Operators

end ForPhysLib.QuantumMechanics.HarmonicOscillator.Operators

