/-
# The QM/HO pilot — feasibility, before the ladder

**Source.** `Physlib/QuantumMechanics/HarmonicOscillator/{Basic,Eigenstates}.lean` and
`OneDimension/Basic.lean`, imported and probed directly. The campaign's pilot directory —
see `PLAN.md`, "The three-directory campaign".

Four capability questions, each of which could force a core change, answered as build
artifacts before any ladder stage is climbed:

* **F1 — the operator carrier.** The quantum oscillator's quantities are partial linear
  operators (`Q.HS →ₗ.[ℂ] Q.HS`). `Quantity` stands up at that carrier: `T̂` and `V̂`
  at kinetic/potential-energy kinds, `T̂ + V̂` through the curated join landing at
  energy — definitionally PhysLib's `hamiltonian` — and `T̂ + p̂²` refused. The carrier
  vocabulary is one upstream constructor (`Carrier.ofZeroAdd`); the `(2·m)⁻¹ • p̂²`
  construction is recorded as the named crossing it is: a dimensionful scalar riding
  Mathlib's `SMul` where no table sees it (the MR30 tier, at an operator carrier).
* **F2 — half-power dimensions.** The library spells the characteristic length both
  ways: root-first in the `d`-dimensional file (`ξ i = √ℏ/(√m·√ωᵢ)` — intermediates of
  half-integer dimension, which **no kind in this vocabulary names**) and radicand-first
  in the 1D file (`ξ = √(ℏ/(m·ω))` — a two-edge `kind_algebra` chain to length², then
  one attested root). Only the radicand-first spelling survives kinding, and PhysLib's
  own `ξ_sq` proves the respelling in one line.
* **F3 — the SI numeral.** `Constants.ℏ = ⟨1.054571817e-34, _⟩`: the unit system (J·s)
  lives in docstring prose, the QM twin of Exhibit E's `(c := 1)` — pinned, then kinded
  as one attested action quantity. (The 1D oscillator's docstring promises "three real
  parameters … a value of Planck's constant `ℏ`"; the structure carries two fields, and
  ℏ arrives from the global constant — a prose finding, recorded here.)
* **F4 — the eigenvalues.** `ℏ ωᵢ (nᵢ + ½)` kinded per mode, and the mode sum proved
  equal to PhysLib's `eigenEnergy`. The sum is taken at magnitudes: aggregating a mode
  *family* at the kind layer is Stage-2 work (`Extensive`'s licensed aggregation).

Held for the ladder: `ξEquiv` (nondimensionalization as a kind-level event), the
eigenfunctions, and the `LadderOperators` stub (green-field co-authoring; `a`, `a†`, `N`
are dimensionless).
-/

import Physlib.QuantumMechanics.HarmonicOscillator.Basic
import Physlib.QuantumMechanics.HarmonicOscillator.Eigenstates
import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic
import PropertyKindCalculus.KindAlgebra
import PropertyKindCalculus.SpecializationLift
import PropertyKindCalculus.QuantityReal

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator

open PropertyKindCalculus Real Constants

-- PhysLib's oscillators and Hilbert space, qualified past this file's own namespace.
local notation "PhysHO" => _root_.QuantumMechanics.HarmonicOscillator
local notation "PhysHO1" => _root_.QuantumMechanics.OneDimension.HarmonicOscillator
local notation "HSpace" => _root_.QuantumMechanics.SpaceDHilbertSpace

/-! ## The kind vocabulary — Stage-0 scale, probe-local

Base kinds by hand, the derived radicand chain by `kind_algebra`, the energy family with
its curated join. The ladder's `Kinds.lean` will restate these against `Iso80000`; the
probe only needs them to exist. -/

/-- Action — ℏ's kind. -/
def actionK : KindOfProperty := { id := "action", scale := .ratio }

/-- Mass — the particle's `m`. -/
def massK : KindOfProperty := { id := "mass", scale := .ratio }

/-- Angular frequency — the oscillator's `ω`. -/
def angularFrequencyK : KindOfProperty := { id := "angular frequency", scale := .ratio }

/-- The characteristic length `ξ`. -/
def lengthK : KindOfProperty := { id := "characteristic length", scale := .ratio }

kind_algebra
  specificActionK : "action per mass"                  := actionK / massK
  xiSqK           : "length squared — the ξ² radicand" := specificActionK / angularFrequencyK

/-- Kinetic energy — `T̂`'s kind. -/
def kineticEnergyK : KindOfProperty :=
  { id := "kinetic energy", scale := .ratio, examPrinciple := some "by motion" }

/-- Potential energy — `V̂`'s kind. -/
def potentialEnergyK : KindOfProperty :=
  { id := "potential energy", scale := .ratio, examPrinciple := some "by configuration" }

/-- Energy — the join, and where the eigenvalues land. -/
def energyK : KindOfProperty := { id := "energy", scale := .ratio }

/-- Momentum squared — `p̂²`'s kind, deliberately *not* joined to the energy family. -/
def momentumSqK : KindOfProperty := { id := "momentum squared", scale := .ratio }

/-- The energy family's edges. -/
inductive EnergyEdge : KindOfProperty → KindOfProperty → Prop
  /-- Kinetic energy is an energy. -/
  | kinetic : EnergyEdge kineticEnergyK energyK
  /-- Potential energy is an energy. -/
  | potential : EnergyEdge potentialEnergyK energyK

/-- `T + V` is licensed at the join. -/
instance : KindJoin EnergyEdge kineticEnergyK potentialEnergyK energyK :=
  ⟨.of_edge .kinetic, .of_edge .potential, .ofScale⟩

/-- `ℏ · ω` is an energy — the eigenvalue factorization. -/
instance : KindMul actionK angularFrequencyK energyK := ⟨ProductKind.ofRatio _ _ _⟩

open scoped PropertyKindCalculus.OperatorTable

/-- A dimensionless numeral scales a quantity without changing its kind — the `nᵢ + ½`
below. Same honesty as Exhibit C's copy of this instance: the action is the
Mathlib-interface tier (MR30) — a dimensioned magnitude smuggled in as a bare numeral is
what the audit measures, not what the type prevents. -/
scoped instance {k : KindOfProperty} {R : Type} [Mul R] : SMul R (Quantity k R) :=
  ⟨fun c q => ⟨c * q.magnitude⟩⟩

/-! ## F1 — the operator carrier -/

/-- The operator type joins the carrier vocabulary through the upstream constructor —
`Zero` and `Add` are Mathlib's `LinearPMap` instances (the sum lives on the intersection
of domains), and that is all `Quantity` asks of a carrier. -/
noncomputable instance {d : ℕ} : Carrier (HSpace d →ₗ.[ℂ] HSpace d) :=
  Carrier.ofZeroAdd _

variable {d : ℕ}

/-- `T̂` at its kind, at the operator carrier. -/
noncomputable def kineticOpQ (Q : PhysHO d) :
    Quantity kineticEnergyK (Q.HS →ₗ.[ℂ] Q.HS) :=
  .attest "reading of PhysLib's kineticOperator" Q.kineticOperator

/-- `V̂` at its kind. -/
noncomputable def potentialOpQ (Q : PhysHO d) :
    Quantity potentialEnergyK (Q.HS →ₗ.[ℂ] Q.HS) :=
  .attest "reading of PhysLib's potentialOperator" Q.potentialOperator

/-- `p̂²` at its kind. -/
noncomputable def momentumSqOpQ (Q : PhysHO d) :
    Quantity momentumSqK (Q.HS →ₗ.[ℂ] Q.HS) :=
  .attest "reading of PhysLib's momentumSqOperator"
    _root_.QuantumMechanics.momentumSqOperator

/-- **F1a.** `T̂ + V̂` through the curated join, at the operator carrier: `KindJoin` and
`Quantity.addAt` are carrier-generic, so the same two-entry curation that licensed the
classical `T + V` licenses the operator sum. -/
noncomputable def hamiltonianOpQ (Q : PhysHO d) : Quantity energyK (Q.HS →ₗ.[ℂ] Q.HS) :=
  kineticOpQ Q + potentialOpQ Q

/-- **F1b.** The join sum *is* PhysLib's `hamiltonian` — definitionally: `Carrier.add` at
this carrier is `LinearPMap`'s `+`, and `hamiltonian` is defined as that sum. -/
theorem hamiltonianOpQ_eq (Q : PhysHO d) :
    (hamiltonianOpQ Q).magnitude = Q.hamiltonian := rfl

/- **F1c.** `T̂ + p̂²` is refused: `(kinetic, momentum²)` is no entry of the join table,
and heterogeneous kinds have no other `+`. `p̂²` is not an energy until `(2m)⁻¹` acts. -/
#check_failure fun (Q : PhysHO 3) => kineticOpQ Q + momentumSqOpQ Q

/-- **F1d — the named crossing.** PhysLib builds `T̂` as `(2·m)⁻¹ • p̂²`: a dimensionful
scalar rides Mathlib's `SMul`, which no kind table sees — the MR30 Mathlib-interface
tier, recurring at an operator carrier. The kinded spelling attests the crossing and is
definitionally PhysLib's `kineticOperator`. -/
noncomputable def kineticFromMomentumQ (Q : PhysHO d) :
    Quantity kineticEnergyK (Q.HS →ₗ.[ℂ] Q.HS) :=
  .attest "(2·mass)⁻¹ carries momentum² to kinetic energy across Mathlib's SMul"
    ((2 * Q.m)⁻¹ • (momentumSqOpQ Q).magnitude)

theorem kineticFromMomentumQ_eq (Q : PhysHO d) :
    (kineticFromMomentumQ Q).magnitude = Q.kineticOperator := rfl

/-- Same-kind sums also live at the operator carrier, through the ordinary homogeneous
instance — nothing about the carrier is special-cased. -/
noncomputable example (Q : PhysHO d) : Quantity kineticEnergyK (Q.HS →ₗ.[ℂ] Q.HS) :=
  kineticOpQ Q + kineticOpQ Q

/-! ## F2 — half-power dimensions and the two spellings of ξ -/

/-- ℏ as an action quantity — one attestation naming what the source's type does not
carry (F3 pins what the numeral commits to). -/
def hbarQ : Quantity actionK ℝ :=
  .attest "Constants.ℏ — SI numeral; the J·s commitment lives in docstring prose" (ℏ : ℝ)

/-- The 1D mass, read at its kind. -/
def mQ (Q₁ : PhysHO1) : Quantity massK ℝ := .attest "PhysLib's bare ℝ field m" Q₁.m

/-- The 1D angular frequency. -/
def ωQ1 (Q₁ : PhysHO1) : Quantity angularFrequencyK ℝ :=
  .attest "PhysLib's bare ℝ field ω" Q₁.ω

/-- **F2a.** The radicand `ℏ/(m·ω)`, built through the table: two registered edges,
landing at length². -/
noncomputable def xiSqQ (Q₁ : PhysHO1) : Quantity xiSqK ℝ := hbarQ / mQ Q₁ / ωQ1 Q₁

theorem xiSqQ_eq (Q₁ : PhysHO1) : (xiSqQ Q₁).magnitude = (ℏ : ℝ) / (Q₁.m * Q₁.ω) :=
  div_div _ _ _

/-- **F2b.** One attested root lands the length: kinded `ξ`, equal to PhysLib's own. -/
noncomputable def xiQ (Q₁ : PhysHO1) : Quantity lengthK ℝ :=
  .attest "the square root of the registered ξ² chain — roots are not a kind operation"
    (√((xiSqQ Q₁).magnitude))

theorem xiQ_eq (Q₁ : PhysHO1) : (xiQ Q₁).magnitude = Q₁.ξ := by
  show √((xiSqQ Q₁).magnitude) = Q₁.ξ
  rw [xiSqQ_eq]; rfl

/-- **F2c — the finding.** The `d`-dimensional file spells the same length *root-first*:
`ξ i = √ℏ / (√m · √ωᵢ)`, whose intermediates `√ℏ`, `√m`, `√ωᵢ` carry half-integer
dimension and are named by **no kind in this vocabulary** — half-power kinds are
deliberately absent. The radicand-first respelling is provable from PhysLib's own `ξ_sq`
in one line, and the 1D file already writes it that way: only one of the library's two
spellings survives kinding, and it is the one PhysLib's own lemma set favors. -/
theorem xi_radicand_first (Q : PhysHO d) (i : Fin d) :
    Q.ξ i = √((ℏ : ℝ) / (Q.m * Q.ω i)) := by
  rw [← Q.ξ_sq i, Real.sqrt_sq (Q.ξ_nonneg i)]

/-! ## F3 — the SI numeral -/

/- The unit commitment, pinned: `ℏ`'s magnitude *is* the J·s numeral — the type says
"positive real"; everything else is prose. The QM twin of Exhibit E's `(c := 1)`. -/
example : (ℏ : ℝ) = 1.054571817e-34 := rfl

/-! ## F4 — the eigenvalues -/

/-- The `d`-dimensional mode frequency at its kind. -/
def ωQ (Q : PhysHO d) (i : Fin d) : Quantity angularFrequencyK ℝ :=
  .attest "PhysLib's bare ℝ family ω i" (Q.ω i)

/-- **F4a.** The mode energy `ℏ ωᵢ (nᵢ + ½)`: `ℏ · ωᵢ` through the registered
action × angular-frequency entry, the dimensionless occupation on the scoped numeral
action. -/
noncomputable def modeEnergyQ (Q : PhysHO d) (n : Fin d → ℕ) (i : Fin d) :
    Quantity energyK ℝ :=
  ((n i : ℝ) + 1 / 2) • (hbarQ * ωQ Q i)

theorem modeEnergyQ_magnitude (Q : PhysHO d) (n : Fin d → ℕ) (i : Fin d) :
    (modeEnergyQ Q n i).magnitude = ((n i : ℝ) + 1 / 2) * ((ℏ : ℝ) * Q.ω i) := rfl

/-- **F4b.** The kinded modes sum to PhysLib's `eigenEnergy`. The sum is taken at
magnitudes: aggregating a mode *family* at the kind layer is Stage-2 work
(`Extensive`'s licensed aggregation), and the probe does not pretend otherwise. -/
theorem eigenEnergy_eq_sum_modes (Q : PhysHO d) (n : Fin d → ℕ) :
    Q.eigenEnergy n = ∑ i, (modeEnergyQ Q n i).magnitude := by
  rw [Q.eigenEnergy_eq]
  exact Finset.sum_congr rfl fun i _ => by rw [modeEnergyQ_magnitude]; ring

/-! ## The substrate, once

The directory rests on the same bare-real substrate as the classical files — one probe
suffices; Exhibits A–C carry the catalogue. -/

/-- A characteristic length plus a mass elaborates at the source's types… -/
noncomputable example (Q₁ : PhysHO1) : ℝ := Q₁.ξ + Q₁.m

/- …and is refused at the kinded ones: `(length, mass)` joins nothing. -/
#check_failure fun (Q₁ : PhysHO1) => xiQ Q₁ + mQ Q₁

end ForPhysLib.QuantumMechanics.HarmonicOscillator
