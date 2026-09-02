/-
# Stage 4 — audits and the API map, for `Physlib/QuantumMechanics/HarmonicOscillator`

The top rung of [the adoption ladder](../../PLAN.md#stage-4-audits-and-the-api-map) for
the pilot directory: the whole directory's kinded surface put under CI — probe files
included, because the probe's quantities *are* directory mints and each now carries the
tier that sanctions it. Five gates, each in the discipline its command enforces:

  * `#kind_boundary_audit` **pinned** over the full directory namespace: twenty
    boundary sites — every mint, attestation and erasure from `Feasibility.lean`'s
    catalogue readings to `Kinded.lean`'s crossings — each with its tier. A new
    untagged site breaks the pin.
  * `#kind_boundary_clean` and `#kind_mint_ratchet` **silent**: they throw on violation
    and print nothing on a clean scope, so neither can be re-blessed by re-pinning. The
    ratchet is why `numeralSMul`'s mint is *attested*, not raw: `[carrierVocab]` keeps
    an empty raw column.
  * `#kind_unkinded` over two declared contracts: the *interior* gated empty, and the
    *ingest boundary* measured — fifteen naked positions, all of them the oscillator
    structure, its occupation labels, a coordinate index, its Hilbert space, its
    operator domains, or the one emitted `ℝ`:
    exactly the Mathlib/PhysLib-interface tier, unkinded by design, counted rather
    than hidden. **The gate placed one crossing during authoring**: `ξEquiv`'s kinded
    reading consumes the raw oscillator (the `ξᵢ` scale factors ride inside `Q`), so
    `positionOfDimensionless` is boundary, not interior — the interior contract
    refused it, and that refusal is the stage working.
  * `#kind_dimensional_clean` **silent** over the whole directory: every edge — the
    Stage-1 laws, the probe-era table entries, Stage 3's registrations, and the
    aggregation license `energyDiff` (a `±` edge) — dimensionally coherent in
    PhysLib's dimension group, from one command no file-local pin can drift from.

The API-map half of the stage is the `checked_by:` field. This directory has no
`API-map.yaml` upstream — its requirement ledger is the `TODO` command list opening
`Eigenstates.lean` — so the proposed delta beside this file
(`HarmonicOscillator.checked_by.yaml`) keys on those TODO texts, pointing each at the
ForPhysLib module whose build now checks the claim or holds its statement ready.
-/

import ForPhysLib.QuantumMechanics.HarmonicOscillator.Operators
import ForPhysLib.QuantumMechanics.HarmonicOscillator.Heisenberg
import ForPhysLib.QuantumMechanics.HarmonicOscillator.AngularMomentum
import ForPhysLib.QuantumMechanics.HarmonicOscillator.Degeneracy
import ForPhysLib.QuantumMechanics.HarmonicOscillator.LadderOperators
import PropertyKindCalculus.BoundaryAudit
import PropertyKindCalculus.KindLedger
import PropertyKindCalculus.DimensionalCoverage

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator.Audits

open PropertyKindCalculus

/-! ## The boundary audit, pinned -/

/--
info: boundary audit:
[carrierVocab] ForPhysLib.QuantumMechanics.HarmonicOscillator.numeralSMul — attests: (kind-parametric) ‹a dimensionless numeral scales; the kind is unchanged›
[kindConst] ForPhysLib.QuantumMechanics.HarmonicOscillator.hbarQ — attests: actionK ‹Constants.ℏ — SI numeral; the J·s commitment lives in docstring prose›
[kindCrossing] ForPhysLib.QuantumMechanics.HarmonicOscillator.AngularMomentum.angularMomentumReading — attests: Kinds.angularMomentum ‹m·ℏ read at 4-11 — the J·s collision crossed on purpose›
[kindCrossing] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.energySMul — erases (emission-only)
[kindCrossing] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.positionOfDimensionless — attests: Kinds.length ‹ξEquiv — the per-component ξᵢ· multiplication rides the equiv unseen›
[kindCrossing] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.totalProbabilityQ — attests: Kinds.probability ‹∫ρ dV — the density · volume edge aggregated by Mathlib's ∫, unseen›
[kindCrossing] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.xiRoot — attests: lengthK ‹the square root of the registered ξ² chain — roots are not a kind operation›
[kindCrossing] ForPhysLib.QuantumMechanics.HarmonicOscillator.kineticFromMomentumQ — attests: kineticEnergyK ‹(2·mass)⁻¹ carries momentum² to kinetic energy across Mathlib's SMul›
[kindEmission] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.rawEigenEnergy — erases (emission-only)
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.Heisenberg.momentumSigmaQ — attests: Kinds.momentum ‹standard deviation of PhysLib's momentumOperator›
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.Heisenberg.positionOpQ — attests: Kinds.length ‹reading of PhysLib's positionOperator›
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.bornDensityQ — mints: Kinds.bornDensity
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.mQd — mints: massK
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.occupationQ — mints: Kinds.quantumNumber
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.Ladder.numberOpQ — attests: Kinds.quantumNumber ‹a†ᵢaᵢ — the occupation observable at its kind›
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.kineticOpQ — attests: kineticEnergyK ‹reading of PhysLib's kineticOperator›
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.mQ — attests: massK ‹PhysLib's bare ℝ field m›
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.momentumSqOpQ — attests: momentumSqK ‹reading of PhysLib's momentumSqOperator›
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.potentialOpQ — attests: potentialEnergyK ‹reading of PhysLib's potentialOperator›
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.xiQ — attests: lengthK ‹the square root of the registered ξ² chain — roots are not a kind operation›
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.ωQ — attests: angularFrequencyK ‹PhysLib's bare ℝ family ω i›
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.ωQ1 — attests: angularFrequencyK ‹PhysLib's bare ℝ field ω›
22 boundary site(s), all tagged — clean
-/
#guard_msgs (whitespace := lax) in
#kind_boundary_audit ForPhysLib.QuantumMechanics.HarmonicOscillator

/--
info: tagged boundary crossings:
[carrierVocab] ForPhysLib.QuantumMechanics.HarmonicOscillator.numeralSMul — A dimensionless numeral scales a quantity without changing its kind — the `nᵢ + ½`
[kindConst] ForPhysLib.QuantumMechanics.HarmonicOscillator.hbarQ — ℏ as an action quantity — one attestation naming what the source's type does not
[kindCrossing] ForPhysLib.QuantumMechanics.HarmonicOscillator.AngularMomentum.angularMomentumReading — **The `m·ℏ` crossing**: a dimensionless integer scales the action constant and the
[kindCrossing] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.energySMul — **F1d's crossing, on the right-hand side of the subject's defining equation**: an
[kindCrossing] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.positionOfDimensionless — `ξEquiv` at kinds: a dimensionless coordinate vector becomes a position.
[kindCrossing] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.totalProbabilityQ — **Density × volume crosses to probability** — the integral `∫ρ dV` aggregates the
[kindCrossing] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.xiRoot — One attested root carries the radicand to the characteristic length — roots are
[kindCrossing] ForPhysLib.QuantumMechanics.HarmonicOscillator.kineticFromMomentumQ — **F1d — the named crossing.** PhysLib builds `T̂` as `(2·m)⁻¹ • p̂²`: a dimensionful
[kindEmission] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.rawEigenEnergy — The emission boundary, stated once as a `def` so it carries its tier: downstream
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.Heisenberg.momentumSigmaQ — The momentum uncertainty read at its kind. Momentum's *essential*
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.Heisenberg.positionOpQ — The position operator read at its kind — self-adjointness is *proved* upstream
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.bornDensityQ — **The Born density, kinded** — `|ψ|²` as a probability density over position. The
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.mQd — The `d`-dimensional mass, read at its kind (the 1D twin is Feasibility's `mQ`).
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.occupationQ — The occupation labels, looked up from the catalogue (ISO 80000-10 item 10-13.1),
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.Ladder.numberOpQ — The number operator read at the quantum-number kind (ISO 80000-10 item 10-13.1):
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.kineticOpQ — `T̂` at its kind, at the operator carrier.
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.mQ — The 1D mass, read at its kind.
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.momentumSqOpQ — `p̂²` at its kind.
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.potentialOpQ — `V̂` at its kind.
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.xiQ — **F2b.** One attested root lands the length: kinded `ξ`, equal to PhysLib's own.
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.ωQ — The `d`-dimensional mode frequency at its kind.
[kindIngest] ForPhysLib.QuantumMechanics.HarmonicOscillator.ωQ1 — The 1D angular frequency.
-/
#guard_msgs (whitespace := lax) in
#kind_crossings ForPhysLib.QuantumMechanics.HarmonicOscillator

/-! ## The gates that cannot be re-blessed — silent on a clean scope -/

#guard_msgs in #kind_boundary_clean ForPhysLib.QuantumMechanics.HarmonicOscillator
#guard_msgs in #kind_mint_ratchet ForPhysLib.QuantumMechanics.HarmonicOscillator
set_option maxHeartbeats 1600000 in
#guard_msgs in #kind_dimensional_clean ForPhysLib.QuantumMechanics.HarmonicOscillator

/-! ## The unkinded ledger — the interior gated, the boundary measured -/

/-- The interior scope: the crossings that are kinded end to end — a quantity in, a
quantity out. Gated empty: a naked binder added here is a build failure. (`ξEquiv`'s
crossing is *not* here: it reads the raw oscillator, so it belongs to the measured
boundary below — the contract refused it, and the refusal was correct.) -/
def interiorScope : Provenance.Contract String String where
  name := "QuantumMechanics/HarmonicOscillator kinded interior"
  members := ["ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.xiRoot",
              "ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.totalProbabilityQ"]
  ports := []
  exits := []

/--
info: unkinded ledger of 'QuantumMechanics/HarmonicOscillator kinded interior':
unkinded: none — every position carries a kind
-/
#guard_msgs in #kind_unkinded interiorScope

/-- info: unkinded-clean: every position of 'QuantumMechanics/HarmonicOscillator kinded interior' carries a kind -/
#guard_msgs in #kind_unkinded_clean interiorScope

/-- The ingest boundary: the Stage-2 mints where PhysLib's carriers enter, the one
emission where a naked `ℝ` leaves, and the two crossings that touch naked carriers —
the eigenstate the TISE's `E •` acts on, and the oscillator whose `ξᵢ` ride `ξEquiv`.
Its ledger is *not* empty and must not be gated: the oscillator structure, the
occupation labels and the Hilbert space are PhysLib's carriers, not quantities — the
MR30 tier discipline: measured, so growth is visible; never hidden behind a gate it
would fail. -/
def ingestBoundary : Provenance.Contract String String where
  name := "QuantumMechanics/HarmonicOscillator ingest boundary"
  members := ["ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.mQd",
              "ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.occupationQ",
              "ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.bornDensityQ",
              "ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.rawEigenEnergy",
              "ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.energySMul",
              "ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded.positionOfDimensionless",
              "ForPhysLib.QuantumMechanics.HarmonicOscillator.Heisenberg.positionOpQ",
              "ForPhysLib.QuantumMechanics.HarmonicOscillator.Heisenberg.momentumSigmaQ"]
  ports := []
  exits := []

/--
info: unkinded ledger of 'QuantumMechanics/HarmonicOscillator ingest boundary':
unkinded: 15 position(s), 9 flow(s)
unkinded input mQd/Q : QuantumMechanics.HarmonicOscillator d
unkinded flow: mQd/Q ⇒ mQd/result
unkinded input occupationQ/n : Fin d → ℕ
unkinded input occupationQ/i : Fin d
unkinded flow: occupationQ/n ⇒ occupationQ/result
unkinded flow: occupationQ/i ⇒ occupationQ/result
unkinded input bornDensityQ/Q : QuantumMechanics.HarmonicOscillator d
unkinded input bornDensityQ/n : Fin d → ℕ
unkinded flow: bornDensityQ/Q ⇒ bornDensityQ/result
unkinded flow: bornDensityQ/n ⇒ bornDensityQ/result
unkinded input rawEigenEnergy/Q : QuantumMechanics.HarmonicOscillator d
unkinded input rawEigenEnergy/n : Fin d → ℕ
unkinded output rawEigenEnergy/result : ℝ
unkinded input energySMul/Q : QuantumMechanics.HarmonicOscillator d
unkinded input energySMul/ψ : Q.HS
unkinded output energySMul/result : Q.HS
unkinded input positionOfDimensionless/Q : QuantumMechanics.HarmonicOscillator d
unkinded flow: positionOfDimensionless/Q ⇒ positionOfDimensionless/_1
unkinded input positionOpQ/i : Fin d
unkinded flow: positionOpQ/i ⇒ positionOpQ/_1
unkinded input momentumSigmaQ/i : Fin d
unkinded input momentumSigmaQ/ψ : ↥(𝓟 i).domain
unkinded flow: momentumSigmaQ/i ⇒ momentumSigmaQ/_1
unkinded flow: momentumSigmaQ/ψ ⇒ momentumSigmaQ/_1
-/
#guard_msgs (whitespace := lax) in #kind_unkinded ingestBoundary

end ForPhysLib.QuantumMechanics.HarmonicOscillator.Audits
