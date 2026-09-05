/-
# Stage 4 — audits and the API map, for `Physlib/Electromagnetism/Kinematics`

The top rung of [the adoption ladder](../../PLAN.md#stage-4-audits-and-the-api-map) for
the campaign's second directory: the whole directory's kinded surface put under CI —
probe files included. Five gates, each in the discipline its command enforces:

  * `#kind_boundary_audit` **pinned** over the full directory namespace: forty-eight
    boundary sites — every mint, attestation and erasure from `Feasibility.lean`'s
    readings through `Maxwell.lean`'s sources to `Dynamics.lean`'s variational
    crossings — each with its tier. A new untagged site breaks the pin.
  * `#kind_boundary_clean` and `#kind_mint_ratchet` **silent**: they throw on
    violation and print nothing on a clean scope, so neither can be re-blessed by
    re-pinning. The ratchet is why `numeralSMul`'s mint is *attested*, not raw.
  * `#kind_unkinded` over two declared contracts — and here the ratio inverts the
    pilot's: **twelve** crossings are kinded end to end (the interior, gated empty)
    against eleven boundary readings. The chain's core derivations — both slices, the
    field constructions, chart, extent, the frame readings, the gauge shift, the
    torsor — never touch a naked carrier once the potential is read in; the boundary
    is exactly where PhysLib's carriers enter (the potential structure, the coordinate
    points, the `SpeedOfLight`) and the one emission where a naked field leaves.
  * `#kind_dimensional_clean` **silent** over the whole directory: the Stage-1 laws,
    Feasibility's probe-era entries, and Stage 3's registrations, coherent in
    PhysLib's dimension group from one command no file-local pin can drift from.

The API-map half of the stage is the `checked_by:` field. This directory has no
`API-map.yaml` upstream — its requirement ledger is the `TODO` commands spread through
the chain — so the proposed delta beside this file (`Kinematics.checked_by.yaml`) keys
on those TODO texts, pointing each at the ForPhysLib module whose build now checks the
claim or holds its statement ready.
-/

import ForPhysLib.Electromagnetism.Kinematics.Operators
import ForPhysLib.Electromagnetism.Kinematics.DistributionalTwin
import ForPhysLib.Electromagnetism.Kinematics.Maxwell
import ForPhysLib.Electromagnetism.Kinematics.Dynamics
import PropertyKindCalculus.BoundaryAudit
import PropertyKindCalculus.KindLedger
import PropertyKindCalculus.DimensionalCoverage

namespace ForPhysLib.Electromagnetism.Kinematics.Audits

open PropertyKindCalculus

/-! ## The boundary audit, pinned -/

/--
info: boundary audit:
[carrierVocab] ForPhysLib.Electromagnetism.Kinematics.numeralSMul — attests: (kind-parametric) ‹a dimensionless numeral scales; the kind is unchanged›
[kindConst] ForPhysLib.Electromagnetism.Kinematics.Maxwell.epsilonQ — attests: Kinds.electricConstant ‹FreeSpace.ε₀ — the electric constant, a bare ℝ field upstream›
[kindConst] ForPhysLib.Electromagnetism.Kinematics.Maxwell.muQ — attests: Kinds.magneticConstant ‹FreeSpace.μ₀ — the magnetic constant, a bare ℝ field upstream›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.DistributionalTwin.distElectricFieldQ — attests: electricFieldK ‹the twin's -∇φ - ∂ₜ𝐀 — distributional derivatives ride the same crossing›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.DistributionalTwin.distFieldStrengthQ — attests: Kinds.fieldStrength ‹the twin's F = dA — the antisymmetrized distributional derivative›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.canonicalMomentumQ — attests: Kinds.canonicalMomentumDensity ‹π = ∂L/∂(∂₀A) — the Legendre-conjugate reading›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.freeCurrentPotentialQ — attests: Kinds.lagrangianDensity ‹⟪A, J⟫ₘ — the interaction density; the Minkowski product is unseen by any table›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.freeSpaceSpeedQ — attests: speedOfLightK ‹c = 1/√(ε₀·μ₀) — FreeSpace.c, the defined constant›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.gradFreeCurrentPotentialQ — attests: Kinds.variationalGradient ‹δ(∫⟪A,J⟫ₘ)/δA = η·J — the current re-kinded by the variational derivative›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.gradKineticTermQ — attests: Kinds.variationalGradient ‹δ(∫L_kin)/δA = μ₀⁻¹·∑∂F — the Euler–Lagrange reading's field side›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.gradLagrangianQ — attests: Kinds.variationalGradient ‹δS/δA — the reading IsExtrema sets to zero›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.hamiltonianQ — attests: Kinds.electromagneticEnergyDensity ‹H = π·∂₀A − L — the Legendre transform, read at the field energy density›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.kineticTermQ — attests: Kinds.lagrangianDensity ‹−¼μ₀⁻¹·F·F — the kinetic term at the gauge-dependent density mint›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.lagrangianQ — attests: Kinds.lagrangianDensity ‹L = kineticTerm − freeCurrentPotential — a same-kind subtraction, no join›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.derivQ — attests: Kinds.potentialGradient ‹∂_μ A^ν — the per-coordinate chart; gauge-dependent until antisymmetrized›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.fieldStrengthMatrixQ — attests: Kinds.fieldStrength ‹the extent in the standard basis›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.fieldStrengthQ — attests: Kinds.fieldStrength ‹η∂A − η∂A — the antisymmetrization erases the gauge dependence›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.magneticFieldFromPotentialQ — attests: magneticFluxDensityK ‹∇×𝐀 — the curl edge, ridden through Mathlib's fderiv›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.magneticFieldMatrixQ — attests: magneticFluxDensityK ‹the spatial block of the tensor, read in the frame the slicing chose›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.magneticReadingQ — attests: magneticFluxDensityK ‹the spatial block read in the frame the slicing chose — same number, framed›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.negGradScalarQ — attests: electricFieldK ‹−∇φ — the difference-quotient edge, ridden through Mathlib's fderiv›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.timeDerivVectorQ — attests: electricFieldK ‹∂ₜ𝐀 — the per-duration edge, ridden through Mathlib's fderiv›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.vectorPotentialQ — attests: vectorPotentialK ‹the spatial slice — same kind; timeSlice re-parameterizes by c·t ↦ t›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.ampereSourceQ — attests: Kinds.magneticFieldDerivative ‹μ₀·(J + ε₀∂ₜE) — one edge over a same-kind sum›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.chargeDensitySliceQ — attests: Kinds.electricChargeDensity ‹J⁰/c — the velocity edge down to the charge density›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.curlBQ — attests: Kinds.magneticFieldDerivative ‹∇⨯B — the magnetic per-length edge, entrywise›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.curlEQ — attests: Kinds.electricFieldDerivative ‹∇⨯E — the electric per-length edge, entrywise›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.currentDensitySliceQ — attests: Kinds.electricCurrentDensity ‹the spatial slice — same kind; timeSlice re-parameterizes›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.divergenceBQ — attests: Kinds.magneticFieldDerivative ‹∇⬝B — the magnetic per-length edge›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.divergenceEQ — attests: Kinds.electricFieldDerivative ‹∇⬝E — the electric per-length edge, fderiv unseen›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.gaussSourceQ — attests: Kinds.electricFieldDerivative ‹ρ/ε₀ — Gauss's source edge›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.negTimeDerivBQ — attests: Kinds.electricFieldDerivative ‹-∂ₜB — the flux density per duration edge›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Operators.potentialSubQ — attests: potentialDifferenceK ‹the torsor −ᵥ: interval positions determine a ratio-scale extent›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.gaugeShiftQ — attests: vectorPotentialK ‹the gauge translation: the potential moves, the kind does not›
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.scalarPotentialQ — attests: electricPotentialK ‹c·A⁰ — the velocity edge, landing on the interval-scale potential›
[kindEmission] ForPhysLib.Electromagnetism.Kinematics.Kinded.rawElectricField — erases (emission-only)
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.DistributionalTwin.distPotentialQ — attests: vectorPotentialK ‹the distributional A^μ — the twin carrier at the chain's kind›
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.Kinded.fieldStrengthAtQ — attests: Kinds.fieldStrength ‹pointwise reading of the chain's field-strength components›
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.Maxwell.currentFourQ — attests: Kinds.electricCurrentDensity ‹J^μ — one kind; the time slot is c·ρ›
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.Operators.scalarPotentialAtQ — attests: electricPotentialK ‹pointwise reading of the chain's scalarPotential — gauge-fixed, interval›
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.electricFieldAtQ — attests: electricFieldK ‹pointwise reading of the chain's electricField›
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.electricFieldQ — attests: electricFieldK ‹reading of the chain's electricField›
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.gaugeFnQ — attests: magneticFluxK ‹a gauge function is a magnetic flux field: ∂^μχ lands at 6-32›
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.magneticFieldQ — attests: magneticFluxDensityK ‹reading of the chain's magneticField›
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.magneticMatrixAtQ — attests: magneticFluxDensityK ‹pointwise reading of the chain's magneticFieldMatrix›
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.potentialQ — attests: vectorPotentialK ‹the four-potential — homogeneous at 6-32 because A⁰ = φ/c›
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.speedQ — attests: speedOfLightK ‹the unit-system choice, declared once instead of defaulted per call site›
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.speedRQ — attests: speedOfLightK ‹the declared speed, at the table's carrier›
48 boundary site(s), all tagged — clean
-/
#guard_msgs (whitespace := lax) in
#kind_boundary_audit ForPhysLib.Electromagnetism.Kinematics

/--
info: tagged boundary crossings:
[carrierVocab] ForPhysLib.Electromagnetism.Kinematics.numeralSMul — A dimensionless numeral scales a quantity without changing its kind — `β` and `γ`
[kindConst] ForPhysLib.Electromagnetism.Kinematics.Maxwell.epsilonQ — `FreeSpace.ε₀`, read at 6-14.1 — a bare `ℝ` field upstream; the F/m commitment
[kindConst] ForPhysLib.Electromagnetism.Kinematics.Maxwell.muQ — `FreeSpace.μ₀`, read at 6-26.1.
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.DistributionalTwin.distElectricFieldQ — The twin's electric field at the chain's 6-10: the same `-∇φ - ∂ₜ𝐀`, with the
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.DistributionalTwin.distFieldStrengthQ — The twin's field-strength tensor at the chain's one mint — the frame-covariant
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.canonicalMomentumQ — `π = ∂L/∂(∂₀A)` — the canonical momentum, on the
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.freeCurrentPotentialQ — `⟪A, J⟫ₘ` — the interaction density, on the `A·J` edge
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.freeSpaceSpeedQ — `c = 1/√(ε₀·μ₀)` — upstream's definition of `FreeSpace.c`, read at the speed of
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.gradFreeCurrentPotentialQ — `δ(∫⟪A, J⟫ₘ)/δA` — the metric-lowered current read as a variational gradient: the
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.gradKineticTermQ — `δ(∫L_kin)/δA` — the kinetic term's variational gradient, on the
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.gradLagrangianQ — `δS/δA` — the full variational gradient, on the
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.hamiltonianQ — `H = π·∂₀A − L` — the Hamiltonian: the Legendre product rides the
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.kineticTermQ — `−¼μ₀⁻¹·F·F` — the kinetic term, riding the `π` edge
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Dynamics.lagrangianQ — `L = L_kin − ⟪A, J⟫ₘ` — the Lagrangian density: the same-kind subtraction the two
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.derivQ — The derivative tensor `∂_μ A^ν` at the **gauge-dependent** chart kind — a vector
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.fieldStrengthMatrixQ — The tensor in the standard basis, at the same extent kind.
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.fieldStrengthQ — The field strength `F^{μν}` at the **frame-covariant, gauge-invariant** extent
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.magneticFieldFromPotentialQ — `∇×𝐀` — the curl crossing (3-D): a vector potential per space-length lands at the
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.magneticFieldMatrixQ — The magnetic-field matrix in general `d` — the tensor's spatial block, sliced.
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.magneticReadingQ — **The magnetic reading** — the spatial block *is* the magnetic field matrix: a
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.negGradScalarQ — `−∇φ` — the gradient crossing of `E = −∇φ − ∂ₜ𝐀`. The Stage-1 edge is stated at
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.timeDerivVectorQ — `∂ₜ𝐀` — the time-derivative crossing of the same equation: a vector potential per
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Kinded.vectorPotentialQ — The vector-potential slice — the spatial components at the same kind,
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.ampereSourceQ — `μ₀J + μ₀ε₀∂ₜE` — Ampère's source: `ε₀∂ₜE` lands at 6-8 (the displacement
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.chargeDensitySliceQ — `ρ = J⁰/c` — the velocity edge down to 6-3, the mirror of `φ = c·A⁰`.
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.curlBQ — `∇⨯B` — Ampère's left side, on `magneticFluxDensity / length`.
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.curlEQ — `∇⨯E` — entrywise on the same electric per-length edge.
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.currentDensitySliceQ — The spatial current slice, at its own kind — `timeSlice` re-parameterizes, the
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.divergenceBQ — `∇⬝B` — the magnetic per-length edge; Gauss-magnetic's left side.
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.divergenceEQ — `∇⬝E` — the per-length edge `electricFieldStrength / length`; `∇` is Mathlib's
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.gaussSourceQ — `ρ/ε₀` — Gauss's source, on the edge
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Maxwell.negTimeDerivBQ — `-∂ₜB` — Faraday's right side, on `magneticFluxDensity / duration`
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.Operators.potentialSubQ — The torsor's `−ᵥ`: two positions on the potential axis determine an extent — the
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.gaugeShiftQ — **F5a — the torsor translation.** The gauge shift `A ↦ A + ∂^μχ` moves the
[kindCrossing] ForPhysLib.Electromagnetism.Kinematics.scalarPotentialQ — **F2b — the crossing back.** `scalarPotential = c·A⁰`: the 6-32 → 6-11.1 velocity
[kindEmission] ForPhysLib.Electromagnetism.Kinematics.Kinded.rawElectricField — The emission boundary, stated once as a `def` so it carries its tier: downstream
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.DistributionalTwin.distPotentialQ — The distributional potential, read at the chain's 6-32 — the *same* kind the
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.Kinded.fieldStrengthAtQ — A pointwise extent entry, read at its kind.
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.Maxwell.currentFourQ — `J^μ` — homogeneous at 6-8 for the same reason `A^μ` was homogeneous at 6-32:
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.Operators.scalarPotentialAtQ — A pointwise reading of the scalar potential, at the **interval-scale** 6-11.1.
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.electricFieldAtQ — A pointwise electric-field reading — the boost law mixes *values*, so the probe
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.electricFieldQ — `E` read at its kind, at the field carrier — the wrap is of the *whole* field
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.gaugeFnQ — A gauge function at its kind: `∂^μχ` sits at 6-32, so `χ` is a magnetic flux
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.magneticFieldQ — `B` read at its kind, over the *same* naked carrier type as `E`.
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.magneticMatrixAtQ — A pointwise magnetic-field-matrix reading — the spatial block of the field
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.potentialQ — The four-potential at its one kind.
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.speedQ — The declared speed of light — F3's alternative to the silent default: one attested
[kindIngest] ForPhysLib.Electromagnetism.Kinematics.speedRQ — The speed of light at the scalar carrier, for the table.
-/
#guard_msgs (whitespace := lax) in
#kind_crossings ForPhysLib.Electromagnetism.Kinematics

/-! ## The gates that cannot be re-blessed — silent on a clean scope -/

#guard_msgs in #kind_boundary_clean ForPhysLib.Electromagnetism.Kinematics
#guard_msgs in #kind_mint_ratchet ForPhysLib.Electromagnetism.Kinematics
#guard_msgs in #kind_dimensional_clean ForPhysLib.Electromagnetism.Kinematics

/-! ## The unkinded ledger — the interior gated, the boundary measured -/

/-- The interior scope: the crossings that are kinded end to end — a quantity in, a
quantity out. Twelve of them, against the pilot's two: once the potential is read in,
the chain's whole derivation tree — slices, field constructions, chart, extent, frame
readings, the gauge shift, the torsor — runs inside the kind layer. Gated empty: a
naked binder added here is a build failure. -/
def interiorScope : Provenance.Contract String String where
  name := "Electromagnetism/Kinematics kinded interior"
  members := ["ForPhysLib.Electromagnetism.Kinematics.scalarPotentialQ",
              "ForPhysLib.Electromagnetism.Kinematics.gaugeShiftQ",
              "ForPhysLib.Electromagnetism.Kinematics.Kinded.vectorPotentialQ",
              "ForPhysLib.Electromagnetism.Kinematics.Kinded.negGradScalarQ",
              "ForPhysLib.Electromagnetism.Kinematics.Kinded.timeDerivVectorQ",
              "ForPhysLib.Electromagnetism.Kinematics.Kinded.magneticFieldFromPotentialQ",
              "ForPhysLib.Electromagnetism.Kinematics.Kinded.magneticFieldMatrixQ",
              "ForPhysLib.Electromagnetism.Kinematics.Kinded.derivQ",
              "ForPhysLib.Electromagnetism.Kinematics.Kinded.fieldStrengthQ",
              "ForPhysLib.Electromagnetism.Kinematics.Kinded.fieldStrengthMatrixQ",
              "ForPhysLib.Electromagnetism.Kinematics.Kinded.magneticReadingQ",
              "ForPhysLib.Electromagnetism.Kinematics.Operators.potentialSubQ"]
  ports := []
  exits := []

/--
info: unkinded ledger of 'Electromagnetism/Kinematics kinded interior':
unkinded: none — every position carries a kind
-/
#guard_msgs in #kind_unkinded interiorScope

/-- info: unkinded-clean: every position of 'Electromagnetism/Kinematics kinded interior' carries a kind -/
#guard_msgs in #kind_unkinded_clean interiorScope

/-- The ingest boundary: the readings where PhysLib's carriers enter — the potential
structure, the evaluation points, the `SpeedOfLight` — and the one emission where a
naked field leaves. Its ledger is *not* empty and must not be gated: those carriers
are PhysLib's, not quantities — the MR30 tier discipline: measured, so growth is
visible; never hidden behind a gate it would fail. -/
def ingestBoundary : Provenance.Contract String String where
  name := "Electromagnetism/Kinematics ingest boundary"
  members := ["ForPhysLib.Electromagnetism.Kinematics.speedQ",
              "ForPhysLib.Electromagnetism.Kinematics.speedRQ",
              "ForPhysLib.Electromagnetism.Kinematics.potentialQ",
              "ForPhysLib.Electromagnetism.Kinematics.gaugeFnQ",
              "ForPhysLib.Electromagnetism.Kinematics.electricFieldQ",
              "ForPhysLib.Electromagnetism.Kinematics.magneticFieldQ",
              "ForPhysLib.Electromagnetism.Kinematics.electricFieldAtQ",
              "ForPhysLib.Electromagnetism.Kinematics.magneticMatrixAtQ",
              "ForPhysLib.Electromagnetism.Kinematics.Kinded.fieldStrengthAtQ",
              "ForPhysLib.Electromagnetism.Kinematics.Operators.scalarPotentialAtQ",
              "ForPhysLib.Electromagnetism.Kinematics.Kinded.rawElectricField"]
  ports := []
  exits := []

/--
info: unkinded ledger of 'Electromagnetism/Kinematics ingest boundary':
unkinded: 28 position(s), 23 flow(s)
unkinded input speedQ/cS : SpeedOfLight
unkinded flow: speedQ/cS ⇒ speedQ/_1
unkinded input speedRQ/cS : SpeedOfLight
unkinded flow: speedRQ/cS ⇒ speedRQ/_1
unkinded input potentialQ/A : Electromagnetism.ElectromagneticPotential d
unkinded flow: potentialQ/A ⇒ potentialQ/_1
unkinded input gaugeFnQ/χ : SpaceTime d → ℝ
unkinded flow: gaugeFnQ/χ ⇒ gaugeFnQ/_1
unkinded input electricFieldQ/A : Electromagnetism.ElectromagneticPotential d
unkinded flow: electricFieldQ/A ⇒ electricFieldQ/_1
unkinded input magneticFieldQ/A : Electromagnetism.ElectromagneticPotential
unkinded flow: magneticFieldQ/A ⇒ magneticFieldQ/_1
unkinded input electricFieldAtQ/cS : SpeedOfLight
unkinded input electricFieldAtQ/A : Electromagnetism.ElectromagneticPotential d
unkinded input electricFieldAtQ/t : Time
unkinded input electricFieldAtQ/x : Space d
unkinded input electricFieldAtQ/i : Fin d
unkinded flow: electricFieldAtQ/cS ⇒ electricFieldAtQ/_1
unkinded flow: electricFieldAtQ/A ⇒ electricFieldAtQ/_1
unkinded flow: electricFieldAtQ/t ⇒ electricFieldAtQ/_1
unkinded flow: electricFieldAtQ/x ⇒ electricFieldAtQ/_1
unkinded flow: electricFieldAtQ/i ⇒ electricFieldAtQ/_1
unkinded input magneticMatrixAtQ/cS : SpeedOfLight
unkinded input magneticMatrixAtQ/A : Electromagnetism.ElectromagneticPotential d
unkinded input magneticMatrixAtQ/t : Time
unkinded input magneticMatrixAtQ/x : Space d
unkinded input magneticMatrixAtQ/ij : Fin d × Fin d
unkinded flow: magneticMatrixAtQ/cS ⇒ magneticMatrixAtQ/_1
unkinded flow: magneticMatrixAtQ/A ⇒ magneticMatrixAtQ/_1
unkinded flow: magneticMatrixAtQ/t ⇒ magneticMatrixAtQ/_1
unkinded flow: magneticMatrixAtQ/x ⇒ magneticMatrixAtQ/_1
unkinded flow: magneticMatrixAtQ/ij ⇒ magneticMatrixAtQ/_1
unkinded input fieldStrengthAtQ/A : Electromagnetism.ElectromagneticPotential d
unkinded input fieldStrengthAtQ/x : SpaceTime d
unkinded input fieldStrengthAtQ/μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)
unkinded flow: fieldStrengthAtQ/A ⇒ fieldStrengthAtQ/_1
unkinded flow: fieldStrengthAtQ/x ⇒ fieldStrengthAtQ/_1
unkinded flow: fieldStrengthAtQ/μν ⇒ fieldStrengthAtQ/_1
unkinded input scalarPotentialAtQ/cS : SpeedOfLight
unkinded input scalarPotentialAtQ/A : Electromagnetism.ElectromagneticPotential d
unkinded input scalarPotentialAtQ/t : Time
unkinded input scalarPotentialAtQ/x : Space d
unkinded flow: scalarPotentialAtQ/cS ⇒ scalarPotentialAtQ/_1
unkinded flow: scalarPotentialAtQ/A ⇒ scalarPotentialAtQ/_1
unkinded flow: scalarPotentialAtQ/t ⇒ scalarPotentialAtQ/_1
unkinded flow: scalarPotentialAtQ/x ⇒ scalarPotentialAtQ/_1
unkinded input rawElectricField/cS : SpeedOfLight
unkinded input rawElectricField/A : Electromagnetism.ElectromagneticPotential d
unkinded input rawElectricField/a._@._internal._hyg.0 : Time
unkinded input rawElectricField/a._@._internal._hyg.0 : Space d
unkinded output rawElectricField/result : EuclideanSpace ℝ (Fin d)
-/
#guard_msgs (whitespace := lax) in #kind_unkinded ingestBoundary

end ForPhysLib.Electromagnetism.Kinematics.Audits
