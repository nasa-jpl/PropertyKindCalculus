/-
# Stage 4 — audits and the API map, for `Physlib/ClassicalMechanics` (two subtrees)

The top rung of [the adoption ladder](../PLAN.md#stage-4-audits-and-the-api-map) for
the campaign's third directory: the whole directory namespace put under CI — probe
files included. Five gates, each in the discipline its command enforces:

  * `#kind_boundary_audit` **pinned** over the full directory namespace — every mint,
    attestation and erasure from `Feasibility.lean`'s readings to `Operators.lean`'s
    full turn, each with its tier; all four tiers present (ingest, crossing, constant,
    emission) plus the carrier vocabulary. A new untagged site breaks the pin.
  * `#kind_boundary_clean` and `#kind_mint_ratchet` **silent**: they throw on
    violation and print nothing on a clean scope, so neither can be re-blessed by
    re-pinning. The ratchet is why `numeralSMul`'s mint is *attested*, not raw.
  * `#kind_unkinded` over two declared contracts. The interior — the composites and
    crossings that are kinded end to end — is **gated empty**. The ingest boundary is
    *measured, not gated*: this directory's boundary is **wide** — the two subtrees'
    readings enter from `HarmonicOscillator`, `InitialConditions`, `RigidBody`,
    `RigidBodyMotion`, `Time`, `Space` — because upstream's objects are structures of
    bare reals, so *every* reading is a boundary site. The pilot's ratio, directed
    the other way from directory 2's: the field theory's interior was deep and its
    boundary thin; point mechanics has a thin interior (the algebra between readings
    is short) and a broad boundary (there are many readings).
  * `#kind_dimensional_clean` **silent** over the whole directory: Stage 1's fourteen
    laws, Feasibility's six probe-era entries and Stage 3's seven registrations,
    coherent in PhysLib's dimension group from one command no file-local pin can
    drift from.

The API-map half of the stage is the `checked_by:` field. Neither subtree has an
`API-map.yaml` upstream — the requirement ledger is the `TODO` commands and one
`@[sorryful]` lemma — so the proposed delta beside this file
(`ClassicalMechanics.checked_by.yaml`) keys on those texts.
-/

import ForPhysLib.ClassicalMechanics.Operators
import PropertyKindCalculus.BoundaryAudit
import PropertyKindCalculus.KindLedger
import PropertyKindCalculus.DimensionalCoverage

namespace ForPhysLib.ClassicalMechanics.Audits

open PropertyKindCalculus

/-! ## The boundary audit, pinned -/

/--
info: boundary audit:
[carrierVocab] ForPhysLib.ClassicalMechanics.numeralSMul — attests: (kind-parametric) ‹a dimensionless numeral scales; the kind is unchanged›
[kindConst] ForPhysLib.ClassicalMechanics.Operators.fullTurnQ — attests: phaseAngleK ‹2π — one full turn of phase›
[kindCrossing] ForPhysLib.ClassicalMechanics.Kinded.pointMassInertiaQ — attests: momentOfInertiaK ‹m·(|c−p|²δ − (c−p)⊗(c−p)) — the point-particle inertia›
[kindCrossing] ForPhysLib.ClassicalMechanics.amplitudeQ — attests: displacementK ‹‖z‖ — the polar radius of two like-kind components›
[kindCrossing] ForPhysLib.ClassicalMechanics.forceQ — attests: forceK ‹−∇V — the force reading›
[kindCrossing] ForPhysLib.ClassicalMechanics.hamiltonianQ — attests: mechanicalEnergyK ‹H(t, p, x) — at the kinded signature the argument order is checked›
[kindCrossing] ForPhysLib.ClassicalMechanics.lagrangianQ — attests: lagrangianK ‹T − V — the difference the joule vocabulary has no home for›
[kindCrossing] ForPhysLib.ClassicalMechanics.omegaQ — attests: angularFrequencyK ‹the root of the radicand: √(k/m) lands at 3-18›
[kindCrossing] ForPhysLib.ClassicalMechanics.periodQ — attests: periodDurationK ‹2π/ω — the repetition interval›
[kindCrossing] ForPhysLib.ClassicalMechanics.toCanonicalMomentumQ — attests: momentumK ‹the canonical momentum m·v — the 4-8 edge at the vector carrier›
[kindEmission] ForPhysLib.ClassicalMechanics.Kinded.cosPhase — erases (emission-only)
[kindEmission] ForPhysLib.ClassicalMechanics.Kinded.rawTrajectoryValue — erases (emission-only)
[kindEmission] ForPhysLib.ClassicalMechanics.Kinded.sinPhase — erases (emission-only)
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.bodyOmegaTensorAtQ — attests: angularVelocityK ‹an entry of Ω_body = Rᵀ Ṙ — the body-frame reading›
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.comQ — attests: displacementK ‹the first moment over the mass — a centre-of-mass coordinate›
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.comVelocityAtQ — attests: velocityK ‹a centre-of-mass velocity component›
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.displacementE1Q — attests: displacementK ‹the configuration, read whole›
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.energyRateQ — attests: Kinds.power ‹∂ₜE — conservation's reading, at the watt›
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.geometricKineticEnergyQ — attests: kineticEnergyK ‹½·g_m(v,v) — the mass metric's kinetic energy›
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.inertiaAboutAtQ — attests: momentOfInertiaK ‹the second moment about p›
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.omegaTensorAtQ — attests: angularVelocityK ‹an entry of Ω = Ṙ Rᵀ — the lab-frame reading›
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.omegaVecAtQ — attests: angularVelocityK ‹an angular-velocity vector component — ω = Ωᵛ›
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.phaseOffsetQ — attests: phaseAngleK ‹arg z — the phase read from the polar pair›
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.relPositionAtQ — attests: displacementK ‹the body point's displacement from the moving centre of mass›
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.velocityAtQ — attests: velocityK ‹the trajectory's time derivative, component 0›
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.velocityE1Q — attests: velocityK ‹the velocity, read whole›
[kindIngest] ForPhysLib.ClassicalMechanics.Operators.displacementAtQ — attests: displacementK ‹the trajectory's displacement, component 0›
[kindIngest] ForPhysLib.ClassicalMechanics.accelerationAtQ — attests: accelerationK ‹the trajectory's second time derivative, component 0›
[kindIngest] ForPhysLib.ClassicalMechanics.displacement0Q — attests: displacementK ‹x₀ — the initial displacement›
[kindIngest] ForPhysLib.ClassicalMechanics.durationQ — attests: durationK ‹the trajectory parameter›
[kindIngest] ForPhysLib.ClassicalMechanics.forceAtQ — attests: forceK ‹the force at the trajectory's displacement, component 0›
[kindIngest] ForPhysLib.ClassicalMechanics.hamiltonianAtQ — attests: mechanicalEnergyK ‹H on the trajectory — equal to the energy by hamiltonian_eq_energy›
[kindIngest] ForPhysLib.ClassicalMechanics.inertiaAtQ — attests: momentOfInertiaK ‹the second moment δᵢⱼ|x|² − xᵢxⱼ of the mass distribution›
[kindIngest] ForPhysLib.ClassicalMechanics.kineticQ — attests: kineticEnergyK ‹the chain's kineticEnergy — ½m⟪ẋ,ẋ⟫›
[kindIngest] ForPhysLib.ClassicalMechanics.massQ — attests: massK ‹the input datum m›
[kindIngest] ForPhysLib.ClassicalMechanics.omegaCompQ — attests: angularVelocityK ‹an angular-velocity component›
[kindIngest] ForPhysLib.ClassicalMechanics.potentialQ — attests: potentialEnergyK ‹the chain's potentialEnergy — ½k⟪x,x⟫›
[kindIngest] ForPhysLib.ClassicalMechanics.rbMassQ — attests: massK ‹ρ(1) — the zeroth moment of the mass distribution›
[kindIngest] ForPhysLib.ClassicalMechanics.rotationalKEQ — attests: rotationalKineticEnergyK ‹½ω·(Iω) — the rotational energy, body frame›
[kindIngest] ForPhysLib.ClassicalMechanics.springQ — attests: springConstantK ‹the input datum k — Hooke's constant, a mint›
[kindIngest] ForPhysLib.ClassicalMechanics.translationalKEQ — attests: translationalKineticEnergyK ‹½M⟪V,V⟫ — the centre of mass's kinetic energy›
[kindIngest] ForPhysLib.ClassicalMechanics.velocity0Q — attests: velocityK ‹v₀ — the initial velocity›
42 boundary site(s), all tagged — clean
-/
#guard_msgs (whitespace := lax) in
#kind_boundary_audit ForPhysLib.ClassicalMechanics

/--
info: tagged boundary crossings:
[carrierVocab] ForPhysLib.ClassicalMechanics.numeralSMul — A dimensionless numeral scales a quantity without changing its kind — the `½` of
[kindConst] ForPhysLib.ClassicalMechanics.Operators.fullTurnQ — One full turn of phase — the `2π` of the period, as a declared constant at 3-7
[kindCrossing] ForPhysLib.ClassicalMechanics.Kinded.pointMassInertiaQ — The point-particle inertia term of the parallel-axis theorem — the whole mass at
[kindCrossing] ForPhysLib.ClassicalMechanics.amplitudeQ — **The complex number that packs two lengths**: the amplitude–phase inverse embeds
[kindCrossing] ForPhysLib.ClassicalMechanics.forceQ — The kinded force — a displacement goes in.
[kindCrossing] ForPhysLib.ClassicalMechanics.hamiltonianQ — The kinded Hamiltonian signature — momentum first, displacement second, the order
[kindCrossing] ForPhysLib.ClassicalMechanics.lagrangianQ — **The difference is not the sum**: `T − V` lands at the Lagrangian mint — a
[kindCrossing] ForPhysLib.ClassicalMechanics.omegaQ — **The kind-level event**: the square root, radicand-first — a crossing from the
[kindCrossing] ForPhysLib.ClassicalMechanics.periodQ — The period — `2π/ω`, a crossing to 3-14 (the dimensionless `2π` cannot ride the
[kindCrossing] ForPhysLib.ClassicalMechanics.toCanonicalMomentumQ — The kinded canonical momentum — kind-*changing* between identical carriers: a
[kindEmission] ForPhysLib.ClassicalMechanics.Kinded.cosPhase — **The trig boundary, made literal**: `cos` consumes a phase angle and returns a
[kindEmission] ForPhysLib.ClassicalMechanics.Kinded.rawTrajectoryValue — The emission boundary, stated once as a `def` so it carries its tier: a
[kindEmission] ForPhysLib.ClassicalMechanics.Kinded.sinPhase — `sin` consumes a phase angle — the boundary's other half.
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.bodyOmegaTensorAtQ — An entry of the body-frame tensor `Ω_body = Rᵀ Ṙ` — the *same kind*, the other
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.comQ — A centre-of-mass coordinate — the first moment of the distribution over the
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.comVelocityAtQ — A centre-of-mass velocity component.
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.displacementE1Q — The configuration, read whole at its kind (MR19 — the wrap is of the vector;
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.energyRateQ — The energy's rate of change, read at the *power* kind — the Stage-1 edge
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.geometricKineticEnergyQ — The metric-induced kinetic energy, ingested at the kinetic kind: the mass
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.inertiaAboutAtQ — An inertia entry about an arbitrary point `p` — the second moment with the
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.omegaTensorAtQ — An entry of the (lab-frame) angular-velocity tensor `Ω = Ṙ Rᵀ`, read at 3-12.
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.omegaVecAtQ — An angular-velocity vector component (3-D — the dual of `Ω` under the hat map).
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.phaseOffsetQ — The phase offset, read off the polar pair — `arg z`, at the phase-angle kind.
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.relPositionAtQ — A body point's displacement from the moving centre of mass, in the lab frame.
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.velocityAtQ — A pointwise velocity reading along the trajectory.
[kindIngest] ForPhysLib.ClassicalMechanics.Kinded.velocityE1Q — The velocity, read whole at its kind.
[kindIngest] ForPhysLib.ClassicalMechanics.Operators.displacementAtQ — A pointwise displacement reading along a trajectory.
[kindIngest] ForPhysLib.ClassicalMechanics.accelerationAtQ — A pointwise acceleration reading — the equation of motion compares *values*, so
[kindIngest] ForPhysLib.ClassicalMechanics.displacement0Q — The initial displacement, component 0.
[kindIngest] ForPhysLib.ClassicalMechanics.durationQ — The trajectory parameter, read at 3-9.
[kindIngest] ForPhysLib.ClassicalMechanics.forceAtQ — A pointwise force reading along the trajectory.
[kindIngest] ForPhysLib.ClassicalMechanics.hamiltonianAtQ — The on-trajectory Hamiltonian, read at the join's kind — `hamiltonian_eq_energy`
[kindIngest] ForPhysLib.ClassicalMechanics.inertiaAtQ — An inertia-tensor entry — the second moment, at 4-7. The functional's reading:
[kindIngest] ForPhysLib.ClassicalMechanics.kineticQ — The kinetic energy along a trajectory, read at 4-28.2.
[kindIngest] ForPhysLib.ClassicalMechanics.massQ — The oscillator's mass, read at 4-1.
[kindIngest] ForPhysLib.ClassicalMechanics.omegaCompQ — An angular-velocity component, read at 3-12.
[kindIngest] ForPhysLib.ClassicalMechanics.potentialQ — The potential energy at a displacement, read at 4-28.1.
[kindIngest] ForPhysLib.ClassicalMechanics.rbMassQ — The rigid body's total mass — the zeroth moment of the distribution functional,
[kindIngest] ForPhysLib.ClassicalMechanics.rotationalKEQ — König's second summand: the rotational kinetic energy about the centre of mass,
[kindIngest] ForPhysLib.ClassicalMechanics.springQ — The spring constant, read at the mint — the system parameter the catalogue does
[kindIngest] ForPhysLib.ClassicalMechanics.translationalKEQ — König's first summand: the translational kinetic energy of the centre of mass.
[kindIngest] ForPhysLib.ClassicalMechanics.velocity0Q — The initial velocity, component 0.
-/
#guard_msgs (whitespace := lax) in
#kind_crossings ForPhysLib.ClassicalMechanics

/-! ## The gates that cannot be re-blessed — silent on a clean scope -/

#guard_msgs in #kind_boundary_clean ForPhysLib.ClassicalMechanics
#guard_msgs in #kind_mint_ratchet ForPhysLib.ClassicalMechanics
#guard_msgs in #kind_dimensional_clean ForPhysLib.ClassicalMechanics

/-! ## The unkinded ledger — the interior gated, the boundary measured -/

/-- The interior scope: the composites and crossings that are kinded end to end — a
quantity in, a quantity out. The radicand's root, the period, the Lagrangian, the
amplitude, both joins, Newton's product, the phase, and the Legendre witness: the
algebra *between* the readings never touches a naked carrier. Gated empty: a naked
binder added here is a build failure. -/
def interiorScope : Provenance.Contract Provenance.NodeId Provenance.KindRef where
  name := "ClassicalMechanics kinded interior"
  members := [``ForPhysLib.ClassicalMechanics.omegaQ, ``ForPhysLib.ClassicalMechanics.periodQ, ``ForPhysLib.ClassicalMechanics.lagrangianQ, ``ForPhysLib.ClassicalMechanics.amplitudeQ, ``ForPhysLib.ClassicalMechanics.energyQ, ``ForPhysLib.ClassicalMechanics.koenigQ, ``ForPhysLib.ClassicalMechanics.newtonLHSQ, ``ForPhysLib.ClassicalMechanics.phaseQ, ``ForPhysLib.ClassicalMechanics.Kinded.kineticFromTableQ]
  ports := []
  exits := []

/--
info: unkinded ledger of 'ClassicalMechanics kinded interior':
unkinded: none — every position carries a kind
-/
#guard_msgs in #kind_unkinded interiorScope

/-- info: unkinded-clean: every position of 'ClassicalMechanics kinded interior' carries a kind -/
#guard_msgs in #kind_unkinded_clean interiorScope

/-- The ingest boundary: the readings where PhysLib's carriers enter — the system
structures (`HarmonicOscillator`, `RigidBody`, `RigidBodyMotion`), the data
structures (`InitialConditions`, `AmplitudePhase`), the coordinates (`Time`,
`Space`, `EuclideanSpace`, the tangent spaces) — and the one emission where a naked
number leaves. Its ledger is *not* empty and must not be gated: those carriers are
PhysLib's, not quantities — the MR30 tier discipline: measured, so growth is
visible; never hidden behind a gate it would fail. -/
def ingestBoundary : Provenance.Contract Provenance.NodeId Provenance.KindRef where
  name := "ClassicalMechanics ingest boundary"
  members := [``ForPhysLib.ClassicalMechanics.massQ, ``ForPhysLib.ClassicalMechanics.springQ, ``ForPhysLib.ClassicalMechanics.kineticQ, ``ForPhysLib.ClassicalMechanics.potentialQ, ``ForPhysLib.ClassicalMechanics.hamiltonianAtQ, ``ForPhysLib.ClassicalMechanics.accelerationAtQ, ``ForPhysLib.ClassicalMechanics.forceAtQ, ``ForPhysLib.ClassicalMechanics.durationQ, ``ForPhysLib.ClassicalMechanics.displacement0Q, ``ForPhysLib.ClassicalMechanics.velocity0Q, ``ForPhysLib.ClassicalMechanics.rbMassQ, ``ForPhysLib.ClassicalMechanics.inertiaAtQ, ``ForPhysLib.ClassicalMechanics.omegaCompQ, ``ForPhysLib.ClassicalMechanics.translationalKEQ, ``ForPhysLib.ClassicalMechanics.rotationalKEQ, ``ForPhysLib.ClassicalMechanics.Kinded.velocityAtQ, ``ForPhysLib.ClassicalMechanics.Kinded.displacementE1Q, ``ForPhysLib.ClassicalMechanics.Kinded.velocityE1Q, ``ForPhysLib.ClassicalMechanics.Kinded.phaseOffsetQ, ``ForPhysLib.ClassicalMechanics.Kinded.energyRateQ, ``ForPhysLib.ClassicalMechanics.Kinded.geometricKineticEnergyQ, ``ForPhysLib.ClassicalMechanics.Kinded.comQ, ``ForPhysLib.ClassicalMechanics.Kinded.inertiaAboutAtQ, ``ForPhysLib.ClassicalMechanics.Kinded.omegaTensorAtQ, ``ForPhysLib.ClassicalMechanics.Kinded.bodyOmegaTensorAtQ, ``ForPhysLib.ClassicalMechanics.Kinded.comVelocityAtQ, ``ForPhysLib.ClassicalMechanics.Kinded.relPositionAtQ, ``ForPhysLib.ClassicalMechanics.Kinded.omegaVecAtQ, ``ForPhysLib.ClassicalMechanics.Operators.displacementAtQ, ``ForPhysLib.ClassicalMechanics.Kinded.rawTrajectoryValue]
  ports := []
  exits := []

/--

info: unkinded ledger of 'ClassicalMechanics ingest boundary':
unkinded: 72 position(s), 68 flow(s)
unkinded input massQ/S : ClassicalMechanics.HarmonicOscillator
unkinded flow: massQ/S ⇒ massQ/_1
unkinded input springQ/S : ClassicalMechanics.HarmonicOscillator
unkinded flow: springQ/S ⇒ springQ/_1
unkinded input kineticQ/S : ClassicalMechanics.HarmonicOscillator
unkinded input kineticQ/xₜ : Time → EuclideanSpace ℝ (Fin 1)
unkinded input kineticQ/t : Time
unkinded flow: kineticQ/S ⇒ kineticQ/_1
unkinded flow: kineticQ/xₜ ⇒ kineticQ/_1
unkinded flow: kineticQ/t ⇒ kineticQ/_1
unkinded input potentialQ/S : ClassicalMechanics.HarmonicOscillator
unkinded input potentialQ/x : EuclideanSpace ℝ (Fin 1)
unkinded flow: potentialQ/S ⇒ potentialQ/_1
unkinded flow: potentialQ/x ⇒ potentialQ/_1
unkinded input hamiltonianAtQ/S : ClassicalMechanics.HarmonicOscillator
unkinded input hamiltonianAtQ/xₜ : Time → EuclideanSpace ℝ (Fin 1)
unkinded input hamiltonianAtQ/t : Time
unkinded flow: hamiltonianAtQ/S ⇒ hamiltonianAtQ/_1
unkinded flow: hamiltonianAtQ/xₜ ⇒ hamiltonianAtQ/_1
unkinded flow: hamiltonianAtQ/t ⇒ hamiltonianAtQ/_1
unkinded input accelerationAtQ/xₜ : Time → EuclideanSpace ℝ (Fin 1)
unkinded input accelerationAtQ/t : Time
unkinded flow: accelerationAtQ/xₜ ⇒ accelerationAtQ/_1
unkinded flow: accelerationAtQ/t ⇒ accelerationAtQ/_1
unkinded input forceAtQ/S : ClassicalMechanics.HarmonicOscillator
unkinded input forceAtQ/xₜ : Time → EuclideanSpace ℝ (Fin 1)
unkinded input forceAtQ/t : Time
unkinded flow: forceAtQ/S ⇒ forceAtQ/_1
unkinded flow: forceAtQ/xₜ ⇒ forceAtQ/_1
unkinded flow: forceAtQ/t ⇒ forceAtQ/_1
unkinded input durationQ/t : Time
unkinded flow: durationQ/t ⇒ durationQ/_1
unkinded input displacement0Q/IC : ClassicalMechanics.HarmonicOscillator.InitialConditions
unkinded flow: displacement0Q/IC ⇒ displacement0Q/_1
unkinded input velocity0Q/IC : ClassicalMechanics.HarmonicOscillator.InitialConditions
unkinded flow: velocity0Q/IC ⇒ velocity0Q/_1
unkinded input rbMassQ/R : RigidBody d
unkinded flow: rbMassQ/R ⇒ rbMassQ/_1
unkinded input inertiaAtQ/R : RigidBody d
unkinded input inertiaAtQ/i : Fin d
unkinded input inertiaAtQ/j : Fin d
unkinded flow: inertiaAtQ/R ⇒ inertiaAtQ/_1
unkinded flow: inertiaAtQ/i ⇒ inertiaAtQ/_1
unkinded flow: inertiaAtQ/j ⇒ inertiaAtQ/_1
unkinded input omegaCompQ/ωv : Fin 3 → ℝ
unkinded input omegaCompQ/j : Fin 3
unkinded flow: omegaCompQ/ωv ⇒ omegaCompQ/_1
unkinded flow: omegaCompQ/j ⇒ omegaCompQ/_1
unkinded input translationalKEQ/M : RigidBodyMotion 3
unkinded input translationalKEQ/t : Time
unkinded flow: translationalKEQ/M ⇒ translationalKEQ/_1
unkinded flow: translationalKEQ/t ⇒ translationalKEQ/_1
unkinded input rotationalKEQ/M : RigidBodyMotion 3
unkinded input rotationalKEQ/t : Time
unkinded flow: rotationalKEQ/M ⇒ rotationalKEQ/_1
unkinded flow: rotationalKEQ/t ⇒ rotationalKEQ/_1
unkinded input velocityAtQ/xₜ : Time → EuclideanSpace ℝ (Fin 1)
unkinded input velocityAtQ/t : Time
unkinded flow: velocityAtQ/xₜ ⇒ velocityAtQ/_1
unkinded flow: velocityAtQ/t ⇒ velocityAtQ/_1
unkinded input displacementE1Q/xₜ : Time → EuclideanSpace ℝ (Fin 1)
unkinded input displacementE1Q/t : Time
unkinded flow: displacementE1Q/xₜ ⇒ displacementE1Q/_1
unkinded flow: displacementE1Q/t ⇒ displacementE1Q/_1
unkinded input velocityE1Q/xₜ : Time → EuclideanSpace ℝ (Fin 1)
unkinded input velocityE1Q/t : Time
unkinded flow: velocityE1Q/xₜ ⇒ velocityE1Q/_1
unkinded flow: velocityE1Q/t ⇒ velocityE1Q/_1
unkinded input phaseOffsetQ/S : ClassicalMechanics.HarmonicOscillator
unkinded input phaseOffsetQ/IC : ClassicalMechanics.HarmonicOscillator.InitialConditions
unkinded flow: phaseOffsetQ/S ⇒ phaseOffsetQ/_1
unkinded flow: phaseOffsetQ/IC ⇒ phaseOffsetQ/_1
unkinded input energyRateQ/S : ClassicalMechanics.HarmonicOscillator
unkinded input energyRateQ/xₜ : Time → EuclideanSpace ℝ (Fin 1)
unkinded input energyRateQ/t : Time
unkinded flow: energyRateQ/S ⇒ energyRateQ/_1
unkinded flow: energyRateQ/xₜ ⇒ energyRateQ/_1
unkinded flow: energyRateQ/t ⇒ energyRateQ/_1
unkinded input geometricKineticEnergyQ/S : ClassicalMechanics.HarmonicOscillator
unkinded input geometricKineticEnergyQ/q : ClassicalMechanics.HarmonicOscillator.ConfigurationSpace
unkinded input geometricKineticEnergyQ/v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) q
unkinded flow: geometricKineticEnergyQ/S ⇒ geometricKineticEnergyQ/_1
unkinded flow: geometricKineticEnergyQ/q ⇒ geometricKineticEnergyQ/_1
unkinded flow: geometricKineticEnergyQ/v ⇒ geometricKineticEnergyQ/_1
unkinded input comQ/R : RigidBody d
unkinded input comQ/i : Fin d
unkinded flow: comQ/R ⇒ comQ/_1
unkinded flow: comQ/i ⇒ comQ/_1
unkinded input inertiaAboutAtQ/R : RigidBody d
unkinded input inertiaAboutAtQ/p : Space d
unkinded input inertiaAboutAtQ/i : Fin d
unkinded input inertiaAboutAtQ/j : Fin d
unkinded flow: inertiaAboutAtQ/R ⇒ inertiaAboutAtQ/_1
unkinded flow: inertiaAboutAtQ/p ⇒ inertiaAboutAtQ/_1
unkinded flow: inertiaAboutAtQ/i ⇒ inertiaAboutAtQ/_1
unkinded flow: inertiaAboutAtQ/j ⇒ inertiaAboutAtQ/_1
unkinded input omegaTensorAtQ/M : RigidBodyMotion d
unkinded input omegaTensorAtQ/t : Time
unkinded input omegaTensorAtQ/i : Fin d
unkinded input omegaTensorAtQ/j : Fin d
unkinded flow: omegaTensorAtQ/M ⇒ omegaTensorAtQ/_1
unkinded flow: omegaTensorAtQ/t ⇒ omegaTensorAtQ/_1
unkinded flow: omegaTensorAtQ/i ⇒ omegaTensorAtQ/_1
unkinded flow: omegaTensorAtQ/j ⇒ omegaTensorAtQ/_1
unkinded input bodyOmegaTensorAtQ/M : RigidBodyMotion d
unkinded input bodyOmegaTensorAtQ/t : Time
unkinded input bodyOmegaTensorAtQ/i : Fin d
unkinded input bodyOmegaTensorAtQ/j : Fin d
unkinded flow: bodyOmegaTensorAtQ/M ⇒ bodyOmegaTensorAtQ/_1
unkinded flow: bodyOmegaTensorAtQ/t ⇒ bodyOmegaTensorAtQ/_1
unkinded flow: bodyOmegaTensorAtQ/i ⇒ bodyOmegaTensorAtQ/_1
unkinded flow: bodyOmegaTensorAtQ/j ⇒ bodyOmegaTensorAtQ/_1
unkinded input comVelocityAtQ/M : RigidBodyMotion d
unkinded input comVelocityAtQ/t : Time
unkinded input comVelocityAtQ/i : Fin d
unkinded flow: comVelocityAtQ/M ⇒ comVelocityAtQ/_1
unkinded flow: comVelocityAtQ/t ⇒ comVelocityAtQ/_1
unkinded flow: comVelocityAtQ/i ⇒ comVelocityAtQ/_1
unkinded input relPositionAtQ/M : RigidBodyMotion d
unkinded input relPositionAtQ/t : Time
unkinded input relPositionAtQ/y : Space d
unkinded input relPositionAtQ/j : Fin d
unkinded flow: relPositionAtQ/M ⇒ relPositionAtQ/_1
unkinded flow: relPositionAtQ/t ⇒ relPositionAtQ/_1
unkinded flow: relPositionAtQ/y ⇒ relPositionAtQ/_1
unkinded flow: relPositionAtQ/j ⇒ relPositionAtQ/_1
unkinded input omegaVecAtQ/M : RigidBodyMotion 3
unkinded input omegaVecAtQ/t : Time
unkinded input omegaVecAtQ/i : Fin 3
unkinded flow: omegaVecAtQ/M ⇒ omegaVecAtQ/_1
unkinded flow: omegaVecAtQ/t ⇒ omegaVecAtQ/_1
unkinded flow: omegaVecAtQ/i ⇒ omegaVecAtQ/_1
unkinded input displacementAtQ/xₜ : Time → EuclideanSpace ℝ (Fin 1)
unkinded input displacementAtQ/t : Time
unkinded flow: displacementAtQ/xₜ ⇒ displacementAtQ/_1
unkinded flow: displacementAtQ/t ⇒ displacementAtQ/_1
unkinded input rawTrajectoryValue/S : ClassicalMechanics.HarmonicOscillator
unkinded input rawTrajectoryValue/IC : ClassicalMechanics.HarmonicOscillator.InitialConditions
unkinded input rawTrajectoryValue/t : Time
unkinded output rawTrajectoryValue/result : ℝ
-/
#guard_msgs (whitespace := lax) in #kind_unkinded ingestBoundary

end ForPhysLib.ClassicalMechanics.Audits
