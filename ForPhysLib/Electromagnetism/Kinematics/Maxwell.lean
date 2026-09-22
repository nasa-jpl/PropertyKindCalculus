/-
# Maxwell's equations, kinded — the chain meets its sources

`ThreeDimension/MaxwellEquations.lean` proves the four laws from the variational
condition `IsExtrema`; this file re-reads them through the kind layer, with the
Stage-0/1 vocabulary extended by exactly what the sources need — four catalogue
lookups (charge density 6-3, current density 6-8, the electric constant 6-14.1, the
magnetic constant 6-26.1), three derivative-reading mints, and seven law-only edges
(Metrology's Maxwell block). What the reading finds:

* **Every law is a same-kind equation after edges — still no join.** `∇⬝E` and `ρ/ε₀`
  both land at the electric-field derivative; `∇⨯B`, `μ₀J` and `μ₀ε₀∂ₜE` all at the
  magnetic-field derivative; Faraday's two sides at the electric-field derivative.
  The chain's zero-`KindJoin` finding survives its collision with the sources.

* **The displacement current is the catalogue's own item**: `ε₀·∂ₜE` lands at 6-8 —
  the edge `electricConstant · electricFieldRate → electricCurrentDensity` — so
  Ampère's right side is `μ₀·(J + ε₀∂ₜE)`, a same-kind sum inside one edge.

* **`J^μ` is one kind for the same reason `A^μ` was**: the time slot stores `c·ρ`,
  and `c·(6-3)` has 6-8's dimension — the velocity edge again, one level down.

* **`c = 1/√(ε₀μ₀)` is dimensionally forced**: `μ₀·ε₀·c²` is dimensionless, decided
  in the catalogue's own dimension group — upstream's *definition* of `FreeSpace.c`
  is the only dimensionally coherent choice.

And one finding the reading did not go looking for: **Maxwell's four laws are
module-private upstream.** `ThreeDimension/MaxwellEquations.lean` is the one file in
its subtree with no `@[expose] public section`, so `gaussLawElectric`, `ampereLaw`,
`faradayLaw` and `gaussLawMagnetic` cannot be named by any downstream consumer — the
`#check_failure` below is that absence as a build artifact. The kinded laws are
therefore *re-proved* here with upstream's own one-liners against the exported API
(`isExtrema_iff_gauss_ampere_magneticFieldMatrix`, `magneticField_eq_3D`, …); the
patch candidate is a single line.
-/

module

public import ForPhysLib.Electromagnetism.Kinematics.Kinded
meta import ForPhysLib.Electromagnetism.Kinematics.Kinded
public import Physlib.Electromagnetism.ThreeDimension.MaxwellEquations
meta import Physlib.Electromagnetism.ThreeDimension.MaxwellEquations

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open PropertyKindCalculus
open Electromagnetism
open Time Space ElectromagneticPotential ContDiff
open ForPhysLib.Electromagnetism.Kinematics
open ForPhysLib.Electromagnetism.Kinematics.Kinds

namespace ForPhysLib.Electromagnetism.Kinematics.Maxwell

noncomputable section

variable (𝓕 : FreeSpace) (V : ElectromagneticPotential 3)
  (J₄ : LorentzCurrentDensity 3)

/-! ## The constants and the sources, at their kinds -/

/-- `FreeSpace.ε₀`, read at 6-14.1 — a bare `ℝ` field upstream; the F/m commitment
lives here. -/
@[kindConst]
def epsilonQ : Quantity electricConstant ℝ :=
  .attest "FreeSpace.ε₀ — the electric constant, a bare ℝ field upstream" 𝓕.ε₀

/-- `FreeSpace.μ₀`, read at 6-26.1. -/
@[kindConst]
def muQ : Quantity magneticConstant ℝ :=
  .attest "FreeSpace.μ₀ — the magnetic constant, a bare ℝ field upstream" 𝓕.μ₀

/-- `J^μ` — homogeneous at 6-8 for the same reason `A^μ` was homogeneous at 6-32:
the time slot stores `c·ρ`, one velocity edge below. -/
@[kindIngest]
def currentFourQ {d : ℕ} (J₄ : LorentzCurrentDensity d) :
    Quantity electricCurrentDensity (LorentzCurrentDensity d) :=
  .attest "J^μ — one kind; the time slot is c·ρ" J₄

/-- `ρ = J⁰/c` — the velocity edge down to 6-3, the mirror of `φ = c·A⁰`. -/
@[kindCrossing]
def chargeDensitySliceQ (cq : Quantity speedOfLightK SpeedOfLight)
    (Jq : Quantity electricCurrentDensity (LorentzCurrentDensity 3)) :
    Quantity electricChargeDensity (Time → Space → ℝ) :=
  .attest "J⁰/c — the velocity edge down to the charge density"
    (Jq.magnitude.chargeDensity cq.magnitude)

/-- The spatial current slice, at its own kind — `timeSlice` re-parameterizes, the
kind is unchanged. -/
@[kindCrossing]
def currentDensitySliceQ (cq : Quantity speedOfLightK SpeedOfLight)
    (Jq : Quantity electricCurrentDensity (LorentzCurrentDensity 3)) :
    Quantity electricCurrentDensity (Time → Space → EuclideanSpace ℝ (Fin 3)) :=
  .attest "the spatial slice — same kind; timeSlice re-parameterizes"
    (Jq.magnitude.currentDensity cq.magnitude)

/-! ## The laws' sides, each on its Metrology edge -/

/-- `∇⬝E` — the per-length edge `electricFieldStrength / length`; `∇` is Mathlib's
`fderiv`, unseen by any table. -/
@[kindCrossing]
def divergenceEQ
    (Eq : Quantity electricFieldK (Time → Space → EuclideanSpace ℝ (Fin 3))) :
    Quantity electricFieldDerivative (Time → Space → ℝ) :=
  .attest "∇⬝E — the electric per-length edge, fderiv unseen"
    (fun t x => (∇ ⬝ Eq.magnitude t) x)

/-- `ρ/ε₀` — Gauss's source, on the edge
`electricChargeDensity / electricConstant`. -/
@[kindCrossing]
def gaussSourceQ (ρq : Quantity electricChargeDensity (Time → Space → ℝ))
    (εq : Quantity electricConstant ℝ) :
    Quantity electricFieldDerivative (Time → Space → ℝ) :=
  .attest "ρ/ε₀ — Gauss's source edge"
    (fun t x => ρq.magnitude t x / εq.magnitude)

/-- `∇⬝B` — the magnetic per-length edge; Gauss-magnetic's left side. -/
@[kindCrossing]
def divergenceBQ
    (Bq : Quantity magneticFluxDensityK (Time → Space → EuclideanSpace ℝ (Fin 3))) :
    Quantity magneticFieldDerivative (Time → Space → ℝ) :=
  .attest "∇⬝B — the magnetic per-length edge"
    (fun t x => (∇ ⬝ Bq.magnitude t) x)

/-- `∇⨯E` — entrywise on the same electric per-length edge. -/
@[kindCrossing]
def curlEQ
    (Eq : Quantity electricFieldK (Time → Space → EuclideanSpace ℝ (Fin 3))) :
    Quantity electricFieldDerivative (Time → Space → EuclideanSpace ℝ (Fin 3)) :=
  .attest "∇⨯E — the electric per-length edge, entrywise"
    (fun t x => (∇ ⨯ Eq.magnitude t) x)

/-- `-∂ₜB` — Faraday's right side, on `magneticFluxDensity / duration`
(`T/s = V/m²`). -/
@[kindCrossing]
def negTimeDerivBQ
    (Bq : Quantity magneticFluxDensityK (Time → Space → EuclideanSpace ℝ (Fin 3))) :
    Quantity electricFieldDerivative (Time → Space → EuclideanSpace ℝ (Fin 3)) :=
  .attest "-∂ₜB — the flux density per duration edge"
    (fun t x => - ∂ₜ (fun t => Bq.magnitude t x) t)

/-- `∇⨯B` — Ampère's left side, on `magneticFluxDensity / length`. -/
@[kindCrossing]
def curlBQ
    (Bq : Quantity magneticFluxDensityK (Time → Space → EuclideanSpace ℝ (Fin 3))) :
    Quantity magneticFieldDerivative (Time → Space → EuclideanSpace ℝ (Fin 3)) :=
  .attest "∇⨯B — the magnetic per-length edge, entrywise"
    (fun t x => (∇ ⨯ Bq.magnitude t) x)

/-- `μ₀J + μ₀ε₀∂ₜE` — Ampère's source: `ε₀∂ₜE` lands at 6-8 (the displacement
current, the catalogue's own item), so the sum inside is *same-kind* and the whole
side rides `magneticConstant · electricCurrentDensity` — no join. -/
@[kindCrossing]
def ampereSourceQ (μq : Quantity magneticConstant ℝ)
    (εq : Quantity electricConstant ℝ)
    (Jq : Quantity electricCurrentDensity (Time → Space → EuclideanSpace ℝ (Fin 3)))
    (Eq : Quantity electricFieldK (Time → Space → EuclideanSpace ℝ (Fin 3))) :
    Quantity magneticFieldDerivative (Time → Space → EuclideanSpace ℝ (Fin 3)) :=
  .attest "μ₀·(J + ε₀∂ₜE) — one edge over a same-kind sum"
    (fun t x => μq.magnitude • Jq.magnitude t x
      + μq.magnitude • εq.magnitude • ∂ₜ (fun t => Eq.magnitude t x) t)

/-! ## The kinded field readings this file consumes -/

/-- The chain's built `E`, at `d = 3` — `Kinded.electricFieldFromPotentialsQ`
specialized; its magnitude *is* upstream's `V.electricField 𝓕.c`. -/
def electricFieldQ :
    Quantity electricFieldK (Time → Space → EuclideanSpace ℝ (Fin 3)) :=
  Kinded.electricFieldFromPotentialsQ (speedQ 𝓕.c) (potentialQ V)

/-- The chain's built `B`, at `d = 3`. -/
def magneticFieldQ :
    Quantity magneticFluxDensityK (Time → Space → EuclideanSpace ℝ (Fin 3)) :=
  Kinded.magneticFieldFromPotentialQ (speedQ 𝓕.c) (potentialQ V)

/-! ## The four laws — re-proved, since upstream's are module-private -/

-- The upstream theorems exist but are not exported — the missing `public section`.
#check_failure Electromagnetism.ThreeDimension.gaussLawElectric

/-- **Gauss, electric, kinded**: both sides at the electric-field derivative. The
proof is upstream's own, re-run because `gaussLawElectric` is module-private. -/
theorem gaussElectric_kinded (h : IsExtrema 𝓕 V J₄) (hV : ContDiff ℝ ∞ V)
    (hJ : ContDiff ℝ ∞ J₄) (t : Time) (x : Space) :
    (divergenceEQ (electricFieldQ 𝓕 V)).magnitude t x
      = (gaussSourceQ (chargeDensitySliceQ (speedQ 𝓕.c) (currentFourQ J₄))
          (epsilonQ 𝓕)).magnitude t x := by
  show (∇ ⬝ ((electricFieldQ 𝓕 V).magnitude t)) x
      = J₄.chargeDensity 𝓕.c t x / 𝓕.ε₀
  rw [electricFieldQ, Kinded.electricFieldFromPotentialsQ_magnitude]
  exact ((isExtrema_iff_gauss_ampere_magneticFieldMatrix hV J₄ hJ (𝓕 := 𝓕)).mp h t x).1

/-- **Gauss, magnetic, kinded**: the magnetic per-length reading vanishes. -/
theorem gaussMagnetic_kinded (hV : ContDiff ℝ ∞ V) (t : Time) (x : Space) :
    (divergenceBQ (magneticFieldQ 𝓕 V)).magnitude t x = 0 := by
  show (∇ ⬝ ((magneticFieldQ 𝓕 V).magnitude t)) x = 0
  rw [magneticFieldQ, Kinded.magneticFieldFromPotentialQ_magnitude,
    _root_.Electromagnetism.ThreeDimension.magneticField_eq_3D, div_of_curl_eq_zero _ (by fun_prop), Pi.zero_apply]

/-- **Ampère, kinded**: both sides at the magnetic-field derivative. -/
theorem ampere_kinded (h : IsExtrema 𝓕 V J₄) (hV : ContDiff ℝ ∞ V)
    (hJ : ContDiff ℝ ∞ J₄) (t : Time) (x : Space) :
    (curlBQ (magneticFieldQ 𝓕 V)).magnitude t x
      = (ampereSourceQ (muQ 𝓕) (epsilonQ 𝓕)
          (currentDensitySliceQ (speedQ 𝓕.c) (currentFourQ J₄))
          (electricFieldQ 𝓕 V)).magnitude t x := by
  show (∇ ⨯ ((magneticFieldQ 𝓕 V).magnitude t)) x
      = 𝓕.μ₀ • J₄.currentDensity 𝓕.c t x
        + 𝓕.μ₀ • 𝓕.ε₀ • ∂ₜ (fun t => (electricFieldQ 𝓕 V).magnitude t x) t
  rw [electricFieldQ, magneticFieldQ, Kinded.electricFieldFromPotentialsQ_magnitude,
    Kinded.magneticFieldFromPotentialQ_magnitude]
  ext i
  have hdE := ((isExtrema_iff_gauss_ampere_magneticFieldMatrix hV J₄ hJ
    (𝓕 := 𝓕)).mp h t x).2 i
  rw [← magneticField_curl_eq_magneticFieldMatrix _ (hV.of_le ENat.LEInfty.out)] at hdE
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, ← mul_assoc, hdE,
    add_sub_cancel]

/-- **Faraday, kinded**: both sides at the electric-field derivative. -/
theorem faraday_kinded (hV : ContDiff ℝ ∞ V) (t : Time) (x : Space) :
    (curlEQ (electricFieldQ 𝓕 V)).magnitude t x
      = (negTimeDerivBQ (magneticFieldQ 𝓕 V)).magnitude t x := by
  show (∇ ⨯ ((electricFieldQ 𝓕 V).magnitude t)) x
      = - ∂ₜ (fun t => (magneticFieldQ 𝓕 V).magnitude t x) t
  rw [electricFieldQ, magneticFieldQ, Kinded.electricFieldFromPotentialsQ_magnitude,
    Kinded.magneticFieldFromPotentialQ_magnitude,
    _root_.Electromagnetism.ThreeDimension.electricField_eq_3D,
    _root_.Electromagnetism.ThreeDimension.magneticField_eq_3D, fun_curl_sub, fun_curl_neg,
    curl_of_grad_eq_zero, time_deriv_curl_commute]
  simp only [neg_zero, Pi.zero_apply, zero_sub]
  all_goals fun_prop

/-! ## The dimensional closure of `c` -/

/-- `μ₀·ε₀·c²` is dimensionless, in the catalogue's own dimension group: upstream's
`c = 1/√(ε₀μ₀)` is the only dimensionally coherent definition of `FreeSpace.c`. -/
example : Iso80000.Part6.EDim.permeability * Iso80000.Part6.EDim.permittivity
    * Dim.speed * Dim.speed = 1 := by decide

end

end ForPhysLib.Electromagnetism.Kinematics.Maxwell

end -- pkc-blanket-expose
end -- pkc-blanket
