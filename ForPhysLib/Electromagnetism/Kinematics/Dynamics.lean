/-
# The variational subtree, kinded — Lagrangian, Euler–Lagrange, Legendre, Hamiltonian

`Dynamics/` derives the chain's field equations instead of postulating them:
`kineticTerm` (`−¼μ₀⁻¹F·F`), `freeCurrentPotential` (`⟪A, J⟫ₘ`), their difference the
`lagrangian`, its variational gradient `gradLagrangian`, the extremal condition
`IsExtrema` (which `ThreeDimension/MaxwellEquations.lean` turns into the four laws
this directory's `Maxwell.lean` kindes), and the Legendre pair
`canonicalMomentum`/`hamiltonian`. This file re-reads that subtree through the kind
layer — two catalogue lookups (the energy density 6-33, the linear current density
6-9), three mints, six edges — and finds:

* **The whole variational calculus is same-kind after edges — still no join.** Both
  Lagrangian terms land at the minted Lagrangian density (`L = L_kin − A·J` is a
  same-kind subtraction, pinned by `rfl`); both variational-gradient spellings land at
  the Euler–Lagrange mint (`gradLagrangian = gradKineticTerm − gradFreeCurrentPotential`
  is another, upstream's own lemma); the Legendre transform `H = π·∂₀A − L` is a third.
  The chain's zero-`KindJoin` finding survives its own derivation tree.

* **The variational readings are the same-dimension discrimination again, at three new
  dimensions.** `L` sits at the energy density's J/m³ and is not 6-33 (it is
  gauge-dependent — `lagrangian_add_const` moves it, `kineticTerm_add_const` pins that
  only its kinetic part is invariant); `δS/δA` sits at the current density's A/m² and
  is not 6-8 (Euler–Lagrange *equates* it to sources through an edge); `π` sits at
  6-9's A/m and is not 6-9. Each separation is a `decide` in `Kinds.lean`.

* **The Hamiltonian is the catalogue's own 6-33, by upstream's theorem.**
  `hamiltonian_eq_electricField_magneticField` writes `H` as `½ε₀‖E‖²` plus the
  magnetic square plus source terms — the identification that licenses the one
  crossing in this file whose target is a lookup rather than a mint.

* **`FreeSpace` is two catalogue constants and a definition.** `ε₀` and `μ₀` are
  6-14.1 and 6-26.1 (already `Maxwell.lean`'s `@[kindConst]` readings); `FreeSpace.c`
  is *defined* as `1/√(ε₀μ₀)` — the `freeSpaceSpeedQ` crossing below, whose
  dimensional necessity `Maxwell.lean` already decided (`μ₀ε₀c²` dimensionless).

* **One stale TODO upstream.** `KineticTerm.lean` and `Lagrangian.lean` both still say
  "In this implementation we have set `μ₀ = 1`. It is a TODO to introduce this
  constant" — but the constant *is* introduced: every definition in the subtree takes
  `𝓕 : FreeSpace` and the kinetic term reads `−1/(4·𝓕.μ₀)`. A two-line docstring
  patch candidate.

The six edges are all law-only: their arithmetic lives inside the variational `δ`,
the tensor contraction, and `∂_` — which no table sees. The directory's Stage-3
registration count is unchanged.
-/

module

public import ForPhysLib.Electromagnetism.Kinematics.Maxwell
meta import ForPhysLib.Electromagnetism.Kinematics.Maxwell
public import Physlib.Electromagnetism.Dynamics.Hamiltonian
meta import Physlib.Electromagnetism.Dynamics.Hamiltonian
public import Physlib.Electromagnetism.Dynamics.IsExtrema
meta import Physlib.Electromagnetism.Dynamics.IsExtrema

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open PropertyKindCalculus
open Electromagnetism
open Time Space SpaceTime ElectromagneticPotential ContDiff
open TensorSpecies Tensor minkowskiMatrix InnerProductSpace RealInnerProductSpace
open Lorentz.Vector
open ForPhysLib.Electromagnetism.Kinematics
open ForPhysLib.Electromagnetism.Kinematics.Kinds
open ForPhysLib.Electromagnetism.Kinematics.Maxwell

namespace ForPhysLib.Electromagnetism.Kinematics.Dynamics

noncomputable section

variable {d : ℕ}

/-! ## The speed of light, from its two constants

Upstream *defines* `FreeSpace.c := 1/√(ε₀μ₀)`; `Maxwell.lean` decided that this is
the only dimensionally coherent choice. The crossing reads that definition at 6-35.2
from the two `@[kindConst]` readings — positivity travels as hypotheses because
`FreeSpace` carries it as fields. -/

/-- `c = 1/√(ε₀·μ₀)` — upstream's definition of `FreeSpace.c`, read at the speed of
light from the two catalogue constants. -/
@[kindCrossing]
def freeSpaceSpeedQ (εq : Quantity electricConstant ℝ)
    (μq : Quantity magneticConstant ℝ)
    (hε : 0 < εq.magnitude) (hμ : 0 < μq.magnitude) :
    Quantity speedOfLightK SpeedOfLight :=
  .attest "c = 1/√(ε₀·μ₀) — FreeSpace.c, the defined constant"
    (FreeSpace.c ⟨εq.magnitude, μq.magnitude, hε, hμ⟩)

/-- The crossing erases to upstream's own constant — `FreeSpace` rebuilt from its two
kinded readings *is* `𝓕`, definitionally (structure eta). -/
theorem freeSpaceSpeedQ_magnitude (𝓕 : FreeSpace) :
    (freeSpaceSpeedQ (epsilonQ 𝓕) (muQ 𝓕) 𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude = 𝓕.c := rfl

/-! ## The Lagrangian density — two products, one kind, no join -/

/-- `⟪A, J⟫ₘ` — the interaction density, on the `A·J` edge
(`magneticVectorPotential · electricCurrentDensity → lagrangianDensity`). -/
@[kindCrossing]
def freeCurrentPotentialQ
    (Aq : Quantity vectorPotentialK (ElectromagneticPotential d))
    (Jq : Quantity electricCurrentDensity (LorentzCurrentDensity d)) :
    Quantity lagrangianDensity (SpaceTime d → ℝ) :=
  .attest "⟪A, J⟫ₘ — the interaction density; the Minkowski product is unseen by any table"
    (fun x => Aq.magnitude.freeCurrentPotential Jq.magnitude x)

/-- `−¼μ₀⁻¹·F·F` — the kinetic term, riding the `π` edge
(`fieldStrength / magneticConstant`) and the `π·F` edge; the contraction lives inside
the tensor expression, unseen. -/
@[kindCrossing]
def kineticTermQ (εq : Quantity electricConstant ℝ)
    (μq : Quantity magneticConstant ℝ)
    (Aq : Quantity vectorPotentialK (ElectromagneticPotential d))
    (hε : 0 < εq.magnitude) (hμ : 0 < μq.magnitude) :
    Quantity lagrangianDensity (SpaceTime d → ℝ) :=
  .attest "−¼μ₀⁻¹·F·F — the kinetic term at the gauge-dependent density mint"
    (Aq.magnitude.kineticTerm ⟨εq.magnitude, μq.magnitude, hε, hμ⟩)

/-- `L = L_kin − ⟪A, J⟫ₘ` — the Lagrangian density: the same-kind subtraction the two
product edges make possible. -/
@[kindCrossing]
def lagrangianQ (εq : Quantity electricConstant ℝ)
    (μq : Quantity magneticConstant ℝ)
    (Aq : Quantity vectorPotentialK (ElectromagneticPotential d))
    (Jq : Quantity electricCurrentDensity (LorentzCurrentDensity d))
    (hε : 0 < εq.magnitude) (hμ : 0 < μq.magnitude) :
    Quantity lagrangianDensity (SpaceTime d → ℝ) :=
  .attest "L = kineticTerm − freeCurrentPotential — a same-kind subtraction, no join"
    (Aq.magnitude.lagrangian ⟨εq.magnitude, μq.magnitude, hε, hμ⟩ Jq.magnitude)

variable (𝓕 : FreeSpace) (A : ElectromagneticPotential d)
  (J : LorentzCurrentDensity d)

/-- **The subtraction is definitional**: the kinded Lagrangian is the kinded kinetic
term minus the kinded interaction, pointwise by `rfl` — the no-join finding at the
density, as a build artifact. -/
theorem lagrangianQ_magnitude_sub (x : SpaceTime d) :
    (lagrangianQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A) (currentFourQ J)
        𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude x
      = (kineticTermQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A)
          𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude x
        - (freeCurrentPotentialQ (potentialQ A) (currentFourQ J)).magnitude x := rfl

/-- **What survives a boost is the kinetic term** — upstream's Lorentz invariance,
consumed at the kinded reading: the mint's magnitude is equivariant. -/
theorem kineticTermQ_equivariant (Λ : LorentzGroup d) (hA : Differentiable ℝ A)
    (x : SpaceTime d) :
    (kineticTermQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ (Λ • A))
        𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude x
      = (kineticTermQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A)
          𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude (Λ⁻¹ • x) :=
  kineticTerm_equivariant A Λ hA x

/-- **What does not survive a gauge-like shift is the interaction** — the pair that
individuates the mint from 6-33: the kinetic part is invariant under `A ↦ A + A₀` … -/
theorem kineticTermQ_add_const (A₀ : Lorentz.Vector d) :
    (kineticTermQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ ⟨fun x => A x + A₀⟩)
        𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude
      = (kineticTermQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A)
          𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude :=
  kineticTerm_add_const A A₀

/-- … while the full Lagrangian density moves by the shifted interaction
(`lagrangian_add_const`): the reading is gauge-dependent, hence not the measurable
6-33. -/
theorem lagrangianQ_add_const (A₀ : Lorentz.Vector d) (x : SpaceTime d) :
    (lagrangianQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ ⟨fun x => A x + A₀⟩)
        (currentFourQ J) 𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude x
      = (lagrangianQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A) (currentFourQ J)
          𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude x - ⟪A₀, J x⟫ₘ :=
  lagrangian_add_const A J A₀ x

/-! ## The variational gradient — Euler–Lagrange at one kind -/

/-- `δ(∫⟪A, J⟫ₘ)/δA` — the metric-lowered current read as a variational gradient: the
*dimension-preserving re-kind* (A/m² stays A/m²; 6-8 does not survive the `δ`). -/
@[kindCrossing]
def gradFreeCurrentPotentialQ
    (Aq : Quantity vectorPotentialK (ElectromagneticPotential d))
    (Jq : Quantity electricCurrentDensity (LorentzCurrentDensity d)) :
    Quantity variationalGradient (SpaceTime d → Lorentz.Vector d) :=
  .attest "δ(∫⟪A,J⟫ₘ)/δA = η·J — the current re-kinded by the variational derivative"
    (Aq.magnitude.gradFreeCurrentPotential Jq.magnitude)

/-- `δ(∫L_kin)/δA` — the kinetic term's variational gradient, on the
`magneticFieldDerivative / magneticConstant` edge (`μ₀⁻¹·∑∂F` is upstream's own
computation of it). -/
@[kindCrossing]
def gradKineticTermQ (εq : Quantity electricConstant ℝ)
    (μq : Quantity magneticConstant ℝ)
    (Aq : Quantity vectorPotentialK (ElectromagneticPotential d))
    (hε : 0 < εq.magnitude) (hμ : 0 < μq.magnitude) :
    Quantity variationalGradient (SpaceTime d → Lorentz.Vector d) :=
  .attest "δ(∫L_kin)/δA = μ₀⁻¹·∑∂F — the Euler–Lagrange reading's field side"
    (Aq.magnitude.gradKineticTerm ⟨εq.magnitude, μq.magnitude, hε, hμ⟩)

/-- `δS/δA` — the full variational gradient, on the
`lagrangianDensity / magneticVectorPotential` edge. -/
@[kindCrossing]
def gradLagrangianQ (εq : Quantity electricConstant ℝ)
    (μq : Quantity magneticConstant ℝ)
    (Aq : Quantity vectorPotentialK (ElectromagneticPotential d))
    (Jq : Quantity electricCurrentDensity (LorentzCurrentDensity d))
    (hε : 0 < εq.magnitude) (hμ : 0 < μq.magnitude) :
    Quantity variationalGradient (SpaceTime d → Lorentz.Vector d) :=
  .attest "δS/δA — the reading IsExtrema sets to zero"
    (Aq.magnitude.gradLagrangian ⟨εq.magnitude, μq.magnitude, hε, hμ⟩ Jq.magnitude)

/-- **Euler–Lagrange is a same-kind subtraction** — upstream's
`gradLagrangian_eq_kineticTerm_sub`, consumed at the kinded readings: both spellings
of `δS/δA` land at the one mint. -/
theorem gradLagrangianQ_eq_sub (hA : ContDiff ℝ ∞ A) (hJ : ContDiff ℝ ∞ J) :
    (gradLagrangianQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A) (currentFourQ J)
        𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude
      = (gradKineticTermQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A)
          𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude
        - (gradFreeCurrentPotentialQ (potentialQ A) (currentFourQ J)).magnitude :=
  gradLagrangian_eq_kineticTerm_sub A hA J hJ

/-- **The extremal condition is the kinded reading's vanishing** — `IsExtrema`
unfolds, definitionally, to "the kinded variational gradient's magnitude is zero".
`Maxwell.lean`'s four laws consume exactly this hypothesis: the variational subtree
and the sources meet at one `Prop`. -/
theorem isExtrema_iff_kinded :
    IsExtrema 𝓕 A J ↔
      (gradLagrangianQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A) (currentFourQ J)
        𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude = 0 := Iff.rfl

/-! ## The Legendre pair — the canonical momentum and the Hamiltonian -/

/-- `π = ∂L/∂(∂₀A)` — the canonical momentum, on the
`fieldStrength / magneticConstant` edge; at 6-9's dimension and minted apart from
it. -/
@[kindCrossing]
def canonicalMomentumQ (εq : Quantity electricConstant ℝ)
    (μq : Quantity magneticConstant ℝ)
    (Aq : Quantity vectorPotentialK (ElectromagneticPotential d))
    (Jq : Quantity electricCurrentDensity (LorentzCurrentDensity d))
    (hε : 0 < εq.magnitude) (hμ : 0 < μq.magnitude) :
    Quantity canonicalMomentumDensity (SpaceTime d → Lorentz.Vector d) :=
  .attest "π = ∂L/∂(∂₀A) — the Legendre-conjugate reading"
    (Aq.magnitude.canonicalMomentum ⟨εq.magnitude, μq.magnitude, hε, hμ⟩ Jq.magnitude)

/-- **The momentum's defining edge realized** — upstream's
`canonicalMomentum_eq_electricField`: the spatial slots are `−E/(μ₀c)` (the
`F/μ₀` entry through the velocity edge), the time slot vanishes. -/
theorem canonicalMomentumQ_eq_electricField (hA : ContDiff ℝ 2 A) :
    (canonicalMomentumQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A) (currentFourQ J)
        𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude
      = fun x => fun μ =>
        match μ with
        | Sum.inl 0 => 0
        | Sum.inr i => - (1/(𝓕.μ₀ * 𝓕.c)) * A.electricField 𝓕.c (x.time 𝓕.c) x.space i :=
  canonicalMomentum_eq_electricField A hA J

/-- `H = π·∂₀A − L` — the Hamiltonian: the Legendre product rides the
`canonicalMomentumDensity · potentialGradient` edge, the subtraction is same-kind,
and the *target* is the catalogue's 6-33 — the one crossing here whose kind is a
lookup, licensed by `hamiltonian_eq_electricField_magneticField` below. -/
@[kindCrossing]
def hamiltonianQ (εq : Quantity electricConstant ℝ)
    (μq : Quantity magneticConstant ℝ)
    (Aq : Quantity vectorPotentialK (ElectromagneticPotential d))
    (Jq : Quantity electricCurrentDensity (LorentzCurrentDensity d))
    (hε : 0 < εq.magnitude) (hμ : 0 < μq.magnitude) :
    Quantity electromagneticEnergyDensity (SpaceTime d → ℝ) :=
  .attest "H = π·∂₀A − L — the Legendre transform, read at the field energy density"
    (Aq.magnitude.hamiltonian ⟨εq.magnitude, μq.magnitude, hε, hμ⟩ Jq.magnitude)

/-- **The Legendre transform is definitional at the kinded readings**: `H`'s
magnitude is the kinded `π` contracted with `∂₀A`, minus the kinded `L` — pointwise
by `rfl`. -/
theorem hamiltonianQ_legendre (x : SpaceTime d) :
    (hamiltonianQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A) (currentFourQ J)
        𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude x
      = ∑ μ, (canonicalMomentumQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A) (currentFourQ J)
            𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude x μ * ∂_ (Sum.inl 0) A x μ
        - (lagrangianQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A) (currentFourQ J)
            𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude x := rfl

/-- **The 6-33 identification, consumed** — upstream's own theorem writes the kinded
Hamiltonian's magnitude as `½ε₀‖E‖²` plus the magnetic square plus the source terms:
the license for the Legendre crossing's catalogue target. -/
theorem hamiltonianQ_eq_electricField_magneticField (hA : ContDiff ℝ 2 A)
    (x : SpaceTime d) :
    (hamiltonianQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A) (currentFourQ J)
        𝓕.ε₀_pos 𝓕.μ₀_pos).magnitude x
      = 1/2 * 𝓕.ε₀ * (‖A.electricField 𝓕.c (x.time 𝓕.c) x.space‖ ^ 2
          + 𝓕.c ^ 2 / 2 *
            ∑ i, ∑ j, ‖A.magneticFieldMatrix 𝓕.c (x.time 𝓕.c) x.space (i, j)‖ ^ 2)
        + 𝓕.ε₀ * ⟪A.electricField 𝓕.c (x.time 𝓕.c) x.space,
            Space.grad (A.scalarPotential 𝓕.c (x.time 𝓕.c) ·) x.space⟫_ℝ
        + A.scalarPotential 𝓕.c (x.time 𝓕.c) x.space
            * J.chargeDensity 𝓕.c (x.time 𝓕.c) x.space
        - ∑ i, A.vectorPotential 𝓕.c (x.time 𝓕.c) x.space i
            * J.currentDensity 𝓕.c (x.time 𝓕.c) x.space i :=
  hamiltonian_eq_electricField_magneticField A hA J x

/-! ## The collision, pinned -/

/-- A consumer of the measurable 6-33. -/
def expectsEnergyDensity
    (w : Quantity electromagneticEnergyDensity (SpaceTime d → ℝ)) :
    Quantity electromagneticEnergyDensity (SpaceTime d → ℝ) := w

-- The Lagrangian density is refused where the energy density is expected — one
-- dimension (J/m³), two kinds, separated by gauge behavior.
#check_failure fun (𝓕 : FreeSpace) (A : ElectromagneticPotential 3)
    (J : LorentzCurrentDensity 3) =>
  expectsEnergyDensity (lagrangianQ (epsilonQ 𝓕) (muQ 𝓕) (potentialQ A)
    (currentFourQ J) 𝓕.ε₀_pos 𝓕.μ₀_pos)

end

end ForPhysLib.Electromagnetism.Kinematics.Dynamics

end -- pkc-blanket-expose
end -- pkc-blanket
