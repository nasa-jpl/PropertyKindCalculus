/-
# Stage 2 — kinded re-authoring of `Physlib/QuantumMechanics/HarmonicOscillator`

The third rung of [the adoption ladder](../../PLAN.md#stage-2-kinded-re-authoring-with-definitional-erasure)
for the pilot directory, plus the first three items of the
[Stage-2 metrological TODO slate](../../PLAN.md#the-pilot-quantummechanicsharmonicoscillator)
— the metrology the upstream TODO list could not ask for, because the vocabulary to
state it does not exist without the kind layer.

**The re-authoring.** `Feasibility.lean` already delivered two of the directory's
erasures (`hamiltonianOpQ_eq` and `xiQ_eq`, both against the 1D file); this stage adds
the `d`-dimensional forms it deliberately held:

  * `eigenEnergyQ` — the mode family aggregated *at the kind layer*: a
    `DifferenceKind`-licensed fold of `Quantity.add` over the modes, erasing to
    PhysLib's `eigenEnergy` (`eigenEnergyQ_magnitude`). The scale gate is the
    aggregation license F4b said Stage 2 would pay.
  * `xiQd` — the `d`-dimensional `ξ i`, radicand-first through the registered chain
    with one attested root. Its erasure to PhysLib's *root-first* `Q.ξ i` is exactly
    the F2 respelling theorem — the one place the naked form is a proved `ξ_sq`
    consequence rather than a `rfl`, because the source's own spelling is the one that
    does not survive kinding.
  * `positionOfDimensionless` — `ξEquiv` read at kinds: the rescaling that carries a
    dimensionless coordinate to a position, per component the authored
    `x/ξ` edge run backwards.

**M-T1 — the Born density is the kinded object.** `|ψ|²` is a probability density over
position (`bornDensityQ`); ψ itself carries the half-power dimension `L^(−d/2)` and is
named by **no kind, on purpose** — F2's radicand-first rule recurring at the states
(the `1/√ξᵢ` in each `eigenCoeff` is that root's trace in the source). The discharged
orthonormality theorem then makes the density's defining property a *theorem*:
`∫ρ dV = 1` (`bornDensity_integral_one`), and `totalProbabilityQ` is that integral as
the authored density × volume → probability crossing, with the `Lᵈ` coherence a
parametric theorem (`bornDensity_dim_coherent`) because `d` is the model's parameter,
not the vocabulary's. The quantum numbers are Part-10 lookups (`occupationQ`), not
mints.

**M-T2 — spacings are reference-free; the level values are not.** The eigenvalues
inherit a silently declared potential zero — `V(0) = 0` at equilibrium, a convention
riding in `potentialFunction`'s definition with no declaration anywhere in the source
(the `c := 1` pattern; pinned as `potential_zero_at_equilibrium`). Eigenvalue
*differences* cancel it: `modeSpacingQ` lands `ℏωᵢ` through the scale-gated
`Quantity.sub`, and `zeroPointEnergyQ` is the one number that reads *against* the
declared reference.

**M-T3 — the TISE is statable now.** `SatisfiesTISE` connects `hamiltonianOpQ` (F1)
with `eigenEnergyQ` through the eigenstate; the `E •` on its right-hand side is F1d's
crossing recurring in the subject's defining equation, attested once (`energySMul`).
The *proof* is the upstream analysis TODO; the kinded *statement* needs only this
vocabulary.
-/

import ForPhysLib.QuantumMechanics.HarmonicOscillator.Metrology
import ForPhysLib.QuantumMechanics.HarmonicOscillator.Feasibility
import ForPhysLib.QuantumMechanics.HarmonicOscillator.Orthonormality
import PropertyKindCalculus.BoundaryAudit

open PropertyKindCalculus MeasureTheory Complex Real
open QuantumMechanics HarmonicOscillator SpaceDHilbertSpace SchwartzSubmodule
open InnerProductSpace
open ForPhysLib.QuantumMechanics.HarmonicOscillator
open ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinds
open ForPhysLib.QuantumMechanics.HarmonicOscillator.Orthonormality

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded

open scoped PropertyKindCalculus.OperatorTable

local notation "PhysHO" => _root_.QuantumMechanics.HarmonicOscillator

variable {d : ℕ}

noncomputable section

/-! ## One vocabulary

`Feasibility.lean`'s probe kinds and Stage 0's literals are the *same* kinds,
definitionally — the probe looked them up from the catalogue, Stage 0 copied them from
it, and both routes land on one literal. Stated once, so everything below may freely
compose Feasibility's quantities with the Stage-0 and Stage-1 vocabulary. -/

example : energyK = mechanicalEnergy := rfl
example : actionK = action := rfl
example : massK = mass := rfl
example : angularFrequencyK = angularFrequency := rfl
example : lengthK = characteristicLength := rfl
example : xiSqK = xiSqRadicand := rfl

/-! ## The mode family, aggregated at the kind layer

F4b took the mode sum at magnitudes and said the kind-level aggregation was Stage-2
work. This is that work: the fold is `Quantity.add`, whose `DifferenceKind` witness is
the metrology gate — an energy's ratio scale licenses `+` — so the aggregation is
scale-checked at every step rather than asserted once at the end. -/

/-- The energy family's scale licenses `+` — the aggregation gate, held once. -/
theorem energyDiff : DifferenceKind energyK := .ofScale

instance : Std.Commutative (α := Quantity energyK ℝ) (Quantity.add energyDiff) :=
  ⟨fun a b => Quantity.add_comm _ a b⟩
instance : Std.Associative (α := Quantity energyK ℝ) (Quantity.add energyDiff) :=
  ⟨fun a b c => Quantity.add_assoc _ a b c⟩

/-- The gated addition erases to `+` — definitionally. -/
theorem addE_magnitude (x y : Quantity energyK ℝ) :
    (Quantity.add energyDiff x y).magnitude = x.magnitude + y.magnitude := rfl

/-- **The kinded eigenvalue**: the mode energies `ℏωᵢ(nᵢ + ½)` aggregated over the
mode family by the licensed fold. -/
def eigenEnergyQ (Q : PhysHO d) (n : Fin d → ℕ) : Quantity energyK ℝ :=
  Finset.univ.fold (Quantity.add energyDiff) Quantity.zero (modeEnergyQ Q n)

/-- **The erasure**: the licensed fold *is* PhysLib's `eigenEnergy`. -/
theorem eigenEnergyQ_magnitude (Q : PhysHO d) (n : Fin d → ℕ) :
    (eigenEnergyQ Q n).magnitude = Q.eigenEnergy n := by
  have hc : Std.Commutative ((· + ·) : ℝ → ℝ → ℝ) := ⟨add_comm⟩
  have ha : Std.Associative ((· + ·) : ℝ → ℝ → ℝ) := ⟨add_assoc⟩
  rw [eigenEnergy_eq_sum_modes, Finset.sum_eq_fold]
  exact (Finset.fold_hom (op := Quantity.add energyDiff) (op' := (· + ·))
    (m := Quantity.magnitude) addE_magnitude).symm

/-- The emission boundary, stated once as a `def` so it carries its tier: downstream
code that wants the naked eigenvalue gets it here. -/
@[kindEmission]
def rawEigenEnergy (Q : PhysHO d) (n : Fin d → ℕ) : ℝ := (eigenEnergyQ Q n).magnitude

/-- **Existing theorem statements survive**: PhysLib's `eigenEnergy_strictMono` closes
the kinded comparison — the kind-gated `<` is the carrier's `<` on magnitudes, and the
magnitudes are the erasure. -/
theorem eigenEnergyQ_lt (Q : PhysHO d) {n n' : Fin d → ℕ} (h : n < n') :
    eigenEnergyQ Q n < eigenEnergyQ Q n' := by
  rw [Quantity.lt_iff, eigenEnergyQ_magnitude, eigenEnergyQ_magnitude]
  exact Q.eigenEnergy_strictMono h

/-! ## The `d`-dimensional ξ, radicand-first -/

/-- The `d`-dimensional mass, read at its kind (the 1D twin is Feasibility's `mQ`). -/
@[kindIngest]
def mQd (Q : PhysHO d) : Quantity massK ℝ := ⟨Q.m⟩

/-- The `i`th radicand `ℏ/(m·ωᵢ)` through the registered chain — two edges, landing at
length². -/
def xiSqQd (Q : PhysHO d) (i : Fin d) : Quantity xiSqK ℝ := hbarQ / mQd Q / ωQ Q i

/-- One attested root carries the radicand to the characteristic length — roots are
not a kind operation, so the crossing is adjudicated here once (F2's rule). -/
@[kindCrossing]
def xiRoot (ξsq : Quantity xiSqK ℝ) : Quantity lengthK ℝ :=
  .attest "the square root of the registered ξ² chain — roots are not a kind operation"
    (√ξsq.magnitude)

/-- The kinded `d`-dimensional characteristic length. -/
def xiQd (Q : PhysHO d) (i : Fin d) : Quantity lengthK ℝ := xiRoot (xiSqQd Q i)

/-- **The erasure — by respelling, not `rfl`, and that is the finding.** PhysLib's
`Q.ξ i` is *root-first* (`√ℏ/(√m·√ωᵢ)`), the spelling whose half-power intermediates
no kind names; the kinded form is radicand-first, and the two meet through PhysLib's
own `ξ_sq` (the F2 respelling `xi_radicand_first`). -/
theorem xiQd_magnitude (Q : PhysHO d) (i : Fin d) : (xiQd Q i).magnitude = Q.ξ i := by
  show √((xiSqQd Q i).magnitude) = Q.ξ i
  have h : (xiSqQd Q i).magnitude = (Constants.ℏ : ℝ) / (Q.m * Q.ω i) := div_div _ _ _
  rw [h, ← xi_radicand_first]

/-! ## `ξEquiv`, read at kinds

The nondimensionalization held from Feasibility: the coordinate rescaling
`xᵢ = ξᵢ·xTildeᵢ` is the authored `x/ξ → dimensionless coordinate` edge run backwards, per
component — a dimensionful rescaling whose kind-level reading is a crossing, because
the per-component `ξᵢ·` multiplication rides the equiv where no table sees it. -/

/-- `ξEquiv` at kinds: a dimensionless coordinate vector becomes a position. -/
@[kindCrossing]
def positionOfDimensionless (Q : PhysHO d)
    (xTilde : Quantity dimensionlessCoordinate (Space d)) : Quantity length (Space d) :=
  .attest "ξEquiv — the per-component ξᵢ· multiplication rides the equiv unseen"
    (Q.ξEquiv xTilde.magnitude)

/-- Per component, the crossing is the authored edge run backwards: `xᵢ = ξᵢ · xTildeᵢ`. -/
theorem positionOfDimensionless_apply (Q : PhysHO d)
    (xTilde : Quantity dimensionlessCoordinate (Space d)) (i : Fin d) :
    (positionOfDimensionless Q xTilde).magnitude i = Q.ξ i * xTilde.magnitude i := rfl

/-! ## M-T1 — the Born density and the quantum numbers -/

/-- The occupation labels, looked up from the catalogue (ISO 80000-10 item 10-13.1),
not minted: `n i` is a quantum number, and the standard already says so. -/
@[kindIngest]
def occupationQ (n : Fin d → ℕ) (i : Fin d) : Quantity quantumNumber ℕ := ⟨n i⟩

/-- **The Born density, kinded** — `|ψ|²` as a probability density over position. The
wavefunction itself is this density's root at `L^(−d/2)`: a half-power dimension named
by no kind, on purpose (F2's rule at the states; the `1/√ξᵢ` in `eigenCoeff` is the
root's trace in the source). -/
@[kindIngest]
def bornDensityQ (Q : PhysHO d) (n : Fin d → ℕ) :
    Quantity bornDensity (Space d → ℝ) := ⟨fun x => ‖Q.eigenfunction n x‖ ^ 2⟩

/-- **The density's defining property is now a theorem**: the diagonal of the
discharged orthonormality is exactly `∫ |ψₙ|² = 1`. -/
theorem bornDensity_integral_one (Q : PhysHO d) (n : Fin d → ℕ) :
    ∫ x : Space d, (bornDensityQ Q n).magnitude x = 1 := by
  have h := eigenstates_orthonormal' Q n n
  simp only [KroneckerDelta.eq_one_of_same n, Nat.cast_one] at h
  rw [HarmonicOscillator.eigenstate_eq, ← Submodule.coe_inner, schwartzEquiv_inner] at h
  have hpt : ∀ x : Space d,
      (starRingEnd ℂ) (Q.eigenfunction n x) * Q.eigenfunction n x
        = ((‖Q.eigenfunction n x‖ ^ 2 : ℝ) : ℂ) := by
    intro x; rw [Complex.conj_mul']; push_cast; ring
  simp_rw [hpt, integral_complex_ofReal] at h
  exact_mod_cast h

/-- **Density × volume crosses to probability** — the integral `∫ρ dV` aggregates the
authored `bornDensity · spatialVolume → probability` edge, but the aggregation is
Mathlib's `∫`, which no kind table sees: an authored crossing, adjudicated once. -/
@[kindCrossing]
def totalProbabilityQ (ρ : Quantity bornDensity (Space d → ℝ)) :
    Quantity probability ℝ :=
  .attest "∫ρ dV — the density · volume edge aggregated by Mathlib's ∫, unseen"
    (∫ x : Space d, ρ.magnitude x)

/-- The total probability of an eigenstate is 1 — the kinded restatement. -/
theorem totalProbabilityQ_eigenstate (Q : PhysHO d) (n : Fin d → ℕ) :
    (totalProbabilityQ (bornDensityQ Q n)).magnitude = 1 :=
  bornDensity_integral_one Q n

/-- **The dimensional coherence of the density edge is parametric in `d`** — `L⁻ᵈ · Lᵈ
= 1` for every `d` — which is why the Born density and the volume element have no
Stage-1 registry pairing: their dimensions are the *model's* parameter, and the
coverage walk pins constants. The group law carries what the registry cannot. -/
theorem bornDensity_dim_coherent (d : ℕ) :
    (Dim.length ^ d)⁻¹ * Dim.length ^ d = 1 := inv_mul_cancel _

/-! ## M-T2 — spacings are reference-free; the levels are not -/

/-- **The silent reference, pinned.** The potential is declared zero at equilibrium —
`V(0) = 0` — by nothing but the *shape* of `potentialFunction`'s definition: no
docstring, no named convention, states it (Exhibit E's `(c := 1)` pattern; F3's ℏ
numeral is the directory's other instance). Every eigenvalue below reads against this
undeclared zero. -/
theorem potential_zero_at_equilibrium (Q : PhysHO d) : Q.potentialFunction 0 = 0 := by
  simp only [HarmonicOscillator.potentialFunction_eq, Function.comp_apply]
  have h0 : (Space.val (0 : Space d)) = (0 : Fin d → ℝ) := rfl
  rw [h0, QuadraticMap.map_zero]

/-- **A level spacing** — the eigenvalue difference across one quantum-number step at
mode `i`, through the scale-gated `Quantity.sub`. The difference *cancels* the silent
potential reference: this quantity means the same thing under any declared `V(0)`. -/
def modeSpacingQ (Q : PhysHO d) (n : Fin d → ℕ) (i : Fin d) : Quantity energyK ℝ :=
  Quantity.sub energyDiff
    (eigenEnergyQ Q (Function.update n i (n i + 1))) (eigenEnergyQ Q n)

/-- The spacing is `ℏωᵢ` — independent of `n`: the equally-spaced ladder, as a kinded
statement about reference-free differences. -/
theorem modeSpacingQ_magnitude (Q : PhysHO d) (n : Fin d → ℕ) (i : Fin d) :
    (modeSpacingQ Q n i).magnitude = (Constants.ℏ : ℝ) * Q.ω i := by
  show (eigenEnergyQ Q (Function.update n i (n i + 1))).magnitude
      - (eigenEnergyQ Q n).magnitude = _
  rw [eigenEnergyQ_magnitude, eigenEnergyQ_magnitude,
    HarmonicOscillator.eigenEnergy_eq, HarmonicOscillator.eigenEnergy_eq,
    ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · rw [Function.update_self]; push_cast; ring
  · intro j _ hj; rw [Function.update_of_ne hj]; ring
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **The zero-point energy** — the one eigenvalue with no lower neighbor to difference
against: `∑ᵢ ℏωᵢ/2`, and *this* number does read against the silent `V(0) = 0`. Under
a shifted potential reference every level moves with it; the spacings above do not. -/
def zeroPointEnergyQ (Q : PhysHO d) : Quantity energyK ℝ := eigenEnergyQ Q 0

theorem zeroPointEnergyQ_magnitude (Q : PhysHO d) :
    (zeroPointEnergyQ Q).magnitude = ∑ i, (Constants.ℏ : ℝ) * Q.ω i / 2 := by
  rw [zeroPointEnergyQ, eigenEnergyQ_magnitude, HarmonicOscillator.eigenEnergy_eq]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.zero_apply]; push_cast; ring

/-! ## M-T3 — the TISE, statable now -/

/-- **F1d's crossing, on the right-hand side of the subject's defining equation**: an
energy-kinded scalar acts on a state through Mathlib's `SMul`, which no kind table
sees — attested once, so every kinded TISE statement names the crossing by using it. -/
@[kindCrossing]
def energySMul (Q : PhysHO d) (E : Quantity energyK ℝ) (ψ : Q.HS) : Q.HS :=
  (E.magnitude : ℂ) • ψ

/-- **The kinded time-independent Schrödinger equation** — `Ĥψₙ = Eₙψₙ` with both
sides carrying their kinds: `hamiltonianOpQ` (F1's join sum) applied to the
eigenstate equals the licensed-fold eigenvalue acting through the attested crossing.
The *statement* needs only this vocabulary; the *proof* is the upstream analysis TODO
("satisfy the TISE"), which this Prop is waiting for. -/
def SatisfiesTISE (Q : PhysHO d) (n : Fin d → ℕ) : Prop :=
  ∃ hmem : (Q.eigenstate n : Q.HS) ∈ (hamiltonianOpQ Q).magnitude.domain,
    (hamiltonianOpQ Q).magnitude ⟨_, hmem⟩ = energySMul Q (eigenEnergyQ Q n) (Q.eigenstate n)

end

end ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded
