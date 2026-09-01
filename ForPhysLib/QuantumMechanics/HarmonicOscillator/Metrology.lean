/-
# Stage 1 — the metrology annex of `Physlib/QuantumMechanics/HarmonicOscillator`

The second rung of [the adoption ladder](../../PLAN.md#stage-1-the-metrology-annex), for
the pilot directory: each Stage-0 kind paired with its PhysLib `Dimension` as a
`DimensionedKind`, the directory's kind algebra authored as laws, and
`#kind_dimensional_coverage` pinned over it with `#guard_msgs` — at **zero cost to
existing code**: nothing in PhysLib changes, or even imports this.

**And the lookup is now a theorem.** Stage 0 copied its ids, scales and examination
principles from PKC's ISO 80000 catalogue; this module imports that catalogue and proves
the agreement by `decide` — kind by kind, and dimension by dimension. A Stage-0 edit
that drifts from the standard stops compiling here.

**The laws are the directory's own equations.** Ten edges, each one a formula the
directory's physics writes: `ℏ/m` and then `/ω` (the ξ² radicand chain of the 1D
file), `ξ·ξ` landing back in the radicand (PhysLib's own `ξ_sq`), `ℏ·ω` an energy (the
eigenvalues), `p̂·p̂` (the squared momentum operator), `p̂²/m` a kinetic energy —
the law behind `kineticOperator = (2m)⁻¹ • p̂²`, authored here even though the source's
spelling rides Mathlib's `SMul` where no table sees it (the F1d crossing; the audit
stage measures that gap, this stage states the law it fails to consume) — `x/ξ` (the
Hermite argument), energy · energy (the variance's kind), `x·x` (the potential's
quadratic form, and a position variance's radicand), and `x·p` landing at action (the
uncertainty product, comparable with `ℏ/2` because both are actions).
-/

import ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinds
import PropertyKindCalculus.Dimension
import PropertyKindCalculus.DimensionalCoverage
import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part4
import PropertyKindCalculus.Iso80000.Part10

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator.Metrology

open PropertyKindCalculus ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinds

/-! ## The pairings -/

/-- Mass is `M`. -/
def massDK : DimensionedKind := { kind := mass, dim := Dim.mass }
/-- Action is `M·L²·T⁻¹` — ℏ's dimension, shared with angular momentum. -/
def actionDK : DimensionedKind :=
  { kind := action, dim := Iso80000.Part4.MDim.angularMomentum }
/-- Angular frequency is `T⁻¹`. -/
def angularFrequencyDK : DimensionedKind :=
  { kind := angularFrequency, dim := Dim.time⁻¹ }
/-- Kinetic energy is `M·L²·T⁻²`. -/
def kineticEnergyDK : DimensionedKind :=
  { kind := kineticEnergy, dim := Iso80000.Part4.MDim.energy }
/-- Potential energy is `M·L²·T⁻²` — the same dimension, a distinct kind. -/
def potentialEnergyDK : DimensionedKind :=
  { kind := potentialEnergy, dim := Iso80000.Part4.MDim.energy }
/-- Mechanical energy is `M·L²·T⁻²` — the third kind at the one dimension. -/
def mechanicalEnergyDK : DimensionedKind :=
  { kind := mechanicalEnergy, dim := Iso80000.Part4.MDim.energy }
/-- Momentum is `M·L·T⁻¹`. -/
def momentumDK : DimensionedKind :=
  { kind := momentum, dim := Iso80000.Part4.MDim.momentum }
/-- Length is `L`. -/
def lengthDK : DimensionedKind := { kind := length, dim := Dim.length }
/-- The characteristic length is `L` (individuated by principle, not dimension). -/
def characteristicLengthDK : DimensionedKind :=
  { kind := characteristicLength, dim := Dim.length }
/-- Momentum squared is `M²·L²·T⁻²` — *not* an energy's dimension: the `M` mismatch
is exactly what `(2m)⁻¹` repairs. -/
def momentumSquaredDK : DimensionedKind :=
  { kind := momentumSquared,
    dim := Iso80000.Part4.MDim.momentum * Iso80000.Part4.MDim.momentum }
/-- Action per mass is `L²·T⁻¹`. -/
def specificActionDK : DimensionedKind :=
  { kind := specificAction, dim := Iso80000.Part4.MDim.angularMomentum / Dim.mass }
/-- The ξ² radicand is `L²`. -/
def xiSqRadicandDK : DimensionedKind := { kind := xiSqRadicand, dim := Dim.area }
/-- A quantum number is dimension one. -/
def quantumNumberDK : DimensionedKind := { kind := quantumNumber, dim := Dim.one }
/-- The dimensionless coordinate `x/ξ` is dimension one. -/
def dimensionlessCoordinateDK : DimensionedKind :=
  { kind := dimensionlessCoordinate, dim := Dim.one }
/-- Probability is dimension one — a third kind at that dimension (with the quantum
numbers and the dimensionless coordinate): the dimension-1 conflation, again. -/
def probabilityDK : DimensionedKind := { kind := probability, dim := Dim.one }
/-- Energy squared — the variance's dimension. -/
def energySquaredDK : DimensionedKind :=
  { kind := energySquared, dim := Iso80000.Part4.MDim.energy * Iso80000.Part4.MDim.energy }

/- The Born density and the `d`-dimensional volume element have **no entry here, on
purpose**: their dimensions (`L⁻ᵈ`, `Lᵈ`) are parameters of the model, not constants of
the vocabulary, so their dimensional coherence is a parametric *theorem* in `Kinded.lean`
rather than a registry pairing the coverage walk could pin once. -/

/-! ## The lookup, proved

Stage 0's vocabulary agrees with `Iso80000` Parts 3 and 4 — same kinds (ids, scales,
examination principles) and same dimensions. Decided, so drift is a build failure. The
characteristic length is checked against the catalogue's own `lengthSpecies` pattern:
the species this directory mints is well-formed by the same constructor the standard's
listed species use. -/

example : mass             = Iso80000.Part4.mass.kind             := by decide
example : action           = Iso80000.Part4.action.kind           := by decide
example : angularFrequency = Iso80000.Part3.angularFrequency.kind := by decide
example : kineticEnergy    = Iso80000.Part4.kineticEnergy.kind    := by decide
example : potentialEnergy  = Iso80000.Part4.potentialEnergy.kind  := by decide
example : mechanicalEnergy = Iso80000.Part4.mechanicalEnergy.kind := by decide
example : momentum         = Iso80000.Part4.momentum.kind         := by decide
example : length           = Iso80000.Part3.length.kind           := by decide
example : characteristicLength
    = (Iso80000.Part3.lengthSpecies "characteristic length"
        { id := "ground-state-width" }).kind := by decide
example : quantumNumber = (Iso80000.Part10.quantumNumber).kind := by decide

example : massDK.dim             = Iso80000.Part4.mass.dim             := rfl
example : actionDK.dim           = Iso80000.Part4.action.dim           := rfl
example : angularFrequencyDK.dim = Iso80000.Part3.angularFrequency.dim := rfl
example : kineticEnergyDK.dim    = Iso80000.Part4.kineticEnergy.dim    := rfl
example : potentialEnergyDK.dim  = Iso80000.Part4.potentialEnergy.dim  := rfl
example : mechanicalEnergyDK.dim = Iso80000.Part4.mechanicalEnergy.dim := rfl
example : momentumDK.dim         = Iso80000.Part4.momentum.dim         := rfl
example : lengthDK.dim           = Iso80000.Part3.length.dim           := rfl
example : characteristicLengthDK.dim
    = (Iso80000.Part3.lengthSpecies "characteristic length"
        { id := "ground-state-width" }).dim := rfl
example : quantumNumberDK.dim = (Iso80000.Part10.quantumNumber).dim := rfl

/-! ## The directory's kind algebra, and its dimensional audit

Ten authored edges — the equations the directory's physics actually writes.
`#kind_dimensional_coverage` then walks every authored edge and checks it in PhysLib's
dimension group. -/

/-- `ℏ / m` — the first link of the ξ² radicand chain (the 1D file's `ξ`). -/
theorem action_div_mass : QuotientKind action mass specificAction :=
  QuotientKind.ofRatio _ _ _

/-- `(ℏ/m) / ω` — the radicand lands at length squared. -/
theorem specificAction_div_angularFrequency :
    QuotientKind specificAction angularFrequency xiSqRadicand :=
  QuotientKind.ofRatio _ _ _

/-- `ξ · ξ` lands back in the radicand — the root's re-entry as a law: PhysLib's own
`ξ_sq` (`ξ² = ℏ/(m·ω)`) is this edge read at magnitudes. The root itself is not a kind
operation; Stage 2 attests it once. -/
theorem characteristicLength_mul_self :
    ProductKind characteristicLength characteristicLength xiSqRadicand :=
  ProductKind.ofRatio _ _ _

/-- `ℏ · ω` is an energy — the eigenvalue factorization `ℏ ωᵢ (nᵢ + ½)`. -/
theorem action_mul_angularFrequency :
    ProductKind action angularFrequency mechanicalEnergy :=
  ProductKind.ofRatio _ _ _

/-- `p̂ · p̂` — the squared momentum operator's kind law. -/
theorem momentum_mul_self : ProductKind momentum momentum momentumSquared :=
  ProductKind.ofRatio _ _ _

/-- `p̂² / m` is a kinetic energy — the law behind `kineticOperator = (2m)⁻¹ • p̂²`.
The source's spelling rides Mathlib's `SMul` (the F1d crossing), so this law exists
here for the coverage walk and the audit to measure against, not because the source
can consume it. -/
theorem momentumSquared_div_mass :
    QuotientKind momentumSquared mass kineticEnergy :=
  QuotientKind.ofRatio _ _ _

/-- `x / ξ` lands at the dimensionless coordinate — the nondimensionalization edge the
eigenfunctions write (`eigenfunction_apply`'s Hermite argument is `x i / Q.ξ i`). -/
theorem length_div_characteristicLength :
    QuotientKind length characteristicLength dimensionlessCoordinate :=
  QuotientKind.ofRatio _ _ _

/-- Energy · energy is the variance's kind — the edge `Measurand.lean`'s variance
lands through; its root back to energy is one attested crossing, not an edge. -/
theorem mechanicalEnergy_mul_self :
    ProductKind mechanicalEnergy mechanicalEnergy energySquared :=
  ProductKind.ofRatio _ _ _

/-- Length · length lands at length squared — the `x²` of the potential's quadratic
form, and the radicand of a position uncertainty: a position measurand's variance
lives at this kind, its σ one attested root back to length (radicand-first again). -/
theorem length_mul_length : ProductKind length length xiSqRadicand :=
  ProductKind.ofRatio _ _ _

/-- Length · momentum lands at action — the uncertainty product's kind law: `σ_x · σ_p`
is comparable with `ℏ/2` because both sides are actions, and that comparability is this
edge plus the same-kind order, nothing else. -/
theorem length_mul_momentum : ProductKind length momentum action :=
  ProductKind.ofRatio _ _ _

/--
info: dimensional coverage:
[coherent] action / mass → specificAction
[coherent] action · angularFrequency → mechanicalEnergy
[coherent] characteristicLength · characteristicLength → xiSqRadicand
[coherent] length / characteristicLength → dimensionlessCoordinate
[coherent] length · length → xiSqRadicand
[coherent] length · momentum → action
[coherent] mechanicalEnergy · mechanicalEnergy → energySquared
[coherent] momentum · momentum → momentumSquared
[coherent] momentumSquared / mass → kineticEnergy
[coherent] specificAction / angularFrequency → xiSqRadicand
10 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage ForPhysLib.QuantumMechanics.HarmonicOscillator.Metrology

end ForPhysLib.QuantumMechanics.HarmonicOscillator.Metrology
