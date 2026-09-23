/-
# Stage 1 — the metrology annex of `Physlib/QuantumMechanics/HarmonicOscillator`

The second rung of [the adoption ladder](../../PLAN.md#stage-1-the-metrology-annex), for
the pilot directory: each Stage-0 kind paired with its PhysLib `Dimension` as a
`DimensionedKind` — the lookups by *referencing the catalogue's own entries* (the
characteristic length by the catalogue's own species constructor, the quantum number by
Part 10's entry), the mints alone as constructed records — the directory's kind algebra
authored as laws, and
`#kind_dimensional_coverage` pinned over it with `#guard_msgs` — at **zero cost to
existing code**: nothing in PhysLib changes, or even imports this.

**And the lookup is definitional.** Stage 0's kinds *are* the catalogue entries'
own projections; this module records the identification kind by kind (`rfl` — there
is no second spelling to drift) and checks each pairing's dimension against the
catalogue's.

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

module

public import ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinds
public import PropertyKindCalculus.Dimension
public import PropertyKindCalculus.DimensionalCoverage
public import PropertyKindCalculus.Iso80000.Part3
public import PropertyKindCalculus.Iso80000.Part4
public import PropertyKindCalculus.Iso80000.Part10

@[expose] public section

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator.Metrology

open PropertyKindCalculus ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinds

/-! ## The pairings -/

/-- Mass is `M`. -/
def massDK : DimensionedKind := Iso80000.Part4.mass
/-- Action is `M·L²·T⁻¹` — ℏ's dimension, shared with angular momentum. -/
def actionDK : DimensionedKind := Iso80000.Part4.action
/-- Angular momentum is the *same* `M·L²·T⁻¹` — the collision the registry decides. -/
def angularMomentumDK : DimensionedKind := Iso80000.Part4.angularMomentum
/-- Angular frequency is `T⁻¹`. -/
def angularFrequencyDK : DimensionedKind := Iso80000.Part3.angularFrequency
/-- Kinetic energy is `M·L²·T⁻²`. -/
def kineticEnergyDK : DimensionedKind := Iso80000.Part4.kineticEnergy
/-- Potential energy is `M·L²·T⁻²` — the same dimension, a distinct kind. -/
def potentialEnergyDK : DimensionedKind := Iso80000.Part4.potentialEnergy
/-- Mechanical energy is `M·L²·T⁻²` — the third kind at the one dimension. -/
def mechanicalEnergyDK : DimensionedKind := Iso80000.Part4.mechanicalEnergy
/-- Momentum is `M·L·T⁻¹`. -/
def momentumDK : DimensionedKind := Iso80000.Part4.momentum
/-- Length is `L`. -/
def lengthDK : DimensionedKind := Iso80000.Part3.length
/-- The characteristic length is `L` (individuated by principle, not dimension) —
the catalogue's own `lengthSpecies` constructor, at this directory's species. -/
def characteristicLengthDK : DimensionedKind :=
  Iso80000.Part3.lengthSpecies "characteristic length" { id := "ground-state-width" }
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
/-- A quantum number is dimension one — the catalogue's own 10-13. -/
def quantumNumberDK : DimensionedKind := Iso80000.Part10.quantumNumber
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

/-! ## The lookup, definitional

Stage 0's vocabulary *is* the catalogue's — each lookup kind is the catalogue entry's
own projection (Parts 3, 4 and 10), and the characteristic length is Part 3's own
`lengthSpecies` constructor at this directory's species — so every identification is
`rfl` and drift is impossible by construction. -/

example : mass             = Iso80000.Part4.mass.kind             := rfl
example : action           = Iso80000.Part4.action.kind           := rfl
example : angularMomentum  = Iso80000.Part4.angularMomentum.kind  := rfl
example : angularFrequency = Iso80000.Part3.angularFrequency.kind := rfl
example : kineticEnergy    = Iso80000.Part4.kineticEnergy.kind    := rfl
example : potentialEnergy  = Iso80000.Part4.potentialEnergy.kind  := rfl
example : mechanicalEnergy = Iso80000.Part4.mechanicalEnergy.kind := rfl
example : momentum         = Iso80000.Part4.momentum.kind         := rfl
example : length           = Iso80000.Part3.length.kind           := rfl
example : characteristicLength
    = (Iso80000.Part3.lengthSpecies "characteristic length"
        { id := "ground-state-width" }).kind := rfl
example : quantumNumber = (Iso80000.Part10.quantumNumber).kind := rfl

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

