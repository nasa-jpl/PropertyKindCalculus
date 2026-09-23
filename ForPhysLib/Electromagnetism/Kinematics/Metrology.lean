/-
# Stage 1 — the metrology annex of `Physlib/Electromagnetism/Kinematics`

The second rung of [the adoption ladder](../../PLAN.md#stage-1-the-metrology-annex), for
the campaign's second directory: each Stage-0 kind paired with its PhysLib `Dimension`
as a `DimensionedKind` — the lookups by *referencing the catalogue's own entries*, the
mints alone as constructed records — the chain's kind algebra authored as laws, and
`#kind_dimensional_coverage` pinned over it with `#guard_msgs` — at **zero cost to
existing code**: nothing in PhysLib changes, or even imports this.

**And the lookup is definitional.** Stage 0's kinds *are* the catalogue entries'
own projections; this module records the identification kind by kind (`rfl` — there
is no second spelling to drift) and checks each pairing's dimension against the
catalogue's.

**The registry now shows the collisions.** Three pairings at the tesla (`B`, the
potential-gradient entry, the field-strength entry) and two at the volt (the interval
potential and its ratio-scale difference) — the same-dimension families whose
separation is Stage 0's whole point, visible as repeated dimensions in one table.

**The laws are the chain's own equations.** Twenty-five edges, each one a formula the
directory's physics writes: the velocity edge in both directions (`c·A⁰` and `φ/c`),
the three derivative edges (`∇φ`, `∂ₜ𝐀`, `∇×𝐀`), the derivative tensor's per-length
entry, the tensor's electric reading (`E = −c·F⁰ⁱ`), the two boost mixings (`c·B` up to
the electric kind, `E/c` down to the magnetic), the gauge edge (`∂χ`), and the two
line-integral edges of the Poincaré-gauge constructor (`∫⟪E, dx⟫` and `∫ dx × B`) —
plus Maxwell's seven: the field-derivative sides (`∇⬝E`/`∇⨯E`, `∂ₜB`, `∇⨯B`, `∂ₜE`),
the sources (`ρ/ε₀`, `μ₀·J`), and the displacement current `ε₀·∂ₜE` landing at the
catalogue's own 6-8 — plus the variational six: the `π` and `π·F` products, `A·J`,
the Legendre product, and the two spellings of `δS/δA`.
-/

module

public import ForPhysLib.Electromagnetism.Kinematics.Kinds
public import PropertyKindCalculus.Dimension
public import PropertyKindCalculus.DimensionalCoverage
public import PropertyKindCalculus.Iso80000.Part3
public import PropertyKindCalculus.Iso80000.Part6
public import PropertyKindCalculus.Iso80000.Part7

@[expose] public section

namespace ForPhysLib.Electromagnetism.Kinematics.Metrology

open PropertyKindCalculus ForPhysLib.Electromagnetism.Kinematics.Kinds

/-! ## The pairings -/

/-- The magnetic vector potential is `M·L·T⁻¹·C⁻¹` (Wb/m). -/
def magneticVectorPotentialDK : DimensionedKind := Iso80000.Part6.magneticVectorPotential
/-- The electric potential is `M·L²·T⁻²·C⁻¹` (the volt) — at interval scale. -/
def electricPotentialDK : DimensionedKind := Iso80000.Part6.electricPotential
/-- The potential difference is the *same* volt — a distinct kind at a distinct
scale; the first of the registry's repeated dimensions. -/
def electricPotentialDifferenceDK : DimensionedKind :=
  Iso80000.Part6.electricPotentialDifference
/-- The electric field strength is `M·L·T⁻²·C⁻¹` (V/m). -/
def electricFieldStrengthDK : DimensionedKind := Iso80000.Part6.electricFieldStrength
/-- The magnetic flux density is `M·T⁻¹·C⁻¹` (the tesla). -/
def magneticFluxDensityDK : DimensionedKind := Iso80000.Part6.magneticFluxDensity
/-- The potential-gradient entry is the *same* tesla — gauge-dependent, a distinct
kind. -/
def potentialGradientDK : DimensionedKind :=
  { kind := potentialGradient, dim := Iso80000.Part6.EDim.magneticFluxDensity }
/-- The field-strength entry is the *same* tesla again — three kinds, one dimension:
the collision the vocabulary exists to prevent, now visible in the registry. -/
def fieldStrengthDK : DimensionedKind :=
  { kind := fieldStrength, dim := Iso80000.Part6.EDim.magneticFluxDensity }
/-- The magnetic flux is `M·L²·T⁻¹·C⁻¹` (the weber) — the gauge function's
dimension. -/
def magneticFluxDK : DimensionedKind := Iso80000.Part6.magneticFlux
/-- The speed of light is `L·T⁻¹` — the catalogue's 6-35.2, the *vacuum* constant.
Not Part 7's `speedOfLight`: that is item 7-1.1, "speed of light in a medium" — a
medium-dependent quantity and a different kind (the two ids differ, decidably). The
chain's `c` is `FreeSpace.c = 1/√(ε₀μ₀)` — vacuum by definition. -/
def speedOfLightDK : DimensionedKind := Iso80000.Part6.speedOfLight
/-- Speed — the genus, same dimension. -/
def speedDK : DimensionedKind := Iso80000.Part3.speed
/-- Length is `L` — the spacetime coordinate (`x⁰ = c·t`), and every `∇`'s
denominator. -/
def lengthDK : DimensionedKind := Iso80000.Part3.length
/-- Duration is `T` — the sliced readings' `∂ₜ` denominator. -/
def durationDK : DimensionedKind := Iso80000.Part3.duration
/-- The charge density is `C·L⁻³`. -/
def electricChargeDensityDK : DimensionedKind := Iso80000.Part6.electricChargeDensity
/-- The current density is `C·T⁻¹·L⁻²`. -/
def electricCurrentDensityDK : DimensionedKind := Iso80000.Part6.electricCurrentDensity
/-- The electric constant is `C²·M⁻¹·L⁻³·T²` (the farad per metre). -/
def electricConstantDK : DimensionedKind := Iso80000.Part6.electricConstant
/-- The magnetic constant is `M·L·C⁻²` (the henry per metre). -/
def magneticConstantDK : DimensionedKind := Iso80000.Part6.magneticConstant
/-- The electric-field derivative is `E` per length. -/
def electricFieldDerivativeDK : DimensionedKind :=
  { kind := electricFieldDerivative,
    dim := Iso80000.Part6.EDim.electricFieldStrength / Dim.length }
/-- The magnetic-field derivative is the tesla per length. -/
def magneticFieldDerivativeDK : DimensionedKind :=
  { kind := magneticFieldDerivative,
    dim := Iso80000.Part6.EDim.magneticFluxDensity / Dim.length }
/-- The electric-field rate is `E` per duration. -/
def electricFieldRateDK : DimensionedKind :=
  { kind := electricFieldRate,
    dim := Iso80000.Part6.EDim.electricFieldStrength / Dim.time }

/-- The electromagnetic energy density is `M·L⁻¹·T⁻²` (J/m³). -/
def electromagneticEnergyDensityDK : DimensionedKind :=
  Iso80000.Part6.electromagneticEnergyDensity
/-- The linear current density is `C·T⁻¹·L⁻¹` (A/m). -/
def linearElectricCurrentDensityDK : DimensionedKind :=
  Iso80000.Part6.linearCurrentDensity
/-- The Lagrangian density is the *same* J/m³ — gauge-dependent, a distinct kind:
the registry's density-level collision. -/
def lagrangianDensityDK : DimensionedKind :=
  { kind := lagrangianDensity, dim := Iso80000.Part6.EDim.energyDensity }
/-- The variational gradient is the *same* A/m² as 6-8 — the Euler–Lagrange reading,
not a current density. -/
def variationalGradientDK : DimensionedKind :=
  { kind := variationalGradient, dim := Iso80000.Part6.EDim.currentDensity }
/-- The canonical momentum is the *same* A/m as 6-9 — the Legendre-conjugate
reading, not a current through a line. -/
def canonicalMomentumDensityDK : DimensionedKind :=
  { kind := canonicalMomentumDensity, dim := Iso80000.Part6.EDim.linearCurrentDensity }

/-! ## The lookup, definitional

Stage 0's vocabulary *is* `Iso80000` Parts 3 and 6's — each lookup kind is the
catalogue entry's own projection, so the identification is `rfl` and drift is
impossible by construction. The mints have no catalogue row — that they *cannot* be
looked up is their finding — but their dimensions are checked against the
catalogue's below. -/

/-- The registry's speed of light is the catalogue's *vacuum* item, and Part 7's
`speedOfLight` (7-1.1, "speed of light in a medium") is decidably a different kind —
the constant and the medium-dependent speed separate at one dimension. -/
example : Iso80000.Part6.speedOfLight.kind ≠ Iso80000.Part7.speedOfLight.kind := by
  decide


example : magneticVectorPotential = Iso80000.Part6.magneticVectorPotential.kind := rfl
example : electricPotential = Iso80000.Part6.electricPotential.kind := rfl
example : electricPotentialDifference
    = Iso80000.Part6.electricPotentialDifference.kind := rfl
example : electricFieldStrength = Iso80000.Part6.electricFieldStrength.kind := rfl
example : magneticFluxDensity = Iso80000.Part6.magneticFluxDensity.kind := rfl
example : magneticFlux = Iso80000.Part6.magneticFlux.kind := rfl
example : speedOfLight = Iso80000.Part6.speedOfLight.kind := rfl
example : speed = Iso80000.Part3.speed.kind := rfl
example : length = Iso80000.Part3.length.kind := rfl
example : duration = Iso80000.Part3.duration.kind := rfl
example : electricChargeDensity  = Iso80000.Part6.electricChargeDensity.kind  := rfl
example : electricCurrentDensity = Iso80000.Part6.electricCurrentDensity.kind := rfl
example : electricConstant       = Iso80000.Part6.electricConstant.kind       := rfl
example : magneticConstant       = Iso80000.Part6.magneticConstant.kind       := rfl
example : electromagneticEnergyDensity
    = Iso80000.Part6.electromagneticEnergyDensity.kind := rfl
example : linearElectricCurrentDensity
    = Iso80000.Part6.linearCurrentDensity.kind := rfl

example : magneticVectorPotentialDK.dim
    = Iso80000.Part6.magneticVectorPotential.dim := rfl
example : electricPotentialDK.dim = Iso80000.Part6.electricPotential.dim := rfl
example : electricPotentialDifferenceDK.dim
    = Iso80000.Part6.electricPotentialDifference.dim := rfl
example : electricFieldStrengthDK.dim = Iso80000.Part6.electricFieldStrength.dim := rfl
example : magneticFluxDensityDK.dim = Iso80000.Part6.magneticFluxDensity.dim := rfl
example : magneticFluxDK.dim = Iso80000.Part6.magneticFlux.dim := rfl
example : speedOfLightDK.dim = Iso80000.Part6.speedOfLight.dim := rfl
example : speedDK.dim = Iso80000.Part3.speed.dim := rfl
example : lengthDK.dim = Iso80000.Part3.length.dim := rfl
example : durationDK.dim = Iso80000.Part3.duration.dim := rfl
/- The mints' dimension is the catalogue's tesla — the same-dimension collision is a
checked fact, not a slogan. -/
example : potentialGradientDK.dim = Iso80000.Part6.magneticFluxDensity.dim := rfl
example : fieldStrengthDK.dim = Iso80000.Part6.magneticFluxDensity.dim := rfl
example : electricChargeDensityDK.dim  = Iso80000.Part6.electricChargeDensity.dim  := rfl
example : electricCurrentDensityDK.dim = Iso80000.Part6.electricCurrentDensity.dim := rfl
example : electricConstantDK.dim       = Iso80000.Part6.electricConstant.dim       := rfl
example : magneticConstantDK.dim       = Iso80000.Part6.magneticConstant.dim       := rfl
example : electromagneticEnergyDensityDK.dim
    = Iso80000.Part6.electromagneticEnergyDensity.dim := rfl
example : linearElectricCurrentDensityDK.dim
    = Iso80000.Part6.linearCurrentDensity.dim := rfl
example : lagrangianDensityDK.dim = Iso80000.Part6.electromagneticEnergyDensity.dim := rfl
example : variationalGradientDK.dim = Iso80000.Part6.electricCurrentDensity.dim := rfl
example : canonicalMomentumDensityDK.dim = Iso80000.Part6.linearCurrentDensity.dim := rfl

/-! ## The chain's kind algebra, and its dimensional audit

Twenty-five authored edges — the equations the chain's physics actually writes,
Maxwell's seven (the four laws' sides and the displacement chain) and the variational
subtree's six (the Lagrangian's two products, the Legendre pair, the two spellings of
`δS/δA`) included.
`#kind_dimensional_coverage` then walks every authored edge and checks it in PhysLib's
dimension group. -/

/-- `c · A⁰` — the velocity edge at the four-potential: `scalarPotential`'s defining
multiplication. The target is the **ratio-scale** 6-11.2, because 6-11.1's interval
scale refuses `ofRatio` (Feasibility's pinned refusal); the crossing onto the interval
potential itself stays attested, never tabled. -/
theorem speedOfLight_mul_magneticVectorPotential :
    ProductKind speedOfLight magneticVectorPotential electricPotentialDifference :=
  ProductKind.ofRatio _ _ _

/-- `φ / c` — the same edge in the direction `ofPotentials` writes it: the time slot
stores `φ/c`, and that division is what makes the four-vector one kind. -/
theorem electricPotentialDifference_div_speedOfLight :
    QuotientKind electricPotentialDifference speedOfLight magneticVectorPotential :=
  QuotientKind.ofRatio _ _ _

/-- `∇φ` — the gradient edge of `electricField = −∇φ − ∂ₜ𝐀`. Stated at the potential's
*differences* (6-11.2): a derivative of an interval-scale quantity is a difference
quotient, so the gradient eats the gauge reference and its edge never touches
6-11.1. -/
theorem electricPotentialDifference_div_length :
    QuotientKind electricPotentialDifference length electricFieldStrength :=
  QuotientKind.ofRatio _ _ _

/-- `∂ₜ𝐀` — the time-derivative edge of the same equation: a vector potential per
duration is an electric field. -/
theorem magneticVectorPotential_div_duration :
    QuotientKind magneticVectorPotential duration electricFieldStrength :=
  QuotientKind.ofRatio _ _ _

/-- `∇×𝐀` — the curl edge: `magneticField = ∇ ⨯ vectorPotential`, a vector potential
per space-length landing at the flux density. -/
theorem magneticVectorPotential_div_length :
    QuotientKind magneticVectorPotential length magneticFluxDensity :=
  QuotientKind.ofRatio _ _ _

/-- `∂_μ A^ν` — the derivative tensor's entry: a vector potential per *spacetime*
coordinate (a length — `x⁰ = c·t`), landing at the gauge-dependent chart kind. Same
dimensional arithmetic as the curl edge, a different target kind: the coordinate
derivative keeps the gauge dependence the curl's antisymmetry cancels. -/
theorem magneticVectorPotential_div_length_gradient :
    QuotientKind magneticVectorPotential length potentialGradient :=
  QuotientKind.ofRatio _ _ _

/-- `E_i = −c·F⁰ⁱ` — the tensor's electric reading: the velocity edge one level up
(`electricField_eq_toFieldStrength_eval`). -/
theorem speedOfLight_mul_fieldStrength :
    ProductKind speedOfLight fieldStrength electricFieldStrength :=
  ProductKind.ofRatio _ _ _

/-- `c·β·B` — the boost's upward mixing (`electricField_apply_x_boost_succ`): a
velocity-scaled flux density lands at the electric kind, which is the only way a
magnetic term enters the boosted `E`. -/
theorem speedOfLight_mul_magneticFluxDensity :
    ProductKind speedOfLight magneticFluxDensity electricFieldStrength :=
  ProductKind.ofRatio _ _ _

/-- `(β/c)·E` — the boost's downward mixing, and the tensor's own storage of the
electric block (`toFieldStrength_eval_inl_inr_eq_electricField` writes `−(1/c)·E`). -/
theorem electricFieldStrength_div_speedOfLight :
    QuotientKind electricFieldStrength speedOfLight magneticFluxDensity :=
  QuotientKind.ofRatio _ _ _

/-- `∂^μχ` — the gauge edge: a flux field per spacetime coordinate is a vector
potential (`ofGradient`), which is why the gauge function is 6-22.1 and the shift
stays inside the potential's kind. -/
theorem magneticFlux_div_length :
    QuotientKind magneticFlux length magneticVectorPotential :=
  QuotientKind.ofRatio _ _ _

/-- `∫⟪E, dx⟫` — the Poincaré-gauge scalar potential (`ofElectromagneticField`): an
electric field times a length is a potential difference. -/
theorem electricFieldStrength_mul_length :
    ProductKind electricFieldStrength length electricPotentialDifference :=
  ProductKind.ofRatio _ _ _

/-- `∫ dx ⨯ B` — the Poincaré-gauge vector potential: a length times a flux density
is a vector potential. -/
theorem length_mul_magneticFluxDensity :
    ProductKind length magneticFluxDensity magneticVectorPotential :=
  ProductKind.ofRatio _ _ _

/-- `∇⬝E` / `∇⨯E` — the electric field's per-length edge: Maxwell's homogeneous and
Gauss-electric left-hand sides. The `∇` is Mathlib's `fderiv`; law-only, like the
chain's other derivative edges. -/
theorem electricFieldStrength_div_length :
    QuotientKind electricFieldStrength length electricFieldDerivative :=
  QuotientKind.ofRatio _ _ _

/-- `ρ/ε₀` — Gauss's source edge: a charge density per electric constant lands at the
electric-field derivative. -/
theorem electricChargeDensity_div_electricConstant :
    QuotientKind electricChargeDensity electricConstant electricFieldDerivative :=
  QuotientKind.ofRatio _ _ _

/-- `∂ₜB` — Faraday's right-hand side: a flux density per duration is an
electric-field derivative (`T/s = V/m²`). -/
theorem magneticFluxDensity_div_duration :
    QuotientKind magneticFluxDensity duration electricFieldDerivative :=
  QuotientKind.ofRatio _ _ _

/-- `∇⨯B` — the magnetic field's per-length edge: Ampère's left-hand side. -/
theorem magneticFluxDensity_div_length :
    QuotientKind magneticFluxDensity length magneticFieldDerivative :=
  QuotientKind.ofRatio _ _ _

/-- `μ₀·J` — Ampère's source edge: the magnetic constant scales a current density to
the magnetic-field derivative. -/
theorem magneticConstant_mul_electricCurrentDensity :
    ProductKind magneticConstant electricCurrentDensity magneticFieldDerivative :=
  ProductKind.ofRatio _ _ _

/-- `∂ₜE` — the displacement chain's first edge: an electric field per duration. -/
theorem electricFieldStrength_div_duration :
    QuotientKind electricFieldStrength duration electricFieldRate :=
  QuotientKind.ofRatio _ _ _

/-- `ε₀·∂ₜE` — the displacement current: the electric constant scales the field rate
back to the catalogue's own 6-8. Ampère's right-hand side is then a *same-kind* sum
after `μ₀·(J + ε₀∂ₜE)` — no join, continuing the chain's finding. -/
theorem electricConstant_mul_electricFieldRate :
    ProductKind electricConstant electricFieldRate electricCurrentDensity :=
  ProductKind.ofRatio _ _ _

/-- `π = −F⁰ⁱ/μ₀` — the canonical momentum's defining edge
(`canonicalMomentum_eq_electricField` writes it `−E/(μ₀c)`, which is the same entry
through the velocity edge): a field-strength entry per magnetic constant. -/
theorem fieldStrength_div_magneticConstant :
    QuotientKind fieldStrength magneticConstant canonicalMomentumDensity :=
  QuotientKind.ofRatio _ _ _

/-- `−¼·(F/μ₀)·F` — the kinetic term (`Dynamics/KineticTerm.lean`): the Lagrangian
density's first product, factored through the canonical-momentum kind the previous
edge lands on. -/
theorem canonicalMomentumDensity_mul_fieldStrength :
    ProductKind canonicalMomentumDensity fieldStrength lagrangianDensity :=
  ProductKind.ofRatio _ _ _

/-- `A·J` — `freeCurrentPotential = ⟪A x, J x⟫ₘ`: the interaction term's product,
landing at the same Lagrangian density — which is what makes
`lagrangian = kineticTerm − freeCurrentPotential` a *same-kind* subtraction. Still no
join. -/
theorem magneticVectorPotential_mul_electricCurrentDensity :
    ProductKind magneticVectorPotential electricCurrentDensity lagrangianDensity :=
  ProductKind.ofRatio _ _ _

/-- `π·∂₀A` — the Legendre product (`hamiltonian`'s first term): a canonical momentum
times a derivative-tensor entry is a Lagrangian density, so `H = π·∂₀A − L` is a
same-kind subtraction too; the Hamiltonian's re-reading at 6-33 is then one attested
crossing. -/
theorem canonicalMomentumDensity_mul_potentialGradient :
    ProductKind canonicalMomentumDensity potentialGradient lagrangianDensity :=
  ProductKind.ofRatio _ _ _

/-- `δS/δA` — the variational derivative's own arithmetic: a Lagrangian density per
vector potential. Law-only: the `δ` lives in `HasVarGradientAt`, which no table
sees. -/
theorem lagrangianDensity_div_magneticVectorPotential :
    QuotientKind lagrangianDensity magneticVectorPotential variationalGradient :=
  QuotientKind.ofRatio _ _ _

/-- `μ₀⁻¹·∑∂F` — the variational gradient as upstream computes it
(`gradLagrangian_eq_sum_toFieldStrength_eval`): a magnetic-field derivative per
magnetic constant, same target — Euler–Lagrange holds at one kind. -/
theorem magneticFieldDerivative_div_magneticConstant :
    QuotientKind magneticFieldDerivative magneticConstant variationalGradient :=
  QuotientKind.ofRatio _ _ _

/--
info: dimensional coverage:
[coherent] canonicalMomentumDensity · fieldStrength → lagrangianDensity
[coherent] canonicalMomentumDensity · potentialGradient → lagrangianDensity
[coherent] electricChargeDensity / electricConstant → electricFieldDerivative
[coherent] electricConstant · electricFieldRate → electricCurrentDensity
[coherent] electricFieldStrength / duration → electricFieldRate
[coherent] electricFieldStrength / length → electricFieldDerivative
[coherent] electricFieldStrength / speedOfLight → magneticFluxDensity
[coherent] electricFieldStrength · length → electricPotentialDifference
[coherent] electricPotentialDifference / length → electricFieldStrength
[coherent] electricPotentialDifference / speedOfLight → magneticVectorPotential
[coherent] fieldStrength / magneticConstant → canonicalMomentumDensity
[coherent] lagrangianDensity / magneticVectorPotential → variationalGradient
[coherent] length · magneticFluxDensity → magneticVectorPotential
[coherent] magneticConstant · electricCurrentDensity → magneticFieldDerivative
[coherent] magneticFieldDerivative / magneticConstant → variationalGradient
[coherent] magneticFlux / length → magneticVectorPotential
[coherent] magneticFluxDensity / duration → electricFieldDerivative
[coherent] magneticFluxDensity / length → magneticFieldDerivative
[coherent] magneticVectorPotential / duration → electricFieldStrength
[coherent] magneticVectorPotential / length → magneticFluxDensity
[coherent] magneticVectorPotential / length → potentialGradient
[coherent] magneticVectorPotential · electricCurrentDensity → lagrangianDensity
[coherent] speedOfLight · fieldStrength → electricFieldStrength
[coherent] speedOfLight · magneticFluxDensity → electricFieldStrength
[coherent] speedOfLight · magneticVectorPotential → electricPotentialDifference
25 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage ForPhysLib.Electromagnetism.Kinematics.Metrology

end ForPhysLib.Electromagnetism.Kinematics.Metrology

