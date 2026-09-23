/-
# Validation probes — dimension-backed bridges (R1, R5, R7, R13, R17-ℝ)

Inhabitation and axiom-profile probes for the requirements whose theorems live in the
PhysLib/Mathlib-backed `Dimension` layer — the seven "verifiable" theorems CI did **not** build
before the `Tests` library was added. Each theorem is applied to a concrete witness; the Rule-2
boundary is the negative (an unsanctioned product is a category error; matching dimensions are
necessary but not sufficient). The Mathlib-backed proofs legitimately use
`[propext, Classical.choice, Quot.sound]`; the gate's job is to confirm **no `sorryAx`** creeps in,
so `whitespace := lax` keeps the pinned axiom list robust to line-wrapping.
-/

module

public import PropertyKindCalculus.Dimension
public import PropertyKindCalculus.Interaction
public import PropertyKindCalculus.ScaleSpanning
public import PropertyKindCalculus.UnitConversion

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.DimensionBridges

open PropertyKindCalculus

/-! ## R1 — kinds discriminate within a dimension (dim is not injective) -/

-- Inhabitation: `dim_not_injective` is an existential, and it is genuinely witnessed — two
-- distinct kinds (vwc, gwc) that forget to the *same* dimension. Re-asserting the two conjuncts
-- that carry the content confirms the witness is real, not a vacuous `∃`.
theorem r1_distinct_kinds_one_dimension :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.toDimension = b.toDimension :=
  match dim_not_injective with
  | ⟨a, b, hne, hdim, _⟩ => ⟨a, b, hne, hdim⟩

-- `Classical.choice` enters from PhysLib, not from this proof: since the `Exponent` reform,
-- `Dimension.exponent` is defined through the basis's `exponentEquiv : Exponents ≃+ (B → Exponent)`,
-- and `#print axioms Dimension.exponent` reports `[propext, Classical.choice, Quot.sound]` on its
-- own. The pin records that, rather than hiding a dependency this statement did not choose.
/-- info: 'PropertyKindCalculus.dim_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dim_not_injective

/-! ## R5 — the interaction algebra is a partial, typed, ternary product -/

-- Inhabitation: on the worked SI-mechanics algebra, the sanctioned product `torque × angle =
-- energy` and its quotient hold together (mul ⇔ div), applied to concrete kinds.
theorem r5_mul_div_inverse : siMech.KDiv energyKind angleKind torqueKind :=
  (siMech.kMul_iff_kDiv torqueKind angleKind energyKind).mp SIMech.KMul.torque_angle_energy

-- Every sanctioned product outputs `energyKind` (both constructors do), so a claimed product with
-- a *different* output is refutable — the mechanism behind the algebra's partiality.
theorem sanctioned_output_energy {a b c : DimensionedKind} (h : SIMech.KMul a b c) :
    c = energyKind := by cases h <;> rfl

-- Boundary (Rule 2): the algebra is *partial* — `torque × angle = torque` is a category error
-- that no constructor sanctions, so it is provably absent. A total algebra would sanction it.
theorem r5_category_error : ¬ SIMech.KMul torqueKind angleKind torqueKind := fun h =>
  torque_angle_work.2.1 (congrArg DimensionedKind.kind (sanctioned_output_energy h)).symm

/-- info: 'PropertyKindCalculus.InteractionAlgebra.kMul_iff_kDiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms InteractionAlgebra.kMul_iff_kDiv

/-! ## R7 — dimension certifies coherence; it does not decide legality -/

-- Inhabitation: every sanctioned product is dimensionally coherent — `dim` carries the kind
-- product to the dimension product, applied to the concrete `torque × angle = energy` edge.
theorem r7_dim_homomorphism :
    energyKind.toDimension = torqueKind.toDimension * angleKind.toDimension :=
  siMech.dim_homomorphism SIMech.KMul.torque_angle_energy

-- The R7 point (and its boundary): matching dimension is *necessary but not sufficient* — energy
-- and torque share a dimension yet are distinct kinds, so `dim` cannot decide legality.
theorem r7_dim_not_sufficient :
    energyKind.toDimension = torqueKind.toDimension ∧ energyKind.kind ≠ torqueKind.kind :=
  ⟨torque_angle_work.2.2, torque_angle_work.2.1⟩

/-- info: 'PropertyKindCalculus.InteractionAlgebra.dim_homomorphism' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms InteractionAlgebra.dim_homomorphism

/-! ## R13 — scale-spanning units are a third category, not a function of dimension -/

-- Inhabitation: the kelvin is scale-spanning — its *proposed* reduction (energy, via k_B) is
-- mechanically reducible, yet its *actual* dimension Θ is not, so membership cannot be read off
-- the dimension layer. A concrete witness of the "extra datum" R13 asserts.
theorem r13_kelvin_scale_spanning :
    Dimension.MechanicallyReducible ScaleSpanning.kelvin.reducesTo
      ∧ ¬ Dimension.MechanicallyReducible Dim.temperature :=
  ScaleSpanning.kelvin_reduction_invisible_to_dimension

/-- info: 'PropertyKindCalculus.ScaleSpanning.scaleSpanning_not_determined_by_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms ScaleSpanning.scaleSpanning_not_determined_by_dimension

/-! ## R17 — unit conversion round-trips exactly over ℝ (the numeric companion) -/

/-- The metre and two SI prefixings of it (radix 10). -/
def metre : MetrologicalUnit := ({ id := "length", scale := .ratio } : KindOfProperty).unit "m"
def cm : PrefixedUnit := metre.withPrefix SIPrefix.centi
def km : PrefixedUnit := metre.withPrefix SIPrefix.kilo

-- Inhabitation: converting a real magnitude cm → km → cm returns it *exactly*, applied to a
-- concrete same-radix pair (premises `SameRadix` by `rfl`, `radix ≠ 0` by `decide`).
theorem r17_real_roundtrip (x : ℝ) : km.convertReal cm (cm.convertReal km x) = x :=
  PrefixedUnit.convertReal_roundtrip cm km rfl (by decide) x

/-- info: 'PropertyKindCalculus.PrefixedUnit.convertReal_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PrefixedUnit.convertReal_roundtrip

/-! ## R17 — §1.22 is the single-generator instance of the contributed unit twin

`UnitScale B` and `UnitScale.dimScale` (PhysLib `ParametricUnits`, the unit twin of the
basis-parametric `Dimension B`) are the generic *chosen-reference* unit the prefix work
anticipated. The bridge exhibits the §1.22 factor as `dimScale` at a generator, applied here
to the concrete cm → km pair over the canonical basis. -/

-- Inhabitation: the generic conversion factor of the two induced unit choices, read at the
-- length generator, is exactly the prefix factor `10 ^ (−2 − 3)` the §1.22 layer computes.
theorem r17_dimScale_is_prefix_factor :
    (((cm.toUnitScale LTMCTDimensionBase.length (by decide)).dimScale
        (km.toUnitScale LTMCTDimensionBase.length (by decide))
        (Dimension.single LTMCTDimensionBase.length) : ℝ)) = cm.realFactor km :=
  PrefixedUnit.dimScale_toUnitScale_single cm km rfl (by decide) _

/-- info: 'PropertyKindCalculus.PrefixedUnit.dimScale_toUnitScale_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PrefixedUnit.dimScale_toUnitScale_single

end PropertyKindCalculus.Tests.DimensionBridges

end Blanket
