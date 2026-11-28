/-
# DimensionalHomogeneity — the third capstone, on PhysLib's dimensions

`Provenance.homogeneity` (core, `Derivation`) is stated over any rule algebra. This module
supplies the one the coverage command evaluates (`DimensionalCoverage`): on PhysLib's
`Dimension B`, a product adds the operand exponents, a quotient subtracts them, a
reciprocal negates them, a power scales them by its rational exponent, a transcendental
demands dimension one, a reference and a copy preserve, a same-kind sum demands equal
operands, and a nominal selection demands equal branches. A `step` has no rule — a
procedure edge's dimensional content is its member's own graph.

With that algebra, `dimensional_homogeneity` is the third capstone: for a well-formed
provenance hypergraph whose declared dimensions are homomorphic along every occurrence —
the verdict the coverage command reports as `[coherent]`, per occurrence — the dimension
of every derived node and every output is the one the rules compute from the sources'
dimensions, and any assignment that follows the rules from the same sources agrees with
the declared one everywhere. `dim_homomorphism` (`Interaction`) is the per-edge, per-algebra
form of the same fact for a curated product; `product_rule` below is where the two meet.

Mathlib-backed through PhysLib, so it lives in the `Dimension` library; build with
`lake build Dimension`.
-/

module

public import PropertyKindCalculus.Dimension
public import PropertyKindCalculus.Derivation

@[expose] public section Blanket

open Dimension

namespace PropertyKindCalculus.DimensionalHomogeneity

open PropertyKindCalculus.Provenance (EdgeFamily DimRule Homomorphic declaredDim)

variable {B : Type} [DimensionBasis B] [Fintype B]

/-- Are all the dimensions in a list equal to a given one? -/
def allEq (d : Dimension B) : List (Dimension B) → Bool
  | [] => true
  | d' :: ds => decide (d' = d) && allEq d ds

/-- **The rule algebra of the coverage command**, on PhysLib dimensions: the result
dimension each edge family computes from its operands' dimensions, or `none` where the
family's rule is violated or the family has none. -/
def dimRule : DimRule (Dimension B)
  | .product, [a, b] => some (a * b)
  | .tableMul, [a, b] => some (a * b)
  | .quotient, [a, b] => some (a / b)
  | .tableDiv, [a, b] => some (a / b)
  | .reciprocal, [a] => some a⁻¹
  | .power p, [a] => some (a ^ p)
  | .transcendental, [a] => if a = 1 then some 1 else none
  | .realPower, [a, b] => if a = 1 ∧ b = 1 then some 1 else none
  | .reference, [a] => some a
  | .additive, [a, b] => if a = b then some a else none
  | .copy, [a] => some a
  | .select _, _ :: b :: bs => if allEq b bs then some b else none
  | _, _ => none

/-- The product rule is the curated homomorphism's equation: the result's dimension is the
product of the operands'. -/
lemma product_rule (a b : Dimension B) : dimRule .product [a, b] = some (a * b) := rfl

/-- The quotient rule: exponents subtract. -/
lemma quotient_rule (a b : Dimension B) : dimRule .quotient [a, b] = some (a / b) := rfl

/-- The transcendental rule refuses a dimensioned operand. -/
lemma transcendental_rule_of_ne_one (a : Dimension B) (h : a ≠ 1) :
    dimRule .transcendental [a] = none := by
  simp [dimRule, h]


/-- The real-power rule refuses a dimensioned base. -/
lemma realPower_rule_of_base_ne_one (a b : Dimension B) (h : a ≠ 1) :
    dimRule .realPower [a, b] = none := by
  simp [dimRule, h]

/-- The real-power rule refuses a dimensioned exponent. -/
lemma realPower_rule_of_exponent_ne_one (a b : Dimension B) (h : b ≠ 1) :
    dimRule .realPower [a, b] = none := by
  simp [dimRule, h]

/-- On a dimension-one base and exponent the real power is dimension one. -/
lemma realPower_rule_one : dimRule (B := B) .realPower [1, 1] = some 1 := by
  simp [dimRule]
variable {ν κ : Type} [BEq ν] [LawfulBEq ν] [BEq κ]

/-- **Dimensional homogeneity along the hypergraph** (the third capstone). Let `g` be a
well-formed provenance hypergraph and `dimOf` the declared dimension of each kind. If the
declared assignment is homomorphic along every occurrence under the coverage rules — the
`[coherent]` verdict per occurrence — then every assignment that follows the rules from the
same source dimensions agrees with the declared one on every known node, hence on every
output and every derived node: the dimension functor is a homomorphism along every path of
`g`, and every output's dimension is computed from the sources' alone. -/
theorem dimensional_homogeneity {g : Provenance ν κ} (hwf : g.WellFormed)
    (dimOf : κ → Option (Dimension B))
    (hcov : ∀ o ∈ g.occurrences, Homomorphic dimRule (declaredDim dimOf g) o)
    {δ : ν → Option (Dimension B)} (hδ : ∀ o ∈ g.occurrences, Homomorphic dimRule δ o)
    (hsrc : ∀ s ∈ g.sources, δ s = declaredDim dimOf g s) :
    (∀ x ∈ g.known, δ x = declaredDim dimOf g x) ∧
      (∀ y ∈ g.outputs, δ y = declaredDim dimOf g y) ∧
      (∀ i ∈ g.intros, i.tier = .derived → δ i.node = declaredDim dimOf g i.node) :=
  Provenance.dimensional_homogeneity hwf hcov hδ hsrc

omit [BEq ν] [LawfulBEq ν] [BEq κ] in
/-- A product occurrence is homomorphic exactly when the result's declared dimension is the
product of the operands' — the hypergraph-level reading of `dim_homomorphism`. -/
lemma homomorphic_product_iff {δ : ν → Option (Dimension B)}
    {o : Provenance.Occurrence ν κ} (hf : o.family = .product) {x y : ν} {kx ky : κ}
    (hops : o.operands = [(x, kx), (y, ky)]) :
    Homomorphic dimRule δ o ↔
      ∃ dx dy, δ x = some dx ∧ δ y = some dy ∧ δ o.result = some (dx * dy) := by
  constructor
  · rintro ⟨ds, d, hds, hr, hres⟩
    simp only [hops, List.map_cons, List.map_nil, Provenance.dimsOf] at hds
    cases hx : δ x with
    | none => simp [hx] at hds
    | some dx =>
      cases hy : δ y with
      | none => simp [hx, hy] at hds
      | some dy =>
        simp only [hx, hy, Option.some.injEq] at hds
        subst hds
        rw [hf, product_rule] at hr
        obtain rfl := Option.some.inj hr
        exact ⟨dx, dy, rfl, rfl, hres⟩
  · rintro ⟨dx, dy, hx, hy, hres⟩
    refine ⟨[dx, dy], dx * dy, ?_, ?_, hres⟩
    · simp [hops, Provenance.dimsOf, hx, hy]
    · rw [hf]; rfl

end PropertyKindCalculus.DimensionalHomogeneity

end Blanket
