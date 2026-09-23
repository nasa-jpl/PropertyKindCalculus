/-
`PropertyKindCalculus.Uncertainty.BudgetDag` — the **kinded ×/÷ uncertainty-budget DAG**
(`UNCERTAINTY.md` §4.4; residual item 2: "the `ProductKind`/`QuotientKind` edges are threaded
through a multi-node graph rather than a single quadrature").

`analyzeQ` (`Adequacy/Significance.lean`, composing `Budget.lean`'s primitives) covers the
*homogeneous-input* case: one flat quadrature at a single
output kind `kₒ`, fed by autograd sensitivities. A genuinely heterogeneous multiply/divide model —
each internal node with its own kind equation — needs the kind gates *threaded through the
expression*. This module supplies that: `BudgetExpr R k` is a kinded ×/÷ expression whose every
`mul`/`div` node **carries its `ProductKind`/`QuotientKind` witness as a constructor field**, so an
ill-kinded expression cannot be written, and every interpretation below (`valueQ`, `propagateQ`,
`contribsQ`) is built exclusively by the kind-gated `Quantity.mul`/`Quantity.div` — never a naked
carrier operation re-stamped.

The GUM first-order content per node (§4.4, the product/quotient rows of GUM Table): at a
multiplication `y = a·b` the two quadrature terms are `u_a·|b|` and `|a|·u_b`; at a division
`y = a/b` they are `u_a/|b|` and `(|y|·u_b)/|b|` — i.e. `|a|·u_b/b²`, written through the
*transposed* witness `QuotientKind.toProductKind` (`k = k₁/k₂` implies `k·k₂ = k₁`) so the
intermediate `|y|·u_b` is itself a kinded product, not an unkinded scratch value.

Honest scope. A `BudgetExpr` is a **tree**: writing a shared subterm twice states, by construction,
that its two occurrences are independent — the same independence assumption the flat `combinedQ`
quadrature makes globally (GUM's correlation term is out of frame here exactly as it is in
`Budget.lean`). This module also deliberately does NOT provide: **add/sub nodes** — the homogeneous
linear case is already served by `Budget.contributionQ`/`combinedQ` fed by autograd sensitivities
via `analyzeQ`, so duplicating it as tree nodes would be a second authoring of the same quadrature;
and **any ordering on the carrier** — `NumCarrier` is deliberately branchless, so nonnegativity
hypotheses (`NonnegUncs`) and the collapse law relating `propagateQ` to the flat `combinedQ` of
`contribsQ` live in the Mathlib-facing `BudgetDagLaws` module, not here. What *is* proved here is
carrier-generic and definitional: the equation-lemma simp set, the per-node GUM-form magnitudes,
and `propagateQ_value_eq_valueQ` (the value component of the propagated estimate is the plain
kinded evaluation). Mathlib- and TorchLean-free.
-/

module

public import PropertyKindCalculus.Uncertainty.Budget
public import PropertyKindCalculus.Uncertainty.UncertainQuantity

@[expose] public section Blanket

namespace PropertyKindCalculus.Uncertainty

open PropertyKindCalculus (Quantity ProductKind QuotientKind KindOfProperty MathCarrier)
open PropertyKindCalculus.Paradigm (NumCarrier)

/-- **A point estimate with its standard uncertainty, both at kind `k`.** The uncertainty of a
`k`-quantity is itself a `k`-quantity (`Budget.stdUncQ`), so the pair is homogeneous at `k` — the
node-level state the DAG propagation threads (value for the sensitivity factors, uncertainty for
the quadrature terms). -/
structure EstimateQ (k : KindOfProperty) (R : Type) where
  /-- The kinded point value. -/
  value : Quantity k R
  /-- The kinded standard uncertainty `u = √variance`. -/
  unc : Quantity k R

/-- Seed an `EstimateQ` from an input descriptor: the value is the distribution's mean, the
uncertainty its standard uncertainty `√variance` (`stdUncQ`) — the same seeding
`Adequacy.ofInputDist` performs on the kind-erased adequacy carrier, here kinded at `k`. -/
def EstimateQ.ofInputDist {R} [NumCarrier R] {k} (d : InputDist R) : EstimateQ k R :=
  { value := ⟨d.moments.mean⟩, unc := stdUncQ d.moments }

/-- Read an `UncertainQuantity` down to its leaf estimate: the stated point value (which may
deliberately differ from the distribution's mean, per `UncertainQuantity`) paired with the
descriptor's standard uncertainty. -/
def UncertainQuantity.toEstimateQ {R} [NumCarrier R] {k} (q : UncertainQuantity k R) :
    EstimateQ k R :=
  { value := q.value, unc := stdUncQ q.dist.moments }

/-- **A kinded ×/÷ uncertainty-budget expression** at output kind `k`. Every `mul`/`div` node
carries its kind-law witness as a constructor field — the `ProductKind`/`QuotientKind` edges of
`UNCERTAINTY.md` §4.4 residual item 2, threaded through the multi-node graph — so an ill-kinded
expression is unwritable, and every interpretation below inherits the gates by construction.

The expression is a *tree*: writing a shared subterm twice states, by construction, that its two
occurrences are independent (the same independence assumption `combinedQ`'s flat quadrature makes
globally). -/
inductive BudgetExpr (R : Type) : KindOfProperty → Type where
  /-- An input leaf: a point estimate with its standard uncertainty, at the leaf's kind. -/
  | leaf {k : KindOfProperty} (q : EstimateQ k R) : BudgetExpr R k
  /-- A product node `y = a·b`, licensed by `ProductKind k1 k2 k`. -/
  | mul {k1 k2 k : KindOfProperty} (h : ProductKind k1 k2 k)
      (a : BudgetExpr R k1) (b : BudgetExpr R k2) : BudgetExpr R k
  /-- A quotient node `y = a/b`, licensed by `QuotientKind k1 k2 k`. -/
  | div {k1 k2 k : KindOfProperty} (h : QuotientKind k1 k2 k)
      (a : BudgetExpr R k1) (b : BudgetExpr R k2) : BudgetExpr R k

/-- **Plain kinded evaluation**: the point value of the expression, every node built by the
kind-gated `Quantity.mul`/`Quantity.div` of the node's own witness. -/
def BudgetExpr.valueQ {R} [NumCarrier R] : {k : KindOfProperty} → BudgetExpr R k → Quantity k R
  | _, .leaf q => q.value
  | _, .mul h a b => Quantity.mul h (valueQ a) (valueQ b)
  | _, .div h a b => Quantity.div h (valueQ a) (valueQ b)

/-- **Node-local GUM propagation**: fold the tree bottom-up, at each node combining the two
sub-results' `(value, unc)` pairs in quadrature. At a `mul` node `y = a·b` the two quadrature
terms are `u_a·|b|` and `|a|·u_b`; at a `div` node `y = a/b` they are `u_a/|b|` and `(|y|·u_b)/|b|`
— i.e. `|a|·u_b/b²`, formed through the transposed witness `h.toProductKind` so the intermediate
`|y|·u_b` is a kinded product at `k1`. Every term is built by the kind-gated
`Quantity.mul`/`Quantity.div`, never a naked carrier operation.

Nested quadrature (`√` at every node, re-squared by the parent's `combinedQ`) states independence
of the two children at *each* node — the tree-shaped reading of the same GUM §4.4 independence
assumption `combinedQ` makes flat. -/
def BudgetExpr.propagateQ {R} [NumCarrier R] : {k : KindOfProperty} → BudgetExpr R k → EstimateQ k R
  | _, .leaf q => q
  | _, .mul h a b =>
      let pa := propagateQ a
      let pb := propagateQ b
      { value := Quantity.mul h pa.value pb.value
        unc := combinedQ [Quantity.mul h pa.unc (Quantity.abs pb.value),
                          Quantity.mul h (Quantity.abs pa.value) pb.unc] }
  | _, .div h a b =>
      let pa := propagateQ a
      let pb := propagateQ b
      let v := Quantity.div h pa.value pb.value
      { value := v
        unc := combinedQ [Quantity.div h pa.unc (Quantity.abs pb.value),
                          Quantity.div h (Quantity.mul h.toProductKind (Quantity.abs v) pb.unc)
                            (Quantity.abs pb.value)] }

/-- **Flattened per-leaf contributions** at the root kind `k`: one output-kind quadrature term per
leaf, each the leaf's uncertainty scaled by the (kinded, absolute) sensitivities accumulated along
its root path — `mul` scales the sibling's plain value in, `div` scales the dividend side by
`1/|b|` and the divisor side by `|a/b|/|b|` through the transposed witness. Feeding the result to
the flat `combinedQ` gives the *single-quadrature* reading of the same tree (one global
independence assumption instead of one per node); relating the two is the collapse law of the
Mathlib-facing `BudgetDagLaws` module, since it needs ordering facts `NumCarrier` deliberately
lacks. -/
def BudgetExpr.contribsQ {R} [NumCarrier R] :
    {k : KindOfProperty} → BudgetExpr R k → List (Quantity k R)
  | _, .leaf q => [q.unc]
  | _, .mul h a b =>
      (contribsQ a).map (fun c => Quantity.mul h c (Quantity.abs (valueQ b)))
        ++ (contribsQ b).map (fun c => Quantity.mul h (Quantity.abs (valueQ a)) c)
  | _, .div h a b =>
      (contribsQ a).map (fun c => Quantity.div h c (Quantity.abs (valueQ b)))
        ++ (contribsQ b).map (fun c =>
            Quantity.div h
              (Quantity.mul h.toProductKind
                (Quantity.abs (Quantity.div h (valueQ a) (valueQ b))) c)
              (Quantity.abs (valueQ b)))

/-! ## Seeding faithfulness — the leaf estimate reads exactly the descriptor -/

/-- The seeded value's magnitude is the descriptor's mean. -/
@[simp] theorem EstimateQ.ofInputDist_value {R} [NumCarrier R] {k} (d : InputDist R) :
    (EstimateQ.ofInputDist (k := k) d).value.magnitude = d.moments.mean := rfl

/-- The seeded uncertainty's magnitude is the descriptor's standard uncertainty `√variance` —
the same carrier `stdUnc` the flat budget's `stdUncQ` overlays. -/
@[simp] theorem EstimateQ.ofInputDist_unc {R} [NumCarrier R] {k} (d : InputDist R) :
    (EstimateQ.ofInputDist (k := k) d).unc.magnitude = stdUnc d.moments := rfl

/-! ## Equation-lemma simp set

The equation-compiler equations of the three interpreters, restated as `@[simp]` `rfl` lemmas so
downstream proofs can unfold one node at a time without naming the equation lemmas. -/

/-- `valueQ` at a leaf is the leaf's point value. -/
@[simp] theorem BudgetExpr.valueQ_leaf {R} [NumCarrier R] {k} (q : EstimateQ k R) :
    (BudgetExpr.leaf q).valueQ = q.value := rfl

/-- `valueQ` at a product node is the kind-gated product of the children's values. -/
@[simp] theorem BudgetExpr.valueQ_mul {R} [NumCarrier R] {k1 k2 k}
    (h : ProductKind k1 k2 k) (a : BudgetExpr R k1) (b : BudgetExpr R k2) :
    (BudgetExpr.mul h a b).valueQ = Quantity.mul h a.valueQ b.valueQ := rfl

/-- `valueQ` at a quotient node is the kind-gated quotient of the children's values. -/
@[simp] theorem BudgetExpr.valueQ_div {R} [NumCarrier R] {k1 k2 k}
    (h : QuotientKind k1 k2 k) (a : BudgetExpr R k1) (b : BudgetExpr R k2) :
    (BudgetExpr.div h a b).valueQ = Quantity.div h a.valueQ b.valueQ := rfl

/-- `contribsQ` at a leaf is the singleton of the leaf's uncertainty. -/
@[simp] theorem BudgetExpr.contribsQ_leaf {R} [NumCarrier R] {k} (q : EstimateQ k R) :
    (BudgetExpr.leaf q).contribsQ = [q.unc] := rfl

/-- `contribsQ` at a product node: the left contributions scaled by `|b|`, then the right
contributions scaled by `|a|`, each through the node's own witness. -/
@[simp] theorem BudgetExpr.contribsQ_mul {R} [NumCarrier R] {k1 k2 k}
    (h : ProductKind k1 k2 k) (a : BudgetExpr R k1) (b : BudgetExpr R k2) :
    (BudgetExpr.mul h a b).contribsQ
      = (a.contribsQ).map (fun c => Quantity.mul h c (Quantity.abs b.valueQ))
          ++ (b.contribsQ).map (fun c => Quantity.mul h (Quantity.abs a.valueQ) c) := rfl

/-- `contribsQ` at a quotient node: the dividend contributions scaled by `1/|b|`, then the divisor
contributions scaled by `|a/b|/|b|` through the transposed witness `h.toProductKind`. -/
@[simp] theorem BudgetExpr.contribsQ_div {R} [NumCarrier R] {k1 k2 k}
    (h : QuotientKind k1 k2 k) (a : BudgetExpr R k1) (b : BudgetExpr R k2) :
    (BudgetExpr.div h a b).contribsQ
      = (a.contribsQ).map (fun c => Quantity.div h c (Quantity.abs b.valueQ))
          ++ (b.contribsQ).map (fun c =>
              Quantity.div h
                (Quantity.mul h.toProductKind
                  (Quantity.abs (Quantity.div h a.valueQ b.valueQ)) c)
                (Quantity.abs b.valueQ)) := rfl

/-- `propagateQ` at a leaf is the leaf estimate itself. -/
@[simp] theorem BudgetExpr.propagateQ_leaf {R} [NumCarrier R] {k} (q : EstimateQ k R) :
    (BudgetExpr.leaf q).propagateQ = q := rfl

/-! ## Per-node GUM-form magnitudes

The textbook §4.4 statements at one node, on the carrier: the propagated uncertainty at a
`mul`/`div` node *is* the two-term quadrature of the GUM product/quotient rows, spelled through
`MathCarrier.sqrt`/`MathCarrier.abs` on the propagated sub-results. The `(0 + t₁·t₁) + t₂·t₂`
shape is the two-element `combinedQ` foldl, computed definitionally. -/

/-- At a product node `y = a·b`, the propagated uncertainty is the quadrature of `u_a·|b|` and
`|a|·u_b` (GUM §4.4, product row), on the propagated sub-results. -/
@[simp] theorem BudgetExpr.propagateQ_mul_unc_magnitude {R} [NumCarrier R] {k1 k2 k}
    (h : ProductKind k1 k2 k) (a : BudgetExpr R k1) (b : BudgetExpr R k2) :
    ((BudgetExpr.mul h a b).propagateQ).unc.magnitude
      = MathCarrier.sqrt
          ((0 + (a.propagateQ.unc.magnitude * MathCarrier.abs b.propagateQ.value.magnitude)
              * (a.propagateQ.unc.magnitude * MathCarrier.abs b.propagateQ.value.magnitude))
            + (MathCarrier.abs a.propagateQ.value.magnitude * b.propagateQ.unc.magnitude)
              * (MathCarrier.abs a.propagateQ.value.magnitude * b.propagateQ.unc.magnitude)) :=
  rfl

/-- At a quotient node `y = a/b`, the propagated uncertainty is the quadrature of `u_a/|b|` and
`(|a/b|·u_b)/|b|` (GUM §4.4, quotient row — the second term is `|a|·u_b/b²`), on the propagated
sub-results. -/
@[simp] theorem BudgetExpr.propagateQ_div_unc_magnitude {R} [NumCarrier R] {k1 k2 k}
    (h : QuotientKind k1 k2 k) (a : BudgetExpr R k1) (b : BudgetExpr R k2) :
    ((BudgetExpr.div h a b).propagateQ).unc.magnitude
      = MathCarrier.sqrt
          ((0 + (a.propagateQ.unc.magnitude / MathCarrier.abs b.propagateQ.value.magnitude)
              * (a.propagateQ.unc.magnitude / MathCarrier.abs b.propagateQ.value.magnitude))
            + ((MathCarrier.abs
                  (a.propagateQ.value.magnitude / b.propagateQ.value.magnitude)
                  * b.propagateQ.unc.magnitude)
                / MathCarrier.abs b.propagateQ.value.magnitude)
              * ((MathCarrier.abs
                    (a.propagateQ.value.magnitude / b.propagateQ.value.magnitude)
                    * b.propagateQ.unc.magnitude)
                  / MathCarrier.abs b.propagateQ.value.magnitude)) :=
  rfl

/-! ## The value component of the propagation is the plain evaluation -/

/-- `propagateQ` computes the same point value as `valueQ`: the uncertainty machinery rides along
without perturbing the evaluation. Structural induction on the expression; the node cases are the
equation lemmas plus the two child hypotheses. -/
theorem BudgetExpr.propagateQ_value_eq_valueQ {R} [NumCarrier R] {k : KindOfProperty}
    (e : BudgetExpr R k) : (e.propagateQ).value = e.valueQ := by
  induction e with
  | leaf q => rfl
  | mul h a b iha ihb =>
      simp only [BudgetExpr.propagateQ, BudgetExpr.valueQ, iha, ihb]
  | div h a b iha ihb =>
      simp only [BudgetExpr.propagateQ, BudgetExpr.valueQ, iha, ihb]

end PropertyKindCalculus.Uncertainty

end Blanket
