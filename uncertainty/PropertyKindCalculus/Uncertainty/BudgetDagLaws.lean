/-
`PropertyKindCalculus.Uncertainty.BudgetDagLaws` — the **law layer of the kinded ×/÷
uncertainty-budget DAG** (`BudgetDag.lean`), at the proof carrier `ℝ`.

`UNCERTAINTY.md` §4.4 and its residual item 2 specify the DAG extension of the kinded budget:
"the `ProductKind`/`QuotientKind` edges are threaded through a multi-node graph rather than a
single quadrature". `BudgetDag.lean` builds that machine; this module proves the law that keeps
the machine honest:

  **The threaded propagation collapses to the flat quadrature.** At `ℝ`, the uncertainty that
  `BudgetExpr.propagateQ` accumulates node-by-node through the tree equals — exactly, not up to a
  bound — the flat `Budget.combinedQ` quadrature over the per-leaf-occurrence contributions
  `BudgetExpr.contribsQ` (`BudgetExpr.propagateQ_unc_eq_combinedQ`). Relative to the flat
  single-quadrature `Budget` baseline, the DAG machinery therefore adds *threading only*, never a
  second combination rule — this collapse is what makes the DAG machine a faithful generalization
  of the Stage-3.4 kinded budget rather than a second authority over the same GUM content.
  ("Faithful" in the logical sense — one combination rule, provably; not the statistical claim
  that the quadrature never understates `u_c`, which no uncorrelated-form GUM budget makes.)

Contents:
  * the **scoped** `noncomputable instance instNumCarrierReal : NumCarrier ℝ` (scoped so it
    cannot perturb instance resolution outside this namespace — the `Torch` library carries a
    global `Context`-based `NumCarrier` forwarding instance that must not be raced), with two
    `rfl` bridge lemmas `MathCarrier.sqrt = Real.sqrt` / `MathCarrier.abs = |·|` so proofs never
    mention the instance internals;
  * the `sumSq` sum-of-squares toolkit, in the exact left-fold shape `combinedQ` computes
    (fold-from-`init` form, nonnegativity, `++`, and the three scaled-family laws
    `sumSq_map_mul_left`/`sumSq_map_mul_right`/`sumSq_map_div`);
  * `combinedQ_magnitude_real` — `Budget.combinedQ`'s magnitude re-spoken in
    `Real.sqrt`/`sumSq` vocabulary;
  * `BudgetExpr.NonnegUncs` — nonnegativity of every leaf uncertainty, statable only at the
    ordered proof carrier (the core `NumCarrier` is deliberately branchless/orderless);
  * the capstone `BudgetExpr.propagateQ_unc_eq_combinedQ`, and the two textbook
    relative-uncertainty quadrature corollaries for single `mul`/`div` nodes.

Honest scope. Independence at every node is *specified*, exactly as the flat `combinedQ`
specifies it globally: there are no correlation terms, and a shared subterm written twice is, by
construction, two independent inputs. The per-node first-order sensitivities (`u_a·|b|`,
`|a|·u_b`, `u_a/|b|`, `(|y|·u_b)/|b|`) are the specified GUM linearizations, not derived here
from any differential calculus — the capstone is the *bookkeeping* law that the threaded and the
flat readings of that one specification agree. Division is `ℝ`'s totalized `x / 0 = 0`, so the
capstone carries **no** divisor-nonzero hypotheses: at a zero divisor both sides degenerate
identically; the statistical meaningfulness of the specified linearization near a zero divisor is
a caveat on the specification, not a hypothesis of this law. Everything here is at `ℝ`; the
`Float`/FP32 adequacy of the same quadrature is the Stage-3 `Adequacy` machinery's concern, not
this module's.
-/

module

public import PropertyKindCalculus.Uncertainty.BudgetDag
public import PropertyKindCalculus.Function
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Uncertainty

open PropertyKindCalculus (Quantity ProductKind QuotientKind KindOfProperty MathCarrier)
open PropertyKindCalculus.Paradigm (NumCarrier)

/-! ## The `ℝ` carrier instance (scoped) and its two bridge facts -/

/-- **`ℝ` as a branchless numeric carrier** — the proof representation for the budget DAG.
Scoped to `PropertyKindCalculus.Uncertainty` so it cannot perturb instance resolution elsewhere
(the `Torch` library carries a global `Context`-based `NumCarrier` forwarding instance that this
instance must not race). All arithmetic/lattice parents are Mathlib's; `MathCarrier` is pinned
*explicitly* to the dimension layer's `instMathCarrierReal` so the two bridge lemmas below hold
by `rfl`; the sole parent `ℝ` lacks is `Coe Nat ℝ`, supplied by `Nat.cast`. Noncomputable, like
the real special functions it forwards to. -/
noncomputable scoped instance instNumCarrierReal : NumCarrier ℝ where
  toMathCarrier := PropertyKindCalculus.instMathCarrierReal
  toCoe := ⟨Nat.cast⟩

/-- Bridge: the carrier `sqrt` at `ℝ` *is* `Real.sqrt` — definitional, so proofs downstream
speak Mathlib vocabulary and never the instance internals. -/
@[simp] theorem mathCarrier_sqrt_real (x : ℝ) : MathCarrier.sqrt x = Real.sqrt x := rfl

/-- Bridge: the carrier `abs` at `ℝ` *is* `|·|` — definitional, the `abs` counterpart of
`mathCarrier_sqrt_real`. -/
@[simp] theorem mathCarrier_abs_real (x : ℝ) : MathCarrier.abs x = |x| := rfl

/-! ## The sum-of-squares toolkit

`combinedQ` computes its radicand as a left fold `foldl (fun acc x => acc + x·x) 0`; naming that
shape `sumSq` and proving its algebra once is what lets every case of the capstone reduce to a
`ring`-closable radicand identity. -/

/-- **Sum of squares** of a list of reals, in the exact left-fold shape `combinedQ`'s quadrature
computes — so the bridge `combinedQ_magnitude_real` below is one `List.foldl_map` away. -/
def sumSq (l : List ℝ) : ℝ := l.foldl (fun a x => a + x * x) 0

/-- The fold engine with the accumulator generalized: folding squares onto any `init` is `init`
plus folding onto `0`. The single induction every other `sumSq` lemma reuses. -/
theorem foldl_add_sq (l : List ℝ) : ∀ init : ℝ,
    l.foldl (fun a x => a + x * x) init = init + l.foldl (fun a x => a + x * x) 0 := by
  induction l with
  | nil => intro init; simp
  | cons x xs ih =>
      intro init
      rw [List.foldl_cons, List.foldl_cons, ih (init + x * x), ih (0 + x * x)]
      ring

/-- The `foldl` form from any starting accumulator equals `init + sumSq l` — `sumSq`'s
definitional fold, re-read from an arbitrary `init`. -/
theorem sumSq_foldl (l : List ℝ) (init : ℝ) :
    l.foldl (fun a x => a + x * x) init = init + sumSq l :=
  foldl_add_sq l init

/-- `sumSq` of the empty list is `0` (definitional). -/
@[simp] theorem sumSq_nil : sumSq ([] : List ℝ) = 0 := rfl

/-- Peel one square off the front of a `sumSq`. -/
@[simp] theorem sumSq_cons (x : ℝ) (l : List ℝ) : sumSq (x :: l) = x * x + sumSq l := by
  show (x :: l).foldl (fun a x => a + x * x) 0 = x * x + sumSq l
  rw [List.foldl_cons, sumSq_foldl]
  ring

/-- A sum of squares is nonnegative — the fact that licenses `Real.mul_self_sqrt` /
`Real.sq_sqrt` on every radicand below. -/
theorem sumSq_nonneg (l : List ℝ) : 0 ≤ sumSq l := by
  induction l with
  | nil => simp
  | cons x xs ih => rw [sumSq_cons]; exact add_nonneg (mul_self_nonneg x) ih

/-- Quadrature radicands concatenate additively: `sumSq (l₁ ++ l₂) = sumSq l₁ + sumSq l₂`. -/
theorem sumSq_append (l₁ l₂ : List ℝ) : sumSq (l₁ ++ l₂) = sumSq l₁ + sumSq l₂ := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc]

/-- Sum of squares of a *left*-scaled family: the scale factor exits as `c·c`. Stated over an
arbitrary projected family `l.map f` (rather than a bare `List ℝ`) so it matches the `contribsQ`
magnitude maps directly, with no `List.map_map` re-association. -/
theorem sumSq_map_mul_left {α : Type*} (f : α → ℝ) (c : ℝ) (l : List α) :
    sumSq (l.map fun x => c * f x) = c * c * sumSq (l.map f) := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, sumSq_cons, ih]; ring

/-- Sum of squares of a *right*-scaled family: the mirror of `sumSq_map_mul_left`, matching the
`mul` node's left-contribution family `c ↦ c·|b|`. -/
theorem sumSq_map_mul_right {α : Type*} (f : α → ℝ) (c : ℝ) (l : List α) :
    sumSq (l.map fun x => f x * c) = sumSq (l.map f) * (c * c) := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, sumSq_cons, ih]; ring

/-- Sum of squares of a divided family: the divisor exits as `/(c·c)`. Holds **also for divisor
`c = 0`** under `ℝ`'s totalized `x / 0 = 0` — the left side is then a sum of squares of zeros and
the right side a division by zero, both `0` — which is exactly why the capstone's `div` case
needs no divisor-nonzero hypothesis. -/
theorem sumSq_map_div {α : Type*} (f : α → ℝ) (c : ℝ) (l : List α) :
    sumSq (l.map fun x => f x / c) = sumSq (l.map f) / (c * c) := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, sumSq_cons, ih]; ring

/-! ## The `combinedQ` bridge -/

/-- **The `combinedQ` bridge**: at `ℝ`, the combined-uncertainty magnitude is `Real.sqrt` of
`sumSq` of the contribution magnitudes — `Budget.combinedQ_magnitude` re-spoken in Mathlib
vocabulary through the instance bridges. The single point where the carrier fold meets the proof
toolkit; deliberately *not* `@[simp]`, so the existing `combinedQ_magnitude` normal form is left
undisturbed (proofs here cite it explicitly). -/
theorem combinedQ_magnitude_real {k : KindOfProperty} (l : List (Quantity k ℝ)) :
    (combinedQ l).magnitude = Real.sqrt (sumSq (l.map Quantity.magnitude)) := by
  rw [combinedQ_magnitude, mathCarrier_sqrt_real]
  congr 1
  simp only [sumSq, List.foldl_map]

/-! ## Nonnegative leaf uncertainties -/

/-- **Every leaf uncertainty in the tree is nonnegative** — a leaf demands `0 ≤ u`, a `mul`/`div`
node demands both children. This predicate cannot live in the core `BudgetDag` module:
`NumCarrier` is deliberately branchless and therefore *orderless* — it carries no `LT`/`LE`/`BEq`
on the carrier — so nonnegativity is only statable here, at the ordered proof carrier `ℝ`. Every
genuinely seeded leaf satisfies it (`EstimateQ.ofInputDist`'s uncertainty is a square root), but
`EstimateQ` leaves are free records, so the capstone carries it as a hypothesis rather than a
construction-time invariant. -/
def BudgetExpr.NonnegUncs : {k : KindOfProperty} → BudgetExpr ℝ k → Prop
  | _, .leaf q => 0 ≤ q.unc.magnitude
  | _, .mul _ a b => a.NonnegUncs ∧ b.NonnegUncs
  | _, .div _ a b => a.NonnegUncs ∧ b.NonnegUncs

/-! ## The capstone — threaded propagation collapses to the flat quadrature -/

/-- **The collapse law.** For every expression with nonnegative leaf uncertainties, the
uncertainty `propagateQ` accumulates node-by-node — `√` at every node, re-squared by the parent's
quadrature — telescopes *exactly* to the flat `Budget.combinedQ` quadrature over the flattened
per-leaf contributions `contribsQ`. Relative to the flat single-quadrature `Budget` baseline, the
DAG machine therefore adds threading only, never a second combination rule: the faithful-
generalization fact the `BudgetDag` design promises (faithful in the logical sense, not a
statistical never-understates claim).

Proof: structural induction; `Quantity.ext` reduces each case to a magnitude identity; the leaf
case is `√(u·u) = u` — the one place the `NonnegUncs` hypothesis is spent; the node cases rewrite
both sides into `Real.sqrt`-of-`sumSq` normal form (`combinedQ_magnitude_real`, `sumSq_append`,
the `sumSq_map_*` family, with sub-values renamed through the core
`propagateQ_value_eq_valueQ`), re-express each child radicand `S` as `√S·√S`
(`Real.mul_self_sqrt`, licensed by `sumSq_nonneg`), and close by `ring`.

There are **no divisor-nonzero hypotheses**: division is `ℝ`'s totalized `x / 0 = 0` and both
sides degenerate identically at a zero divisor (`sumSq_map_div` holds there too). The statistical
meaningfulness of the specified first-order linearization near a zero divisor is a caveat on the
specification, not a hypothesis of this bookkeeping law. -/
theorem BudgetExpr.propagateQ_unc_eq_combinedQ {k : KindOfProperty}
    (e : BudgetExpr ℝ k) (hne : e.NonnegUncs) :
    (e.propagateQ).unc = combinedQ e.contribsQ := by
  induction e with
  | leaf q =>
      simp only [BudgetExpr.NonnegUncs] at hne
      apply PropertyKindCalculus.Quantity.ext
      simp only [BudgetExpr.propagateQ, BudgetExpr.contribsQ, combinedQ_magnitude_real,
        List.map_cons, List.map_nil, sumSq_cons, sumSq_nil, add_zero]
      exact (Real.sqrt_mul_self hne).symm
  | mul h a b iha ihb =>
      simp only [BudgetExpr.NonnegUncs] at hne
      obtain ⟨ha, hb⟩ := hne
      apply PropertyKindCalculus.Quantity.ext
      simp only [BudgetExpr.propagateQ, BudgetExpr.contribsQ, iha ha, ihb hb,
        BudgetExpr.propagateQ_value_eq_valueQ, combinedQ_magnitude_real,
        List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
        PropertyKindCalculus.Quantity.mul_magnitude, PropertyKindCalculus.Quantity.abs_magnitude,
        mathCarrier_abs_real, sumSq_cons, sumSq_nil, sumSq_append,
        sumSq_map_mul_left, sumSq_map_mul_right, add_zero]
      congr 1
      conv_rhs =>
        rw [← Real.mul_self_sqrt (sumSq_nonneg ((BudgetExpr.contribsQ a).map Quantity.magnitude)),
            ← Real.mul_self_sqrt (sumSq_nonneg ((BudgetExpr.contribsQ b).map Quantity.magnitude))]
      ring
  | div h a b iha ihb =>
      simp only [BudgetExpr.NonnegUncs] at hne
      obtain ⟨ha, hb⟩ := hne
      apply PropertyKindCalculus.Quantity.ext
      simp only [BudgetExpr.propagateQ, BudgetExpr.contribsQ, iha ha, ihb hb,
        BudgetExpr.propagateQ_value_eq_valueQ, combinedQ_magnitude_real,
        List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
        PropertyKindCalculus.Quantity.mul_magnitude, PropertyKindCalculus.Quantity.div_magnitude,
        PropertyKindCalculus.Quantity.abs_magnitude,
        mathCarrier_abs_real, sumSq_cons, sumSq_nil, sumSq_append,
        sumSq_map_mul_left, sumSq_map_div, add_zero]
      congr 1
      conv_rhs =>
        rw [← Real.mul_self_sqrt (sumSq_nonneg ((BudgetExpr.contribsQ a).map Quantity.magnitude)),
            ← Real.mul_self_sqrt (sumSq_nonneg ((BudgetExpr.contribsQ b).map Quantity.magnitude))]
      ring

/-! ## Textbook corollaries — the relative-uncertainty quadratures -/

/-- **Relative-uncertainty quadrature at a product node** (the relative form of the GUM §4.4
product row): for a single `mul` node on two leaves with nonzero values, the squared relative
uncertainty of the propagated result is the sum of the squared relative uncertainties of the
inputs — `(u_y/|y|)² = (u_a/|a|)² + (u_b/|b|)²`. Unlike the capstone, the nonzero-value
hypotheses are genuinely needed here: relative uncertainty divides by the value. -/
theorem BudgetExpr.mul_leaf_relative_quadrature {k1 k2 k : KindOfProperty}
    (h : ProductKind k1 k2 k) (qa : EstimateQ k1 ℝ) (qb : EstimateQ k2 ℝ)
    (hva : qa.value.magnitude ≠ 0) (hvb : qb.value.magnitude ≠ 0) :
    ((BudgetExpr.mul h (.leaf qa) (.leaf qb)).propagateQ.unc.magnitude
        / |(BudgetExpr.mul h (.leaf qa) (.leaf qb)).propagateQ.value.magnitude|) ^ 2
      = (qa.unc.magnitude / |qa.value.magnitude|) ^ 2
        + (qb.unc.magnitude / |qb.value.magnitude|) ^ 2 := by
  have hA : |qa.value.magnitude| ≠ 0 := abs_ne_zero.mpr hva
  have hB : |qb.value.magnitude| ≠ 0 := abs_ne_zero.mpr hvb
  simp only [BudgetExpr.propagateQ, combinedQ_magnitude_real, List.map_cons, List.map_nil,
    PropertyKindCalculus.Quantity.mul_magnitude, PropertyKindCalculus.Quantity.abs_magnitude,
    mathCarrier_abs_real, abs_mul]
  rw [div_pow, Real.sq_sqrt (sumSq_nonneg _), sumSq_cons, sumSq_cons, sumSq_nil, add_zero]
  field_simp

/-- **Relative-uncertainty quadrature at a quotient node** (the relative form of the GUM §4.4
quotient row): same right-hand side as the product corollary — at first order, multiplication and
division are indistinguishable in *relative* terms, which is exactly why the relative form is the
textbook mnemonic. Nonzero values required, as in the product case. -/
theorem BudgetExpr.div_leaf_relative_quadrature {k1 k2 k : KindOfProperty}
    (h : QuotientKind k1 k2 k) (qa : EstimateQ k1 ℝ) (qb : EstimateQ k2 ℝ)
    (hva : qa.value.magnitude ≠ 0) (hvb : qb.value.magnitude ≠ 0) :
    ((BudgetExpr.div h (.leaf qa) (.leaf qb)).propagateQ.unc.magnitude
        / |(BudgetExpr.div h (.leaf qa) (.leaf qb)).propagateQ.value.magnitude|) ^ 2
      = (qa.unc.magnitude / |qa.value.magnitude|) ^ 2
        + (qb.unc.magnitude / |qb.value.magnitude|) ^ 2 := by
  have hA : |qa.value.magnitude| ≠ 0 := abs_ne_zero.mpr hva
  have hB : |qb.value.magnitude| ≠ 0 := abs_ne_zero.mpr hvb
  simp only [BudgetExpr.propagateQ, combinedQ_magnitude_real, List.map_cons, List.map_nil,
    PropertyKindCalculus.Quantity.mul_magnitude, PropertyKindCalculus.Quantity.div_magnitude,
    PropertyKindCalculus.Quantity.abs_magnitude, mathCarrier_abs_real, abs_div]
  rw [div_pow, Real.sq_sqrt (sumSq_nonneg _), sumSq_cons, sumSq_cons, sumSq_nil, add_zero]
  field_simp

end PropertyKindCalculus.Uncertainty

end -- pkc-blanket-expose
end -- pkc-blanket
