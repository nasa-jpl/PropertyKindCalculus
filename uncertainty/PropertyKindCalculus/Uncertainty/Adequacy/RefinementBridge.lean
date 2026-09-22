/-
`PropertyKindCalculus.Uncertainty.Adequacy.RefinementBridge` — **which bridge carries which half of
A3′** (`UNCERTAINTY.md` §7).

Two routes connect the executable binary32 rung to the `ℝ` specification, and it was an open
question whether the adequacy layer should be consolidated onto one of them:

  * the **algebraic** route — PKC's `CarrierRefinement E S`, with `MulRefinement`/`DivRefinement`
    beside it. Its content is one *equation* per operator: the executable operation, forgotten to
    the specification carrier, is the rounding of the specification operation
    (`toSpec (x ⊕ y) = round (toSpec x + toSpec y)`).
  * the **metric** route — TorchLean's `FP32.*_abs_error`, packaged here as
    `Fp32Grounding.{add32,sub32,mul32,div32}_within_half_ulp`. Its content is one *bound* per
    operator: the executable result is within half a ulp of the exact one.

They are not alternatives, and this module is why. They answer different questions, their side
conditions are of different kinds, and A3′ needs one of each:

  * **An equation is not a bound and a bound is not an equation.** The algebraic route says what the
    executable operation *is*; the metric route says how far it is. The first implies the second
    given a bound on `round`; the second implies nothing about the first.
  * **Their side conditions are about different things.** `DivRefinement` is unconditional at the
    specification rung only because `ℝ` totalizes `x / 0` — a *definedness* question, and the reason
    the executable rung's version instead carries the divisor's nonzero decoded mantissa. `DagBound`
    carries `Regular` at a `div` node for an unrelated reason: the per-operation bound
    `Fp32Grounding.div32_within_half_ulp` has **no** hypothesis at all, and `Regular` guards the
    *propagation* factors `1/|b|` and `|a|/|b|²` — a *magnitude* question. A consolidated bridge
    would have to conflate the two, and `Uncertainty.Adequacy.MeanBound` shows what that would cost:
    at the weighted mean's single `div` node the two rungs' licenses are genuinely independent in
    both directions.
  * **They meet, and the meeting point is checked here.** The refinement's rounding *is* the
    format's: `CarrierRefinement.round (E := FP32)` and `round32` are the same function. So
    `DagBound.ExactRepresentable` — the condition under which the metric bound collapses to equality
    — is precisely the statement that the refinement's rounding is the identity along the
    evaluation. `refinementFixes_iff_exactRepresentable` proves that, and
    `toSpec_evalFP32_eq_evalExact` states A3′'s exact case in the refinement's own vocabulary.

**The decision, then: keep both, with this division of labour.** The forward-error accumulation and
box faithfulness are metric and stay on `*_abs_error`; the exactness regime is algebraic and is a
`CarrierRefinement` statement, as the theorems below make machine-checked rather than asserted.
Proved over `ℝ`/`FP32`, sorry-free.
-/

module

public import PropertyKindCalculus.Uncertainty.Adequacy.DagBound
public import PropertyKindCalculus.Torch.Fp32

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Uncertainty.Adequacy

open TorchLean.Floats
open TorchLean.Floats.IEEE754
open FloatLib.Floats.Formats.Flocq (genericFormat)
open FloatLib.Numerics (binaryRadix)
open PropertyKindCalculus

/-! ## The refinement's rounding is the format's -/

/-- **The two roundings are one function.** `CarrierRefinement FP32 ℝ` rounds by
`IEEE32Exec.fp32Round`, which is `round32`; the identification is definitional, so every fact proved
about one applies to the other with no transport. -/
theorem refinement_round_eq_round32 (x : ℝ) :
    CarrierRefinement.round (E := FP32) x = round32 x := rfl

/-- **Hence the refinement's rounding fixes exactly the representable reals.** This is
`Fp32Grounding.round32_eq_self_iff` read as a statement about the R10 bridge. -/
theorem refinement_round_eq_self_iff (x : ℝ) :
    CarrierRefinement.round (E := FP32) x = x ↔ genericFormat binaryRadix fexp32 x :=
  round32_eq_self_iff x

/-- **And its forgetful map is the format's `.val`.** -/
theorem refinement_toSpec_eq_val (x : FP32) :
    CarrierRefinement.toSpec (S := ℝ) x = x.val := rfl

/-! ## Flag-freedom, said in the bridge's vocabulary -/

/-- Flag-freedom stated with the *refinement's* rounding rather than the format's: at every node,
`CarrierRefinement.round` fixes that node's exact value. Equivalent to
`DagBound.ExactRepresentable` (`refinementFixes_iff_exactRepresentable`) — which is the sense in
which the exactness half of A3′ is a `CarrierRefinement` statement. -/
def RefinementFixes : Expr → (ℕ → FP32) → Prop
  | .inp _,   _ => True
  | .const _, _ => True
  | .add a b, ρ => RefinementFixes a ρ ∧ RefinementFixes b ρ ∧
      CarrierRefinement.round (E := FP32) (evalExact a ρ + evalExact b ρ)
        = evalExact a ρ + evalExact b ρ
  | .sub a b, ρ => RefinementFixes a ρ ∧ RefinementFixes b ρ ∧
      CarrierRefinement.round (E := FP32) (evalExact a ρ - evalExact b ρ)
        = evalExact a ρ - evalExact b ρ
  | .mul a b, ρ => RefinementFixes a ρ ∧ RefinementFixes b ρ ∧
      CarrierRefinement.round (E := FP32) (evalExact a ρ * evalExact b ρ)
        = evalExact a ρ * evalExact b ρ
  | .div a b, ρ => RefinementFixes a ρ ∧ RefinementFixes b ρ ∧
      CarrierRefinement.round (E := FP32) (evalExact a ρ / evalExact b ρ)
        = evalExact a ρ / evalExact b ρ

/-- **The vocabularies agree.** Node by node, "the refinement's rounding fixes this value" and "this
value is representable" are the same statement — `refinement_round_eq_self_iff` under an induction
that does nothing else. -/
theorem refinementFixes_iff_exactRepresentable (ρ : ℕ → FP32) :
    ∀ e : Expr, RefinementFixes e ρ ↔ ExactRepresentable e ρ := by
  intro e
  induction e with
  | inp _ => exact Iff.rfl
  | const _ => exact Iff.rfl
  | add a b iha ihb =>
    exact and_congr iha (and_congr ihb (refinement_round_eq_self_iff _))
  | sub a b iha ihb =>
    exact and_congr iha (and_congr ihb (refinement_round_eq_self_iff _))
  | mul a b iha ihb =>
    exact and_congr iha (and_congr ihb (refinement_round_eq_self_iff _))
  | div a b iha ihb =>
    exact and_congr iha (and_congr ihb (refinement_round_eq_self_iff _))

/-! ## A3′'s exact case, in the bridge's vocabulary -/

/-- **Forgetting the executable evaluation is the exact evaluation, where the refinement's rounding
does nothing.** `DagBound.evalFP32_val_eq_exact_of_exactRepresentable` with `.val` read as the
refinement's forgetful map — the exactness half of A3′ as a statement about R10. -/
theorem toSpec_evalFP32_eq_evalExact (e : Expr) (ρ : ℕ → FP32) (h : RefinementFixes e ρ) :
    CarrierRefinement.toSpec (S := ℝ) (evalFP32 e ρ) = evalExact e ρ :=
  evalFP32_val_eq_exact_of_exactRepresentable ρ e
    ((refinementFixes_iff_exactRepresentable ρ e).mp h)

/-- **And the box equality.** Where the refinement rounds nothing at either input, the executable
measurand's variation over the box, forgotten to the specification carrier, is exactly the
specification's. -/
theorem toSpec_box_exact (e : Expr) (ρ σ : ℕ → FP32)
    (hρ : RefinementFixes e ρ) (hσ : RefinementFixes e σ) :
    CarrierRefinement.toSpec (S := ℝ) (evalFP32 e σ)
        - CarrierRefinement.toSpec (S := ℝ) (evalFP32 e ρ)
      = evalExact e σ - evalExact e ρ := by
  rw [toSpec_evalFP32_eq_evalExact e σ hσ, toSpec_evalFP32_eq_evalExact e ρ hρ]

end PropertyKindCalculus.Uncertainty.Adequacy

end -- pkc-blanket-expose
end -- pkc-blanket
