/-
`PropertyKindCalculus.Uncertainty.Adequacy.DagBound` — **A3′, the universal (whole-evaluation)
adequacy soundness theorem** over `ℝ`/`FP32` (Stage 3.1, `UNCERTAINTY.md` §6).

The per-site verdict A3 (`Adequacy.Soundness.verdict_sound`) is *local*: it certifies that the
carrier's flag at one addition site is exactly the condition "this contribution is numerically
lost". This module **lifts that per-site fact to a whole model evaluation**. A science model written
once over `[NumCarrier α]` is an *evaluation DAG* of `+`/`−` (the operations the adequacy carrier
analyses); we abstract it as an explicit `Expr` and interpret it two ways over the *real* binary32
format (TorchLean's `FP32`):

  * `evalFP32 e ρ` — the rounded floating-point measurand: every `+`/`−` node rounds to binary32
    (`(a + b).val = round32 (a.val + b.val)`);
  * `evalExact e ρ` — the exact `ℝ` measurand (no rounding), the reference.

Composing the *per-operation* rounding bounds `Fp32Grounding.{add32,sub32}_within_half_ulp` (the
genuine, Flocq-backed `FP32.{add,sub}_abs_error`) along the DAG yields:

  * **`dag_fp32_error_bound`** — the forward-error accumulation: the FP32 measurand differs from the
    `ℝ` one by at most `errBound e ρ`, the tree-sum of the per-node half-ulps `eps32`.
  * **A3′ — `dag_fp32_box_faithful`.** For *any* two inputs `ρ`, `σ` (in particular every input in a
    box around a nominal `ρ`), the FP32 output *variation* `evalFP32 σ − evalFP32 ρ` reproduces the
    exact `ℝ` output variation `evalExact σ − evalExact ρ` up to `errBound σ + errBound ρ`. So the
    FP32 measurand's uncertainty (its spread over the input box) equals the `ℝ` one **up to a proven,
    DAG-additive bound** — the universal lift of A3.
  * **A3′, flag-free case — `dag_fp32_box_exact_of_flagFree`.** When no node rounds anywhere in the
    evaluation (`FlagFree` — the DAG-level *no flagged site*, e.g. every subtraction in the Sterbenz
    regime by A2, `Adequacy.Sterbenz32.flx_sterbenz`), the bound collapses to **equality**: the FP32
    measurand's uncertainty over the box is *exactly* the `ℝ` one. Rounding is the *sole* source of
    the gap — which is precisely the adequacy hazard the carrier flags.
  * **The same regime, checkable — `ExactRepresentable` and `flagFree_iff_exactRepresentable`.**
    `FlagFree` is phrased about the floating-point intermediates, so nothing short of evaluating in
    binary32 settles it. `ExactRepresentable` asks instead that each node's *exact* value be a
    binary32 number, which is a question about the `ℝ` model and its inputs; the two cut out the same
    inputs. It is minimal for this conclusion because `round32` fixes exactly the representable reals
    (`Fp32Grounding.round32_eq_self_iff`), so nothing weaker on a node's exact value keeps that node
    from rounding. `UncertaintyExamples.AdequacyDag` discharges it on a doubling chain, which is what
    makes the flag-free theorems statements about inhabited regimes rather than about hypotheses.
    That the regime is *proper* — that some evaluations fall outside it — is witnessed at the
    executable rung by `Tests.Uncertainty.MeanBound`, where `2²⁴ ⊕ 1` returns `2²⁴`.

Scope (`UNCERTAINTY.md` §6). The DAG covers the full arithmetic operator class `+`/`−`/`×`/`÷`. The
*linear* nodes `+`/`−` are exactly the operations the per-site verdict A1/A2/A3 and the runtime
carrier flag; the *nonlinear* nodes `×`/`÷` are added here by composing their per-operation rounding
bounds `Fp32Grounding.{mul32,div32}_within_half_ulp` (the genuine `FP32.{mul,div}_abs_error`) with the
first-order *propagation* of operand errors — the magnitude-dependent factors of a GUM sensitivity
analysis (`∂(ab)/∂a = b`, `∂(a/b)/∂b = −a/b²`). Division propagation is a genuine bound only where the
denominator is nonzero, so the forward-error theorem carries a `Regular` side condition (vacuous on
any `÷`-free DAG).

What remains open is a genuinely *weaker* regime, and it is a different theorem rather than a weaker
hypothesis for this one. `ExactRepresentable` is minimal among conditions that stop every node from
rounding; a no-absorption condition would instead **allow** rounding and ask only that a tracked
contribution survive it. Equality of the variations is then false, so the conclusion has to change
too — from `dag_fp32_box_exact_of_*`'s equality to a resolution statement, lifting A1-converse
(`Adequacy.resolve`: a perturbation of at least half a ulp does move the result) along the DAG the
way `dag_fp32_error_bound` lifts the half-ulp bound. Proved over `ℝ`/`FP32`, sorry-free
(`[propext, Classical.choice, Quot.sound]`).
-/
import PropertyKindCalculus.Uncertainty.Adequacy.Fp32Grounding

namespace PropertyKindCalculus.Uncertainty.Adequacy

open TorchLean.Floats
open FloatLib.Floats.Formats.Flocq (genericFormat)
open FloatLib.Numerics (binaryRadix)

/-! ## A finite `+`/`−` evaluation DAG and its two interpretations -/

/-- A finite arithmetic **evaluation DAG** over `add`/`sub` — the operations the adequacy carrier
analyses — with indexed inputs (`inp i`) and exact binary32 constants (`const c`). This is the
formal abstraction of a WO1 model as a tree of floating-point operations. -/
inductive Expr where
  /-- The `i`-th input variable. -/
  | inp : ℕ → Expr
  /-- An exact binary32 constant. -/
  | const : FP32 → Expr
  /-- Addition node. -/
  | add : Expr → Expr → Expr
  /-- Subtraction node. -/
  | sub : Expr → Expr → Expr
  /-- Multiplication node. -/
  | mul : Expr → Expr → Expr
  /-- Division node. -/
  | div : Expr → Expr → Expr

/-- **The rounded (binary32) measurand.** Every `add`/`sub` node rounds its result to the binary32
grid: `(a + b).val = round32 (a.val + b.val)` (TorchLean's `FP32` `Add`/`Sub`). This is the
floating-point evaluation a science model actually runs. -/
noncomputable def evalFP32 : Expr → (ℕ → FP32) → FP32
  | .inp i,   ρ => ρ i
  | .const c, _ => c
  | .add a b, ρ => evalFP32 a ρ + evalFP32 b ρ
  | .sub a b, ρ => evalFP32 a ρ - evalFP32 b ρ
  | .mul a b, ρ => evalFP32 a ρ * evalFP32 b ρ
  | .div a b, ρ => evalFP32 a ρ / evalFP32 b ρ

/-- **The exact `ℝ` measurand.** The same DAG evaluated with *no rounding* over the reals — the
reference against which the floating-point evaluation's information loss is measured. -/
noncomputable def evalExact : Expr → (ℕ → FP32) → ℝ
  | .inp i,   ρ => (ρ i).val
  | .const c, _ => c.val
  | .add a b, ρ => evalExact a ρ + evalExact b ρ
  | .sub a b, ρ => evalExact a ρ - evalExact b ρ
  | .mul a b, ρ => evalExact a ρ * evalExact b ρ
  | .div a b, ρ => evalExact a ρ / evalExact b ρ

/-- **The accumulated rounding budget** of the DAG: the tree-sum of the per-node rounding half-ulps
`eps32` *plus* the propagated operand error, composed from the per-operation bounds
`Fp32Grounding.{add32,sub32,mul32,div32}_within_half_ulp`. For the *linear* nodes (`add`/`sub`) the
operand errors pass through with coefficient one, so the budget is a plain sum. For the *nonlinear*
nodes the propagation carries magnitude-dependent factors, exactly as in a first-order (GUM)
sensitivity analysis:

  * at a **product** `a·b`, operand `a`'s error is weighted by `|b|` and vice-versa
    (`∂(ab)/∂a = b`);
  * at a **quotient** `a/b`, the numerator's error is scaled by `1/|b|` and the denominator's by
    `|a|/(|b|·|b|)` (`∂(a/b)/∂a = 1/b`, `∂(a/b)/∂b = −a/b²`) — well-defined, and a genuine *bound*,
    only where the denominator is nonzero (the side condition `Regular`).

The `div` node uses the *FP32* denominator `|(evalFP32 b ρ).val|` and the *exact* denominator
`|evalExact b ρ|` — the two magnitudes the propagation identity naturally exposes. -/
noncomputable def errBound : Expr → (ℕ → FP32) → ℝ
  | .inp _,   _ => 0
  | .const _, _ => 0
  | .add a b, ρ => errBound a ρ + errBound b ρ + eps32 ((evalFP32 a ρ).val + (evalFP32 b ρ).val)
  | .sub a b, ρ => errBound a ρ + errBound b ρ + eps32 ((evalFP32 a ρ).val - (evalFP32 b ρ).val)
  | .mul a b, ρ =>
      |(evalFP32 a ρ).val| * errBound b ρ + |evalExact b ρ| * errBound a ρ
        + eps32 ((evalFP32 a ρ).val * (evalFP32 b ρ).val)
  | .div a b, ρ =>
      errBound a ρ / |(evalFP32 b ρ).val|
        + |evalExact a ρ| * errBound b ρ / (|(evalFP32 b ρ).val| * |evalExact b ρ|)
        + eps32 ((evalFP32 a ρ).val / (evalFP32 b ρ).val)

/-- `|x − y| ≤ |x| + |y|`, the triangle bound used to split a difference of errors. -/
private theorem abs_sub_bound (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [sub_eq_add_neg, ← abs_neg y]; exact abs_add_le x (-y)

/-- Half a ulp is nonnegative — immediate from the rounding bound `round32_within_half_ulp`. -/
private theorem eps_nonneg (x : ℝ) : 0 ≤ eps32 x :=
  le_trans (abs_nonneg _) (round32_within_half_ulp x)

/-- The rounding budget is nonnegative: it is a sum of half-ulps. -/
theorem errBound_nonneg (ρ : ℕ → FP32) (e : Expr) : 0 ≤ errBound e ρ := by
  induction e with
  | inp i => simp [errBound]
  | const c => simp [errBound]
  | add a b iha ihb =>
    simp only [errBound]
    have := eps_nonneg ((evalFP32 a ρ).val + (evalFP32 b ρ).val); linarith
  | sub a b iha ihb =>
    simp only [errBound]
    have := eps_nonneg ((evalFP32 a ρ).val - (evalFP32 b ρ).val); linarith
  | mul a b iha ihb =>
    simp only [errBound]
    have h1 : 0 ≤ |(evalFP32 a ρ).val| * errBound b ρ := mul_nonneg (abs_nonneg _) ihb
    have h2 : 0 ≤ |evalExact b ρ| * errBound a ρ := mul_nonneg (abs_nonneg _) iha
    have h3 := eps_nonneg ((evalFP32 a ρ).val * (evalFP32 b ρ).val); linarith
  | div a b iha ihb =>
    simp only [errBound]
    have h1 : 0 ≤ errBound a ρ / |(evalFP32 b ρ).val| := div_nonneg iha (abs_nonneg _)
    have h2 : 0 ≤ |evalExact a ρ| * errBound b ρ / (|(evalFP32 b ρ).val| * |evalExact b ρ|) :=
      div_nonneg (mul_nonneg (abs_nonneg _) ihb) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have h3 := eps_nonneg ((evalFP32 a ρ).val / (evalFP32 b ρ).val); linarith

/-! ## The forward-error accumulation and the box-faithfulness capstone (A3′) -/

/-- The DAG is **regular** at inputs `ρ` when every division has a nonzero denominator — in *both*
the floating-point and the exact interpretation (`(evalFP32 b ρ).val ≠ 0` and `evalExact b ρ ≠ 0`).
This is the domain condition under which the quotient-rule error propagation of a `div` node is a
genuine bound (a division by zero has no first-order sensitivity). It is vacuously true on any
`div`-free DAG (`add`/`sub`/`mul` only), so the forward-error bound below is unconditional there. -/
def Regular : Expr → (ℕ → FP32) → Prop
  | .inp _,   _ => True
  | .const _, _ => True
  | .add a b, ρ => Regular a ρ ∧ Regular b ρ
  | .sub a b, ρ => Regular a ρ ∧ Regular b ρ
  | .mul a b, ρ => Regular a ρ ∧ Regular b ρ
  | .div a b, ρ => Regular a ρ ∧ Regular b ρ ∧ (evalFP32 b ρ).val ≠ 0 ∧ evalExact b ρ ≠ 0

/-- **Forward-error accumulation over the DAG.** For a `Regular` input assignment, the rounded
binary32 measurand differs from the exact `ℝ` one by at most the accumulated rounding budget
`errBound e ρ`. Proved by structural induction, composing the per-operation half-ulp bounds
`Fp32Grounding.{add32,sub32,mul32,div32}_within_half_ulp` (the *rounding* stage) with the triangle
inequality and the first-order *propagation* of operand errors at each node — the whole-evaluation
lift of the local half-ulp bound `Grid.abs_sub_gridRound_le` (A1's grid). At the *linear* nodes the
propagation is coefficient-one; at the *nonlinear* nodes it carries the magnitude factors of a GUM
sensitivity analysis (`|b|`, `1/|b|`, `|a|/|b|²`). -/
theorem dag_fp32_error_bound (ρ : ℕ → FP32) :
    ∀ e : Expr, Regular e ρ → |(evalFP32 e ρ).val - evalExact e ρ| ≤ errBound e ρ := by
  intro e
  induction e with
  | inp i => intro _; simp [evalFP32, evalExact, errBound]
  | const c => intro _; simp [evalFP32, evalExact, errBound]
  | add a b iha ihb =>
    intro hreg
    simp only [Regular] at hreg
    obtain ⟨ha, hb⟩ := hreg
    have iha' := iha ha; have ihb' := ihb hb
    simp only [evalFP32, evalExact, errBound]
    have hop := add32_within_half_ulp (evalFP32 a ρ) (evalFP32 b ρ)
    have htri := abs_sub_le ((evalFP32 a ρ + evalFP32 b ρ).val)
      ((evalFP32 a ρ).val + (evalFP32 b ρ).val) (evalExact a ρ + evalExact b ρ)
    have hsplit : |((evalFP32 a ρ).val + (evalFP32 b ρ).val) - (evalExact a ρ + evalExact b ρ)|
        ≤ |(evalFP32 a ρ).val - evalExact a ρ| + |(evalFP32 b ρ).val - evalExact b ρ| := by
      have hrw : ((evalFP32 a ρ).val + (evalFP32 b ρ).val) - (evalExact a ρ + evalExact b ρ)
          = ((evalFP32 a ρ).val - evalExact a ρ) + ((evalFP32 b ρ).val - evalExact b ρ) := by ring
      rw [hrw]; exact abs_add_le _ _
    linarith [hop, htri, hsplit, iha', ihb']
  | sub a b iha ihb =>
    intro hreg
    simp only [Regular] at hreg
    obtain ⟨ha, hb⟩ := hreg
    have iha' := iha ha; have ihb' := ihb hb
    simp only [evalFP32, evalExact, errBound]
    have hop := sub32_within_half_ulp (evalFP32 a ρ) (evalFP32 b ρ)
    have htri := abs_sub_le ((evalFP32 a ρ - evalFP32 b ρ).val)
      ((evalFP32 a ρ).val - (evalFP32 b ρ).val) (evalExact a ρ - evalExact b ρ)
    have hsplit : |((evalFP32 a ρ).val - (evalFP32 b ρ).val) - (evalExact a ρ - evalExact b ρ)|
        ≤ |(evalFP32 a ρ).val - evalExact a ρ| + |(evalFP32 b ρ).val - evalExact b ρ| := by
      have hrw : ((evalFP32 a ρ).val - (evalFP32 b ρ).val) - (evalExact a ρ - evalExact b ρ)
          = ((evalFP32 a ρ).val - evalExact a ρ) - ((evalFP32 b ρ).val - evalExact b ρ) := by ring
      rw [hrw]; exact abs_sub_bound _ _
    linarith [hop, htri, hsplit, iha', ihb']
  | mul a b iha ihb =>
    intro hreg
    simp only [Regular] at hreg
    obtain ⟨ha, hb⟩ := hreg
    have iha' := iha ha; have ihb' := ihb hb
    simp only [evalFP32, evalExact, errBound]
    have hop := mul32_within_half_ulp (evalFP32 a ρ) (evalFP32 b ρ)
    -- First-order propagation: ãb̃ − âb̂ = ã·(b̃−b̂) + b̂·(ã−â).
    have hprop : |(evalFP32 a ρ).val * (evalFP32 b ρ).val - evalExact a ρ * evalExact b ρ|
        ≤ |(evalFP32 a ρ).val| * |(evalFP32 b ρ).val - evalExact b ρ|
          + |evalExact b ρ| * |(evalFP32 a ρ).val - evalExact a ρ| := by
      have hrw : (evalFP32 a ρ).val * (evalFP32 b ρ).val - evalExact a ρ * evalExact b ρ
          = (evalFP32 a ρ).val * ((evalFP32 b ρ).val - evalExact b ρ)
            + evalExact b ρ * ((evalFP32 a ρ).val - evalExact a ρ) := by ring
      rw [hrw]
      calc |(evalFP32 a ρ).val * ((evalFP32 b ρ).val - evalExact b ρ)
              + evalExact b ρ * ((evalFP32 a ρ).val - evalExact a ρ)|
          ≤ |(evalFP32 a ρ).val * ((evalFP32 b ρ).val - evalExact b ρ)|
            + |evalExact b ρ * ((evalFP32 a ρ).val - evalExact a ρ)| := abs_add_le _ _
        _ = |(evalFP32 a ρ).val| * |(evalFP32 b ρ).val - evalExact b ρ|
            + |evalExact b ρ| * |(evalFP32 a ρ).val - evalExact a ρ| := by rw [abs_mul, abs_mul]
    have hm1 : |(evalFP32 a ρ).val| * |(evalFP32 b ρ).val - evalExact b ρ|
        ≤ |(evalFP32 a ρ).val| * errBound b ρ := mul_le_mul_of_nonneg_left ihb' (abs_nonneg _)
    have hm2 : |evalExact b ρ| * |(evalFP32 a ρ).val - evalExact a ρ|
        ≤ |evalExact b ρ| * errBound a ρ := mul_le_mul_of_nonneg_left iha' (abs_nonneg _)
    have htri := abs_sub_le ((evalFP32 a ρ * evalFP32 b ρ).val)
      ((evalFP32 a ρ).val * (evalFP32 b ρ).val) (evalExact a ρ * evalExact b ρ)
    linarith [hop, hprop, hm1, hm2, htri]
  | div a b iha ihb =>
    intro hreg
    simp only [Regular] at hreg
    obtain ⟨ha, hb, hbfp, hbex⟩ := hreg
    have iha' := iha ha; have ihb' := ihb hb
    simp only [evalFP32, evalExact, errBound]
    have hop := div32_within_half_ulp (evalFP32 a ρ) (evalFP32 b ρ)
    -- First-order propagation of a quotient (nonzero denominators):
    -- ã/b̃ − â/b̂ = (ã−â)/b̃ − â·(b̃−b̂)/(b̃·b̂).
    have hid : (evalFP32 a ρ).val / (evalFP32 b ρ).val - evalExact a ρ / evalExact b ρ
        = ((evalFP32 a ρ).val - evalExact a ρ) / (evalFP32 b ρ).val
          - evalExact a ρ * ((evalFP32 b ρ).val - evalExact b ρ)
            / ((evalFP32 b ρ).val * evalExact b ρ) := by
      field_simp
      ring
    have hprop : |(evalFP32 a ρ).val / (evalFP32 b ρ).val - evalExact a ρ / evalExact b ρ|
        ≤ |(evalFP32 a ρ).val - evalExact a ρ| / |(evalFP32 b ρ).val|
          + |evalExact a ρ| * |(evalFP32 b ρ).val - evalExact b ρ|
            / (|(evalFP32 b ρ).val| * |evalExact b ρ|) := by
      rw [hid]
      calc |((evalFP32 a ρ).val - evalExact a ρ) / (evalFP32 b ρ).val
              - evalExact a ρ * ((evalFP32 b ρ).val - evalExact b ρ)
                / ((evalFP32 b ρ).val * evalExact b ρ)|
          ≤ |((evalFP32 a ρ).val - evalExact a ρ) / (evalFP32 b ρ).val|
            + |evalExact a ρ * ((evalFP32 b ρ).val - evalExact b ρ)
                / ((evalFP32 b ρ).val * evalExact b ρ)| := abs_sub_bound _ _
        _ = |(evalFP32 a ρ).val - evalExact a ρ| / |(evalFP32 b ρ).val|
            + |evalExact a ρ| * |(evalFP32 b ρ).val - evalExact b ρ|
              / (|(evalFP32 b ρ).val| * |evalExact b ρ|) := by
          simp only [abs_div, abs_mul]
    have hm1 : |(evalFP32 a ρ).val - evalExact a ρ| / |(evalFP32 b ρ).val|
        ≤ errBound a ρ / |(evalFP32 b ρ).val| := by gcongr
    have hm2 : |evalExact a ρ| * |(evalFP32 b ρ).val - evalExact b ρ|
          / (|(evalFP32 b ρ).val| * |evalExact b ρ|)
        ≤ |evalExact a ρ| * errBound b ρ / (|(evalFP32 b ρ).val| * |evalExact b ρ|) := by gcongr
    have htri := abs_sub_le ((evalFP32 a ρ / evalFP32 b ρ).val)
      ((evalFP32 a ρ).val / (evalFP32 b ρ).val) (evalExact a ρ / evalExact b ρ)
    linarith [hop, hprop, hm1, hm2, htri]

/-- **A3′ — box faithfulness of the floating-point measurand.** For a fixed model DAG `e`, a nominal
input `ρ`, and *any* input `σ` (in particular every input in a box around `ρ`), the floating-point
output *variation* `evalFP32 σ − evalFP32 ρ` reproduces the exact `ℝ` output variation
`evalExact σ − evalExact ρ` up to the summed rounding budget `errBound σ + errBound ρ`. So the FP32
measurand's uncertainty — its spread over the input box — equals the `ℝ` one **up to a proven,
DAG-additive bound**: the universal (whole-evaluation) lift of the per-site verdict A3. -/
theorem dag_fp32_box_faithful (e : Expr) (ρ σ : ℕ → FP32)
    (hρ : Regular e ρ) (hσ : Regular e σ) :
    |((evalFP32 e σ).val - (evalFP32 e ρ).val) - (evalExact e σ - evalExact e ρ)|
      ≤ errBound e σ + errBound e ρ := by
  have hσ' := dag_fp32_error_bound σ e hσ
  have hρ' := dag_fp32_error_bound ρ e hρ
  have hrw : ((evalFP32 e σ).val - (evalFP32 e ρ).val) - (evalExact e σ - evalExact e ρ)
      = ((evalFP32 e σ).val - evalExact e σ) - ((evalFP32 e ρ).val - evalExact e ρ) := by ring
  rw [hrw]
  have h := abs_sub_bound ((evalFP32 e σ).val - evalExact e σ) ((evalFP32 e ρ).val - evalExact e ρ)
  linarith [h, hσ', hρ']

/-! ## The flag-free regime — no rounding, hence exact box faithfulness -/

/-- The DAG is **flag-free** at inputs `ρ` when *no node rounds*: every `add`/`sub` is exact
(`(a + b).val = a.val + b.val`). This is the whole-evaluation *no flagged site* condition — no
absorption at any addition, and every subtraction in the exact (Sterbenz, A2) regime. -/
def FlagFree : Expr → (ℕ → FP32) → Prop
  | .inp _,   _ => True
  | .const _, _ => True
  | .add a b, ρ => FlagFree a ρ ∧ FlagFree b ρ ∧
      (evalFP32 a ρ + evalFP32 b ρ).val = (evalFP32 a ρ).val + (evalFP32 b ρ).val
  | .sub a b, ρ => FlagFree a ρ ∧ FlagFree b ρ ∧
      (evalFP32 a ρ - evalFP32 b ρ).val = (evalFP32 a ρ).val - (evalFP32 b ρ).val
  | .mul a b, ρ => FlagFree a ρ ∧ FlagFree b ρ ∧
      (evalFP32 a ρ * evalFP32 b ρ).val = (evalFP32 a ρ).val * (evalFP32 b ρ).val
  | .div a b, ρ => FlagFree a ρ ∧ FlagFree b ρ ∧
      (evalFP32 a ρ / evalFP32 b ρ).val = (evalFP32 a ρ).val / (evalFP32 b ρ).val

/-- **Under flag-freedom the floating-point measurand is exact.** If no node rounds, the binary32
evaluation coincides with the exact `ℝ` evaluation. Proved by induction, discharging each node with
its (hypothesised) exactness and the inductive exactness of the operands. -/
theorem evalFP32_val_eq_exact_of_flagFree (ρ : ℕ → FP32) :
    ∀ e : Expr, FlagFree e ρ → (evalFP32 e ρ).val = evalExact e ρ := by
  intro e
  induction e with
  | inp i => intro _; rfl
  | const c => intro _; rfl
  | add a b iha ihb =>
    intro h
    simp only [FlagFree] at h
    obtain ⟨ha, hb, hexact⟩ := h
    simp only [evalFP32, evalExact]
    rw [hexact, iha ha, ihb hb]
  | sub a b iha ihb =>
    intro h
    simp only [FlagFree] at h
    obtain ⟨ha, hb, hexact⟩ := h
    simp only [evalFP32, evalExact]
    rw [hexact, iha ha, ihb hb]
  | mul a b iha ihb =>
    intro h
    simp only [FlagFree] at h
    obtain ⟨ha, hb, hexact⟩ := h
    simp only [evalFP32, evalExact]
    rw [hexact, iha ha, ihb hb]
  | div a b iha ihb =>
    intro h
    simp only [FlagFree] at h
    obtain ⟨ha, hb, hexact⟩ := h
    simp only [evalFP32, evalExact]
    rw [hexact, iha ha, ihb hb]

/-- **A3′, flag-free case — exact box faithfulness.** When the DAG is flag-free at *both* `ρ` and
`σ` (no rounding, hence no absorption, anywhere in the evaluation), the bound of
`dag_fp32_box_faithful` collapses to **equality**: the FP32 measurand's uncertainty over the box is
*exactly* the `ℝ` one, for every input in the box. Rounding — the flagged sites — is the sole source
of the FP32/`ℝ` measurand gap, which is exactly the adequacy guarantee. -/
theorem dag_fp32_box_exact_of_flagFree (e : Expr) (ρ σ : ℕ → FP32)
    (hρ : FlagFree e ρ) (hσ : FlagFree e σ) :
    (evalFP32 e σ).val - (evalFP32 e ρ).val = evalExact e σ - evalExact e ρ := by
  rw [evalFP32_val_eq_exact_of_flagFree σ e hσ, evalFP32_val_eq_exact_of_flagFree ρ e hρ]

/-! ## The same regime, stated where it can be checked

`FlagFree` is a hypothesis about the *floating-point* evaluation: it says each node's rounded
operation happens to return its own operands' exact combination. A reader holding a model and a set
of inputs cannot check that without evaluating in binary32 first, and it names the intermediates
`evalFP32` produces rather than anything about the model.

`ExactRepresentable` says the same thing about the *exact* evaluation: at every node, the exact
result of that node is a binary32 number. That is checkable from the `ℝ` model and the inputs alone,
and `flagFree_iff_exactRepresentable` proves the two conditions are the *same set of inputs* — so it
is not merely a sufficient condition that happens to be convenient, it is `FlagFree` itself,
relocated. Minimality follows: `round32` fixes exactly the representable reals
(`round32_eq_self_iff`), so no weaker condition on a node's exact value keeps that node from
rounding. -/

/-- **Flag-freedom, read off the exact evaluation.** At every node the exact result lands on the
binary32 grid. Equivalent to `FlagFree` (`flagFree_iff_exactRepresentable`) and stated without
reference to any floating-point intermediate. -/
def ExactRepresentable : Expr → (ℕ → FP32) → Prop
  | .inp _,   _ => True
  | .const _, _ => True
  | .add a b, ρ => ExactRepresentable a ρ ∧ ExactRepresentable b ρ ∧
      genericFormat binaryRadix fexp32 (evalExact a ρ + evalExact b ρ)
  | .sub a b, ρ => ExactRepresentable a ρ ∧ ExactRepresentable b ρ ∧
      genericFormat binaryRadix fexp32 (evalExact a ρ - evalExact b ρ)
  | .mul a b, ρ => ExactRepresentable a ρ ∧ ExactRepresentable b ρ ∧
      genericFormat binaryRadix fexp32 (evalExact a ρ * evalExact b ρ)
  | .div a b, ρ => ExactRepresentable a ρ ∧ ExactRepresentable b ρ ∧
      genericFormat binaryRadix fexp32 (evalExact a ρ / evalExact b ρ)

/-- **The two conditions cut out the same inputs.** Each direction needs the other condition on the
operands first — which is what the induction supplies — because the node's own statement is about
the operands' *values*, and it is exactly the operand-level equality that identifies the two
readings of them. -/
theorem flagFree_iff_exactRepresentable (ρ : ℕ → FP32) :
    ∀ e : Expr, FlagFree e ρ ↔ ExactRepresentable e ρ := by
  intro e
  induction e with
  | inp i => exact Iff.rfl
  | const c => exact Iff.rfl
  | add a b iha ihb =>
    constructor
    · rintro ⟨ha, hb, hex⟩
      refine ⟨iha.mp ha, ihb.mp hb, ?_⟩
      rw [← evalFP32_val_eq_exact_of_flagFree ρ a ha, ← evalFP32_val_eq_exact_of_flagFree ρ b hb]
      exact (round32_eq_self_iff _).mp hex
    · rintro ⟨ha, hb, hg⟩
      have ha' := iha.mpr ha
      have hb' := ihb.mpr hb
      refine ⟨ha', hb', ?_⟩
      show round32 ((evalFP32 a ρ).val + (evalFP32 b ρ).val)
          = (evalFP32 a ρ).val + (evalFP32 b ρ).val
      rw [evalFP32_val_eq_exact_of_flagFree ρ a ha', evalFP32_val_eq_exact_of_flagFree ρ b hb']
      exact round32_fix hg
  | sub a b iha ihb =>
    constructor
    · rintro ⟨ha, hb, hex⟩
      refine ⟨iha.mp ha, ihb.mp hb, ?_⟩
      rw [← evalFP32_val_eq_exact_of_flagFree ρ a ha, ← evalFP32_val_eq_exact_of_flagFree ρ b hb]
      exact (round32_eq_self_iff _).mp hex
    · rintro ⟨ha, hb, hg⟩
      have ha' := iha.mpr ha
      have hb' := ihb.mpr hb
      refine ⟨ha', hb', ?_⟩
      show round32 ((evalFP32 a ρ).val - (evalFP32 b ρ).val)
          = (evalFP32 a ρ).val - (evalFP32 b ρ).val
      rw [evalFP32_val_eq_exact_of_flagFree ρ a ha', evalFP32_val_eq_exact_of_flagFree ρ b hb']
      exact round32_fix hg
  | mul a b iha ihb =>
    constructor
    · rintro ⟨ha, hb, hex⟩
      refine ⟨iha.mp ha, ihb.mp hb, ?_⟩
      rw [← evalFP32_val_eq_exact_of_flagFree ρ a ha, ← evalFP32_val_eq_exact_of_flagFree ρ b hb]
      exact (round32_eq_self_iff _).mp hex
    · rintro ⟨ha, hb, hg⟩
      have ha' := iha.mpr ha
      have hb' := ihb.mpr hb
      refine ⟨ha', hb', ?_⟩
      show round32 ((evalFP32 a ρ).val * (evalFP32 b ρ).val)
          = (evalFP32 a ρ).val * (evalFP32 b ρ).val
      rw [evalFP32_val_eq_exact_of_flagFree ρ a ha', evalFP32_val_eq_exact_of_flagFree ρ b hb']
      exact round32_fix hg
  | div a b iha ihb =>
    constructor
    · rintro ⟨ha, hb, hex⟩
      refine ⟨iha.mp ha, ihb.mp hb, ?_⟩
      rw [← evalFP32_val_eq_exact_of_flagFree ρ a ha, ← evalFP32_val_eq_exact_of_flagFree ρ b hb]
      exact (round32_eq_self_iff _).mp hex
    · rintro ⟨ha, hb, hg⟩
      have ha' := iha.mpr ha
      have hb' := ihb.mpr hb
      refine ⟨ha', hb', ?_⟩
      show round32 ((evalFP32 a ρ).val / (evalFP32 b ρ).val)
          = (evalFP32 a ρ).val / (evalFP32 b ρ).val
      rw [evalFP32_val_eq_exact_of_flagFree ρ a ha', evalFP32_val_eq_exact_of_flagFree ρ b hb']
      exact round32_fix hg

/-- **The FP32 measurand is exact when every node's exact value is representable.** The checkable
form of `evalFP32_val_eq_exact_of_flagFree`. -/
theorem evalFP32_val_eq_exact_of_exactRepresentable (ρ : ℕ → FP32) (e : Expr)
    (h : ExactRepresentable e ρ) : (evalFP32 e ρ).val = evalExact e ρ :=
  evalFP32_val_eq_exact_of_flagFree ρ e ((flagFree_iff_exactRepresentable ρ e).mpr h)

/-- **A3′, exact-representable case.** `dag_fp32_box_exact_of_flagFree` under the checkable
hypothesis: if every node's exact value is a binary32 number at both inputs, the FP32 measurand's
variation over the box is *exactly* the `ℝ` one. -/
theorem dag_fp32_box_exact_of_exactRepresentable (e : Expr) (ρ σ : ℕ → FP32)
    (hρ : ExactRepresentable e ρ) (hσ : ExactRepresentable e σ) :
    (evalFP32 e σ).val - (evalFP32 e ρ).val = evalExact e σ - evalExact e ρ :=
  dag_fp32_box_exact_of_flagFree e ρ σ
    ((flagFree_iff_exactRepresentable ρ e).mpr hρ)
    ((flagFree_iff_exactRepresentable σ e).mpr hσ)

end PropertyKindCalculus.Uncertainty.Adequacy
