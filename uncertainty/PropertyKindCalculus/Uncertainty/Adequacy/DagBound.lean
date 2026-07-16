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
    (`(a + b).val = round₃₂ (a.val + b.val)`);
  * `evalExact e ρ` — the exact `ℝ` measurand (no rounding), the reference.

Composing the *per-operation* rounding bounds `Fp32Grounding.{add32,sub32}_within_half_ulp` (the
genuine, Flocq-backed `FP32.{add,sub}_abs_error`) along the DAG yields:

  * **`dag_fp32_error_bound`** — the forward-error accumulation: the FP32 measurand differs from the
    `ℝ` one by at most `errBound e ρ`, the tree-sum of the per-node half-ulps `eps₃₂`.
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

Restriction (honest scope, `UNCERTAINTY.md` §6). The DAG covers `+`/`−` — the operations A1/A2/A3
cover and the carrier flags. Multiplication/division rounding (their per-op bounds
`FP32.{mul,div}_abs_error` exist in `Fp32Grounding`) accumulate the same way but with
magnitude-dependent factors; extending the box theorem to them, and refining `FlagFree` to the
*minimal* no-absorption condition (rounding allowed as long as the tracked contribution survives),
are the remaining refinements. Proved over `ℝ`/`FP32`, sorry-free
(`[propext, Classical.choice, Quot.sound]`).
-/
import PropertyKindCalculus.Uncertainty.Adequacy.Fp32Grounding

namespace PropertyKindCalculus.Uncertainty.Adequacy

open TorchLean.Floats

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

/-- **The rounded (binary32) measurand.** Every `add`/`sub` node rounds its result to the binary32
grid: `(a + b).val = round₃₂ (a.val + b.val)` (TorchLean's `FP32` `Add`/`Sub`). This is the
floating-point evaluation a science model actually runs. -/
noncomputable def evalFP32 : Expr → (ℕ → FP32) → FP32
  | .inp i,   ρ => ρ i
  | .const c, _ => c
  | .add a b, ρ => evalFP32 a ρ + evalFP32 b ρ
  | .sub a b, ρ => evalFP32 a ρ - evalFP32 b ρ

/-- **The exact `ℝ` measurand.** The same DAG evaluated with *no rounding* over the reals — the
reference against which the floating-point evaluation's information loss is measured. -/
noncomputable def evalExact : Expr → (ℕ → FP32) → ℝ
  | .inp i,   ρ => (ρ i).val
  | .const c, _ => c.val
  | .add a b, ρ => evalExact a ρ + evalExact b ρ
  | .sub a b, ρ => evalExact a ρ - evalExact b ρ

/-- **The accumulated rounding budget** of the DAG: the tree-sum of the per-node half-ulps `eps₃₂`
at each rounded (`add`/`sub`) node's exact operand sum. This is the total forward error the
floating-point evaluation can introduce, composed from the per-operation bounds
`Fp32Grounding.{add32,sub32}_within_half_ulp`. -/
noncomputable def errBound : Expr → (ℕ → FP32) → ℝ
  | .inp _,   _ => 0
  | .const _, _ => 0
  | .add a b, ρ => errBound a ρ + errBound b ρ + eps₃₂ ((evalFP32 a ρ).val + (evalFP32 b ρ).val)
  | .sub a b, ρ => errBound a ρ + errBound b ρ + eps₃₂ ((evalFP32 a ρ).val - (evalFP32 b ρ).val)

/-- `|x − y| ≤ |x| + |y|`, the triangle bound used to split a difference of errors. -/
private theorem abs_sub_bound (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [sub_eq_add_neg, ← abs_neg y]; exact abs_add_le x (-y)

/-- Half a ulp is nonnegative — immediate from the rounding bound `round32_within_half_ulp`. -/
private theorem eps_nonneg (x : ℝ) : 0 ≤ eps₃₂ x :=
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

/-! ## The forward-error accumulation and the box-faithfulness capstone (A3′) -/

/-- **Forward-error accumulation over the DAG.** The rounded binary32 measurand differs from the
exact `ℝ` one by at most the accumulated rounding budget `errBound e ρ`. Proved by structural
induction, composing the per-operation half-ulp bounds `Fp32Grounding.{add32,sub32}_within_half_ulp`
with the triangle inequality at each node — the whole-evaluation lift of the local half-ulp bound
`Grid.abs_sub_gridRound_le` (A1's grid). -/
theorem dag_fp32_error_bound (ρ : ℕ → FP32) (e : Expr) :
    |(evalFP32 e ρ).val - evalExact e ρ| ≤ errBound e ρ := by
  induction e with
  | inp i => simp [evalFP32, evalExact, errBound]
  | const c => simp [evalFP32, evalExact, errBound]
  | add a b iha ihb =>
    simp only [evalFP32, evalExact, errBound]
    have hop := add32_within_half_ulp (evalFP32 a ρ) (evalFP32 b ρ)
    have htri := abs_sub_le ((evalFP32 a ρ + evalFP32 b ρ).val)
      ((evalFP32 a ρ).val + (evalFP32 b ρ).val) (evalExact a ρ + evalExact b ρ)
    have hsplit : |((evalFP32 a ρ).val + (evalFP32 b ρ).val) - (evalExact a ρ + evalExact b ρ)|
        ≤ |(evalFP32 a ρ).val - evalExact a ρ| + |(evalFP32 b ρ).val - evalExact b ρ| := by
      have hrw : ((evalFP32 a ρ).val + (evalFP32 b ρ).val) - (evalExact a ρ + evalExact b ρ)
          = ((evalFP32 a ρ).val - evalExact a ρ) + ((evalFP32 b ρ).val - evalExact b ρ) := by ring
      rw [hrw]; exact abs_add_le _ _
    linarith [hop, htri, hsplit, iha, ihb]
  | sub a b iha ihb =>
    simp only [evalFP32, evalExact, errBound]
    have hop := sub32_within_half_ulp (evalFP32 a ρ) (evalFP32 b ρ)
    have htri := abs_sub_le ((evalFP32 a ρ - evalFP32 b ρ).val)
      ((evalFP32 a ρ).val - (evalFP32 b ρ).val) (evalExact a ρ - evalExact b ρ)
    have hsplit : |((evalFP32 a ρ).val - (evalFP32 b ρ).val) - (evalExact a ρ - evalExact b ρ)|
        ≤ |(evalFP32 a ρ).val - evalExact a ρ| + |(evalFP32 b ρ).val - evalExact b ρ| := by
      have hrw : ((evalFP32 a ρ).val - (evalFP32 b ρ).val) - (evalExact a ρ - evalExact b ρ)
          = ((evalFP32 a ρ).val - evalExact a ρ) - ((evalFP32 b ρ).val - evalExact b ρ) := by ring
      rw [hrw]; exact abs_sub_bound _ _
    linarith [hop, htri, hsplit, iha, ihb]

/-- **A3′ — box faithfulness of the floating-point measurand.** For a fixed model DAG `e`, a nominal
input `ρ`, and *any* input `σ` (in particular every input in a box around `ρ`), the floating-point
output *variation* `evalFP32 σ − evalFP32 ρ` reproduces the exact `ℝ` output variation
`evalExact σ − evalExact ρ` up to the summed rounding budget `errBound σ + errBound ρ`. So the FP32
measurand's uncertainty — its spread over the input box — equals the `ℝ` one **up to a proven,
DAG-additive bound**: the universal (whole-evaluation) lift of the per-site verdict A3. -/
theorem dag_fp32_box_faithful (e : Expr) (ρ σ : ℕ → FP32) :
    |((evalFP32 e σ).val - (evalFP32 e ρ).val) - (evalExact e σ - evalExact e ρ)|
      ≤ errBound e σ + errBound e ρ := by
  have hσ := dag_fp32_error_bound σ e
  have hρ := dag_fp32_error_bound ρ e
  have hrw : ((evalFP32 e σ).val - (evalFP32 e ρ).val) - (evalExact e σ - evalExact e ρ)
      = ((evalFP32 e σ).val - evalExact e σ) - ((evalFP32 e ρ).val - evalExact e ρ) := by ring
  rw [hrw]
  have h := abs_sub_bound ((evalFP32 e σ).val - evalExact e σ) ((evalFP32 e ρ).val - evalExact e ρ)
  linarith [h, hσ, hρ]

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

/-- **A3′, flag-free case — exact box faithfulness.** When the DAG is flag-free at *both* `ρ` and
`σ` (no rounding, hence no absorption, anywhere in the evaluation), the bound of
`dag_fp32_box_faithful` collapses to **equality**: the FP32 measurand's uncertainty over the box is
*exactly* the `ℝ` one, for every input in the box. Rounding — the flagged sites — is the sole source
of the FP32/`ℝ` measurand gap, which is exactly the adequacy guarantee. -/
theorem dag_fp32_box_exact_of_flagFree (e : Expr) (ρ σ : ℕ → FP32)
    (hρ : FlagFree e ρ) (hσ : FlagFree e σ) :
    (evalFP32 e σ).val - (evalFP32 e ρ).val = evalExact e σ - evalExact e ρ := by
  rw [evalFP32_val_eq_exact_of_flagFree σ e hσ, evalFP32_val_eq_exact_of_flagFree ρ e hρ]

end PropertyKindCalculus.Uncertainty.Adequacy
