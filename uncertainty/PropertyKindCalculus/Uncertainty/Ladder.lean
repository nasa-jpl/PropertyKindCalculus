/-
`PropertyKindCalculus.Uncertainty.Ladder` — the GUM ⊂ Willink rungs of the nesting ladder,
stated and proved over Mathlib's `ℝ` (the proof carrier).

`UNCERTAINTY.md` §3.3 makes the "GUM ⊂ Willink ⊂ SSPRC" slogan concrete: each coarser method is
the projection of the finer one onto fewer cumulants, and the whole ladder rests on one fact —
**cumulant additivity under independent summation** (Willink 2005, eq. 3). This module delivers
the first two rungs as theorems:

  * **T1 — cumulant additivity.** The measurand's combined cumulants are the sum of the
    per-input contributions. Encoded as: `Cumulants` is a commutative monoid under `combine`,
    and `willinkCumulants` of a `cons` list splits as `termCumulants t + willinkCumulants ts`.
    *That the `combine` monoid law holds at all is the independence assumption made explicit.*

  * **T2 — `gum = willink|κ₄=0`.** The `κ₂`-projection of the Willink cumulant pair is exactly
    the GUM combined variance (`willinkCumulants_kappa2`); and when every input's fourth cumulant
    vanishes (all-Gaussian inputs), the Willink coefficient of excess is `0`, its Pearson coverage
    factor collapses to the Gaussian `z` (`k95 0 = 1.96`), and the Willink expanded-uncertainty
    half-width equals the GUM Gaussian half-width `1.96·u_c` (`gum_eq_willink_of_normal`).

These are the `ℝ` specifications; the executable `Float` counterparts (`gumStdUnc`,
`willinkCombine`, `willinkK95/99` in `Combine.lean`) are the same arithmetic on the rounding
carrier, and the `WillinkGaugeBlock` example reproduces Willink's Table 4 half-widths at `Float`.
Only the second/fourth cumulants (`κ₂`, `κ₄`) enter T1/T2; the third (asymmetry, Willink §5) is
carried by `MomentData` but not exercised until the asymmetric-input extension.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import PropertyKindCalculus.Uncertainty.InputDist

namespace PropertyKindCalculus.Uncertainty

/-! ## The output-cumulant contribution type and its `combine` monoid -/

/-- **The measurand's cumulant contribution** carried by the Willink rung: the second cumulant
`κ₂ = u_Y²` (variance) and the fourth cumulant `κ₄ = w_Y`. `combine` is componentwise addition
(below), a commutative monoid — and *that this is a monoid is precisely the independence
assumption* of `UNCERTAINTY.md` P3/§3.1. -/
@[ext]
structure Cumulants where
  /-- Second cumulant `κ₂ = u_Y²` (variance). -/
  kappa2 : ℝ
  /-- Fourth cumulant `κ₄ = w_Y`. -/
  kappa4 : ℝ

namespace Cumulants

instance : Add Cumulants := ⟨fun a b => ⟨a.kappa2 + b.kappa2, a.kappa4 + b.kappa4⟩⟩
instance : Zero Cumulants := ⟨⟨0, 0⟩⟩

@[simp] theorem add_kappa2 (a b : Cumulants) : (a + b).kappa2 = a.kappa2 + b.kappa2 := rfl
@[simp] theorem add_kappa4 (a b : Cumulants) : (a + b).kappa4 = a.kappa4 + b.kappa4 := rfl
@[simp] theorem zero_kappa2 : (0 : Cumulants).kappa2 = 0 := rfl
@[simp] theorem zero_kappa4 : (0 : Cumulants).kappa4 = 0 := rfl

/-- **`combine` is a commutative monoid** (P3): componentwise real addition, associative and
commutative with unit `0`. The three laws are exactly the plan's `combine_assoc`/`combine_comm`/
`empty_combine` obligations — the typed form of "the inputs combine independently". -/
instance : AddCommMonoid Cumulants where
  add := (· + ·)
  zero := 0
  add_assoc a b c := by ext <;> exact add_assoc _ _ _
  zero_add a := by ext <;> exact zero_add _
  add_zero a := by ext <;> exact add_zero _
  add_comm a b := by ext <;> exact add_comm _ _
  nsmul := nsmulRec

/-- The independence monoid law, named for §3.1. -/
theorem combine_comm (a b : Cumulants) : a + b = b + a := add_comm a b
/-- The independence monoid law, named for §3.1. -/
theorem combine_assoc (a b c : Cumulants) : a + b + c = a + (b + c) := add_assoc a b c
/-- The independence monoid law, named for §3.1. -/
theorem empty_combine (a : Cumulants) : 0 + a = a := zero_add a

end Cumulants

/-! ## Extraction and combination (the linearized `extract`/`combine`) -/

/-- The per-input Willink contribution `(cᵢ²·uᵢ², cᵢ⁴·wᵢ)` for a sensitivity coefficient
`cᵢ = t.1` and input moments `t.2`. This is the linearized `extract` step. -/
def termCumulants (t : ℝ × MomentData ℝ) : Cumulants :=
  { kappa2 := t.1 ^ 2 * t.2.variance, kappa4 := t.1 ^ 4 * t.2.fourthCumulant }

/-- **Willink combined cumulants** — the `combine`-fold of the per-input contributions. -/
def willinkCumulants (terms : List (ℝ × MomentData ℝ)) : Cumulants :=
  (terms.map termCumulants).sum

/-- **GUM combined variance** `u_c² = Σ cᵢ²·uᵢ²` — the second-cumulant-only combine. -/
def gumVariance (terms : List (ℝ × MomentData ℝ)) : ℝ :=
  (terms.map fun t => t.1 ^ 2 * t.2.variance).sum

/-! ## T1 — cumulant additivity (Willink eq. 3) -/

/-- **T1 (fold form).** Prepending an input adds its contribution: the combined cumulants of
`t :: ts` are `termCumulants t + willinkCumulants ts`. Independent contributions add — the
cumulant-additivity theorem, realized through the `Cumulants` monoid. -/
theorem willinkCumulants_cons (t : ℝ × MomentData ℝ) (ts : List (ℝ × MomentData ℝ)) :
    willinkCumulants (t :: ts) = termCumulants t + willinkCumulants ts := by
  simp [willinkCumulants, List.map_cons, List.sum_cons]

/-- **T1 (componentwise).** Each cumulant of a combined pair is the sum of the parts — the
`κ_r(a ⊕ b) = κ_r a + κ_r b` of Willink eq. 3, here for `r = 2` and `r = 4`. -/
theorem kappa_additive (a b : Cumulants) :
    (a + b).kappa2 = a.kappa2 + b.kappa2 ∧ (a + b).kappa4 = a.kappa4 + b.kappa4 :=
  ⟨rfl, rfl⟩

theorem gumVariance_cons (t : ℝ × MomentData ℝ) (ts : List (ℝ × MomentData ℝ)) :
    gumVariance (t :: ts) = t.1 ^ 2 * t.2.variance + gumVariance ts := by
  simp [gumVariance, List.map_cons, List.sum_cons]

/-! ## T2 — GUM is the `κ₂`-projection of Willink -/

/-- **T2 (variance agreement).** The second cumulant of the Willink combine is exactly the GUM
combined variance: `κ₂` is the projection that recovers GUM. Holds for *any* inputs. -/
theorem willinkCumulants_kappa2 :
    ∀ terms : List (ℝ × MomentData ℝ), (willinkCumulants terms).kappa2 = gumVariance terms
  | [] => by simp [willinkCumulants, gumVariance]
  | t :: ts => by
    rw [willinkCumulants_cons, Cumulants.add_kappa2, willinkCumulants_kappa2 ts,
      gumVariance_cons]
    rfl

/-- **T2 (shape collapse).** If every input's fourth cumulant vanishes (all-Gaussian inputs),
the combined fourth cumulant is `0`. -/
theorem willinkCumulants_kappa4_zero :
    ∀ (terms : List (ℝ × MomentData ℝ)), (∀ t ∈ terms, (t.2).fourthCumulant = 0) →
      (willinkCumulants terms).kappa4 = 0
  | [], _ => by simp [willinkCumulants]
  | t :: ts, h => by
    obtain ⟨hHead, hTail⟩ := List.forall_mem_cons.mp h
    rw [willinkCumulants_cons, Cumulants.add_kappa4, willinkCumulants_kappa4_zero ts hTail]
    have ht : (termCumulants t).kappa4 = 0 := by
      show t.1 ^ 4 * t.2.fourthCumulant = 0
      rw [hHead, mul_zero]
    rw [ht, add_zero]

/-! ## The Pearson coverage factors and the summarize collapse -/

/-- Coefficient of excess `γ_Y = w_Y / u_Y⁴ = κ₄ / κ₂²`. -/
noncomputable def excess (c : Cumulants) : ℝ := c.kappa4 / c.kappa2 ^ 2

/-- Willink eq. (6): the 95% Pearson coverage factor `k₀.₉₅(γ)`. -/
noncomputable def k95 (g : ℝ) : ℝ :=
  (1.96 + 1.845 * g + 0.47 * g ^ 2) / (1 + 0.906 * g + 0.239 * g ^ 2)

/-- Willink eq. (7): the 99% Pearson coverage factor `k₀.₉₉(γ)`. -/
noncomputable def k99 (g : ℝ) : ℝ :=
  (2.5758 + 2.6736 * g + 0.7685 * g ^ 2) / (1 + 0.8864 * g + 0.2362 * g ^ 2)

/-- **The excess range Willink's rational fits are stated on.** `k95` and `k99` are fits to
the Pearson-family percentage points, valid for `-1.2 ≤ γ ≤ 6`; outside that range the
expression still evaluates and is no longer a coverage factor. The executable side
(`Combine.inPearsonFitDomain`) carries the same two bounds and returns `none` outside them,
so what the specification calls the domain and what the report refuses are one thing. -/
def PearsonFitDomain (g : ℝ) : Prop := -1.2 ≤ g ∧ g ≤ 6

/-- **The Gaussian case is interior to the fit's range**, so T2's collapse — which is stated
at `γ = 0` — never reads the fit outside where it is stated. -/
theorem zero_mem_pearsonFitDomain : PearsonFitDomain 0 := by
  constructor <;> norm_num

/-- When `κ₄ = 0` the coefficient of excess is `0` (the Gaussian shape). -/
theorem excess_of_kappa4_zero {c : Cumulants} (h : c.kappa4 = 0) : excess c = 0 := by
  simp [excess, h]

/-- At zero excess the 95% Pearson factor is the Gaussian `z₀.₉₇₅ = 1.96`. -/
@[simp] theorem k95_zero : k95 0 = 1.96 := by norm_num [k95]

/-- At zero excess the 99% Pearson factor is the Gaussian `z₀.₉₉₅ = 2.5758`. -/
@[simp] theorem k99_zero : k99 0 = 2.5758 := by norm_num [k99]

/-! ## T2 capstone — the Willink interval collapses to the GUM interval -/

/-- The GUM 95% expanded-uncertainty half-width `U₀.₉₅ = 1.96 · u_c`. -/
noncomputable def gumHalf95 (terms : List (ℝ × MomentData ℝ)) : ℝ :=
  1.96 * Real.sqrt (gumVariance terms)

/-- The Willink 95% expanded-uncertainty half-width `k₀.₉₅(γ_Y) · u_Y`. -/
noncomputable def willinkHalf95 (terms : List (ℝ × MomentData ℝ)) : ℝ :=
  k95 (excess (willinkCumulants terms)) * Real.sqrt (willinkCumulants terms).kappa2

/-- **T2 — GUM = Willink at κ₄ = 0.** For all-Gaussian inputs the Willink cumulants method's
95% expanded-uncertainty half-width equals the GUM Gaussian half-width. The finer method's
extra structure (the fourth cumulant, the Pearson closure) contributes nothing precisely when
the coarser method's Gaussian assumption already holds — so `gum` is the faithful `κ₄ = 0`
restriction of `willink`, not a different answer. -/
theorem gum_eq_willink_of_normal (terms : List (ℝ × MomentData ℝ))
    (h : ∀ t ∈ terms, (t.2).fourthCumulant = 0) :
    willinkHalf95 terms = gumHalf95 terms := by
  rw [willinkHalf95, gumHalf95, willinkCumulants_kappa2,
    excess_of_kappa4_zero (willinkCumulants_kappa4_zero terms h), k95_zero]

end PropertyKindCalculus.Uncertainty
