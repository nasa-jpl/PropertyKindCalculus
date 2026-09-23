/-
`PropertyKindCalculus.Uncertainty.Convolution` — the SSPRC rigor spine over Mathlib's `ℝ`:
discrete deviation distributions, their **convolution**, and the theorems that make
`GUM ⊂ Willink ⊂ SSPRC` a chain of homomorphisms (`UNCERTAINTY.md` §3.3, Stage 2).

The SSPRC method (Degenhardt 2025) propagates each input's uncertainty *separately* into a
per-input **deviation distribution** and combines them by **convolution** — the distribution of a
sum of independent contributions. This module models a deviation distribution as a finite discrete
distribution (`Dist = List (ℝ × ℝ)`, value/weight pairs) and proves the three ladder theorems the
plan owes:

  * **T5 — convolution ↔ cumulant addition.** For centered probability distributions the second and
    fourth cumulants are *additive under convolution*: `κ₂(d₁ ⋆ d₂) = κ₂ d₁ + κ₂ d₂` and
    `κ₄(d₁ ⋆ d₂) = κ₄ d₁ + κ₄ d₂` (`kappa2_conv`, `kappa4_conv`). This is the genuine mathematical
    content — convolution is defined as the distribution of the sum (`conv`, all pairwise sums with
    product weights), *not* as cumulant addition; the additivity is *proved* from the independence
    factorization of the joint expectation. Packaged as the monoid homomorphism
    `cumulantsOf_conv : cumulantsOf (d₁ ⋆ d₂) = cumulantsOf d₁ + cumulantsOf d₂` onto the `Ladder`
    `Cumulants` monoid.

  * **T3 — Willink is the fourth-cumulant truncation of the linearized SSPRC.** For a *linear* model
    the per-input deviation is `cᵢ·Zᵢ`; convolving them and reading off `(κ₂, κ₄)` yields exactly the
    Willink combined cumulants `(Σcᵢ²uᵢ², Σcᵢ⁴wᵢ)` (`cumulantsOf_combinedDeviation`). So `willink` is
    the `(κ₂,κ₄)`-projection of the (linearized) `ssprc` — the lower edge of the ladder, whose top
    edge (`gum = willink|κ₄=0`) is T2 in `Ladder`.

  * **T4 — the SSPRC reference equals the mean for an affine model.** The combined deviation's mean
    is `Σ cᵢ·E(Zᵢ)` (`mean_combinedDeviation`); for a linear model (centered inputs) it is `0`, so the
    reference value `R = f(E(X))` equals `E(Y)` (`combinedDeviation_isCentered`). The nonlinearity
    signature `E(Y) − R` is exactly the non-vanishing of that sum when a deviation is *not* centered —
    the very gap the Degenhardt fictive example exhibits and the linearized rungs miss.

All proved over `ℝ`, sorry-free. The executable `Float` SSPRC pipeline (`Ssprc.lean`) realizes the
*same* convolution on concrete samples; this module is its specification. Mathlib-backed (imports
`Ladder`, hence `ℝ` and the `Cumulants` monoid).
-/

module

public import PropertyKindCalculus.Uncertainty.Ladder

@[expose] public section Blanket

namespace PropertyKindCalculus.Uncertainty

/-! ## Discrete distributions and their weighted expectation -/

/-- A finite **discrete distribution** over `ℝ`: a list of `(value, weight)` pairs. A deviation
distribution reconstructed by SSPRC from systematic samples is exactly this shape. -/
abbrev Dist := List (ℝ × ℝ)

namespace Dist

/-- Total weight `Σ wᵢ`. A *probability* distribution has total `1`. -/
def total (d : Dist) : ℝ := (d.map Prod.snd).sum

/-- **Weighted expectation** `E[g(X)] = Σ wᵢ · g(xᵢ)`. Every moment below is an instance. -/
def expect (d : Dist) (g : ℝ → ℝ) : ℝ := (d.map (fun p => p.2 * g p.1)).sum

/-- Raw moment `E[Xᵏ] = Σ wᵢ · xᵢᵏ`. -/
def rawMoment (d : Dist) (k : ℕ) : ℝ := d.expect (fun x => x ^ k)

/-- Mean `E[X] = Σ wᵢ · xᵢ`. -/
def mean (d : Dist) : ℝ := d.expect (fun x => x)

/-- The distribution is **normalized** (a probability distribution): total weight `1`. -/
def IsProb (d : Dist) : Prop := d.total = 1

/-- The distribution is **centered**: mean `0`. SSPRC deviation distributions of a *linear* model
are centered; the non-linearity signature is exactly a non-zero mean. -/
def IsCentered (d : Dist) : Prop := d.mean = 0

/-- The **second cumulant** `κ₂`. For a centered probability distribution this is the variance
`E[X²]` (the general `E[X²] − E[X]²` collapses to `E[X²]` at mean `0`). -/
def kappa2 (d : Dist) : ℝ := d.rawMoment 2

/-- The **fourth cumulant** `κ₄ = E[X⁴] − 3·E[X²]²`. For a centered probability distribution this is
the standard fourth cumulant; `0` for a Gaussian. -/
def kappa4 (d : Dist) : ℝ := d.rawMoment 4 - 3 * (d.rawMoment 2) ^ 2

/-! ### Linearity of `expect` and `total` -/

@[simp] theorem total_nil : total [] = 0 := rfl
@[simp] theorem total_cons (p : ℝ × ℝ) (d : Dist) : total (p :: d) = p.2 + total d := by
  simp [total]

@[simp] theorem expect_nil (g : ℝ → ℝ) : expect [] g = 0 := rfl
@[simp] theorem expect_cons (p : ℝ × ℝ) (d : Dist) (g : ℝ → ℝ) :
    expect (p :: d) g = p.2 * g p.1 + expect d g := by
  simp [expect]

@[simp] theorem mean_cons (p : ℝ × ℝ) (d : Dist) : mean (p :: d) = p.2 * p.1 + mean d := by
  simp [mean]

@[simp] theorem rawMoment_cons (p : ℝ × ℝ) (d : Dist) (k : ℕ) :
    rawMoment (p :: d) k = p.2 * p.1 ^ k + rawMoment d k := by
  simp [rawMoment]

theorem total_eq_expect_one (d : Dist) : d.total = d.expect (fun _ => 1) := by
  induction d with
  | nil => simp
  | cons p d ih => simp [ih]

theorem expect_add (d : Dist) (g h : ℝ → ℝ) :
    d.expect (fun x => g x + h x) = d.expect g + d.expect h := by
  induction d with
  | nil => simp
  | cons p d ih => simp only [expect_cons, ih]; ring

theorem expect_const_mul (c : ℝ) (d : Dist) (g : ℝ → ℝ) :
    d.expect (fun x => c * g x) = c * d.expect g := by
  induction d with
  | nil => simp
  | cons p d ih => simp only [expect_cons, ih]; ring

theorem expect_const (d : Dist) (c : ℝ) : d.expect (fun _ => c) = d.total * c := by
  induction d with
  | nil => simp
  | cons p d ih => simp only [expect_cons, total_cons, ih]; ring

theorem expect_append (d1 d2 : Dist) (g : ℝ → ℝ) :
    (d1 ++ d2).expect g = d1.expect g + d2.expect g := by
  simp [expect, List.map_append, List.sum_append]

theorem total_append (d1 d2 : Dist) : (d1 ++ d2).total = d1.total + d2.total := by
  simp [total, List.map_append, List.sum_append]

/-- **Expectation of a degree-≤4 polynomial** splits into a linear combination of the moments —
the workhorse that pushes the binomial expansion of `(x+y)ᵏ` through `expect`. -/
theorem expect_poly4 (d : Dist) (a0 a1 a2 a3 a4 : ℝ) :
    d.expect (fun x => a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4)
      = a0 * d.total + a1 * d.mean + a2 * d.rawMoment 2 + a3 * d.rawMoment 3 + a4 * d.rawMoment 4 := by
  induction d with
  | nil => simp [mean, rawMoment]
  | cons p d ih =>
    simp only [expect_cons, total_cons, mean_cons, rawMoment_cons, ih]
    ring

/-! ## Scaling — `κ_r(a·Z) = aʳ·κ_r(Z)` -/

/-- Scale every value by `a` (weights unchanged): the distribution of `a·X`. -/
def scale (a : ℝ) (d : Dist) : Dist := d.map (fun p => (a * p.1, p.2))

@[simp] theorem total_scale (a : ℝ) (d : Dist) : (scale a d).total = d.total := by
  induction d with
  | nil => rfl
  | cons p d ih =>
    have h : scale a (p :: d) = (a * p.1, p.2) :: scale a d := rfl
    rw [h, total_cons, total_cons, ih]

theorem expect_scale (a : ℝ) (d : Dist) (g : ℝ → ℝ) :
    (scale a d).expect g = d.expect (fun x => g (a * x)) := by
  induction d with
  | nil => rfl
  | cons p d ih =>
    have h : scale a (p :: d) = (a * p.1, p.2) :: scale a d := rfl
    rw [h, expect_cons, expect_cons, ih]

theorem rawMoment_scale (a : ℝ) (d : Dist) (k : ℕ) :
    (scale a d).rawMoment k = a ^ k * d.rawMoment k := by
  rw [rawMoment, expect_scale, rawMoment]
  rw [show (fun x => (a * x) ^ k) = (fun x => a ^ k * x ^ k) from by funext x; rw [mul_pow]]
  exact expect_const_mul (a ^ k) d (fun x => x ^ k)

theorem mean_scale (a : ℝ) (d : Dist) : (scale a d).mean = a * d.mean := by
  have h := rawMoment_scale a d 1
  simpa [mean, rawMoment, pow_one] using h

theorem kappa2_scale (a : ℝ) (d : Dist) : (scale a d).kappa2 = a ^ 2 * d.kappa2 := by
  simp only [kappa2, rawMoment_scale]

theorem kappa4_scale (a : ℝ) (d : Dist) : (scale a d).kappa4 = a ^ 4 * d.kappa4 := by
  simp only [kappa4, rawMoment_scale]; ring

theorem isProb_scale (a : ℝ) (d : Dist) (h : d.IsProb) : (scale a d).IsProb := by
  simpa [IsProb] using h

theorem isCentered_scale (a : ℝ) (d : Dist) (h : d.IsCentered) : (scale a d).IsCentered := by
  have hm : d.mean = 0 := h
  simp [IsCentered, mean_scale, hm]

/-! ## Convolution — the distribution of a sum of independent contributions -/

/-- **Convolution** `d₁ ⋆ d₂`: the distribution of `X + Y` for independent `X ∼ d₁`, `Y ∼ d₂` — every
pairwise sum `xᵢ + yⱼ` weighted by the product `wᵢ · w'ⱼ`. This is the actual sum-of-independent
construction; the cumulant-additivity below is a *theorem* about it, not a definition. -/
def conv : Dist → Dist → Dist
  | [], _ => []
  | p :: d1, d2 => (d2.map (fun q => (p.1 + q.1, p.2 * q.2))) ++ conv d1 d2

@[simp] theorem conv_nil (d2 : Dist) : conv [] d2 = [] := rfl

theorem conv_cons (p : ℝ × ℝ) (d1 d2 : Dist) :
    conv (p :: d1) d2 = (d2.map (fun q => (p.1 + q.1, p.2 * q.2))) ++ conv d1 d2 := rfl

/-- The single-input term: shifting `d₂` by `x` and reweighting by `w` scales its expectation. -/
theorem expect_shiftBy (x w : ℝ) (d2 : Dist) (g : ℝ → ℝ) :
    expect (d2.map (fun q => (x + q.1, w * q.2))) g = w * d2.expect (fun y => g (x + y)) := by
  induction d2 with
  | nil => simp [expect]
  | cons q d2 ih => simp only [List.map_cons, expect_cons, ih]; ring

/-- **Expectation over a convolution is the iterated expectation** — the joint of two independent
distributions factors. This is the one place independence enters, and it is a computed identity. -/
theorem expect_conv (d1 d2 : Dist) (g : ℝ → ℝ) :
    (conv d1 d2).expect g = d1.expect (fun x => d2.expect (fun y => g (x + y))) := by
  induction d1 with
  | nil => simp
  | cons p d1 ih =>
    rw [conv_cons, expect_append, ih, expect_cons, expect_shiftBy]

theorem total_conv (d1 d2 : Dist) : (conv d1 d2).total = d1.total * d2.total := by
  rw [total_eq_expect_one, expect_conv]
  rw [show (fun x : ℝ => d2.expect (fun _ => 1)) = (fun _ : ℝ => d2.total) from by
        funext x; exact (total_eq_expect_one d2).symm]
  rw [expect_const]

theorem mean_conv (d1 d2 : Dist) :
    (conv d1 d2).mean = d1.mean * d2.total + d1.total * d2.mean := by
  rw [mean, expect_conv]
  rw [show (fun x => d2.expect (fun y => x + y)) = (fun x => d2.total * x + d2.mean) from by
        funext x
        rw [expect_add d2 (fun _ => x) (fun y => y), expect_const]
        simp [mean]]
  rw [expect_add d1 (fun x => d2.total * x) (fun _ => d2.mean), expect_const_mul, expect_const]
  simp [mean]; ring

/-- The second moment of a convolution (general form, before centering). -/
theorem rawMoment_conv_two (d1 d2 : Dist) :
    (conv d1 d2).rawMoment 2
      = d2.total * d1.rawMoment 2 + 2 * d1.mean * d2.mean + d1.total * d2.rawMoment 2 := by
  rw [rawMoment, expect_conv]
  rw [show (fun x => d2.expect (fun y => (x + y) ^ 2))
        = (fun x => d2.rawMoment 2 + (2 * d2.mean) * x + d2.total * x ^ 2
                      + (0 : ℝ) * x ^ 3 + (0 : ℝ) * x ^ 4) from by
        funext x
        rw [show (fun y => (x + y) ^ 2)
              = (fun y => x ^ 2 + (2 * x) * y + (1 : ℝ) * y ^ 2 + (0 : ℝ) * y ^ 3 + (0 : ℝ) * y ^ 4)
              from by funext y; ring]
        rw [expect_poly4]; ring]
  rw [expect_poly4]; ring

/-- The fourth moment of a convolution (general form, before centering). -/
theorem rawMoment_conv_four (d1 d2 : Dist) :
    (conv d1 d2).rawMoment 4
      = d2.total * d1.rawMoment 4 + 4 * d2.mean * d1.rawMoment 3
        + 6 * d2.rawMoment 2 * d1.rawMoment 2 + 4 * d2.rawMoment 3 * d1.mean
        + d1.total * d2.rawMoment 4 := by
  rw [rawMoment, expect_conv]
  rw [show (fun x => d2.expect (fun y => (x + y) ^ 4))
        = (fun x => d2.rawMoment 4 + (4 * d2.rawMoment 3) * x + (6 * d2.rawMoment 2) * x ^ 2
                      + (4 * d2.mean) * x ^ 3 + d2.total * x ^ 4) from by
        funext x
        rw [show (fun y => (x + y) ^ 4)
              = (fun y => x ^ 4 + (4 * x ^ 3) * y + (6 * x ^ 2) * y ^ 2
                            + (4 * x) * y ^ 3 + (1 : ℝ) * y ^ 4)
              from by funext y; ring]
        rw [expect_poly4]; ring]
  rw [expect_poly4]; ring

/-! ## T5 — cumulants are additive under convolution -/

/-- Convolution preserves normalization: `total(d₁ ⋆ d₂) = 1` when both totals are `1`. -/
theorem isProb_conv (d1 d2 : Dist) (h1 : d1.IsProb) (h2 : d2.IsProb) : (conv d1 d2).IsProb := by
  have e := total_conv d1 d2
  simp only [IsProb] at *
  rw [e, h1, h2]; ring

/-- Convolution preserves centering: the mean of a sum of centered contributions is `0`. -/
theorem isCentered_conv (d1 d2 : Dist) (c1 : d1.IsCentered) (c2 : d2.IsCentered) :
    (conv d1 d2).IsCentered := by
  have m1 : d1.mean = 0 := c1
  have m2 : d2.mean = 0 := c2
  simp only [IsCentered, mean_conv, m1, m2]; ring

/-- **T5 (second cumulant).** For independent centered probability distributions the variances add:
`κ₂(d₁ ⋆ d₂) = κ₂ d₁ + κ₂ d₂`. -/
theorem kappa2_conv (d1 d2 : Dist) (h1 : d1.IsProb) (h2 : d2.IsProb)
    (c1 : d1.IsCentered) (c2 : d2.IsCentered) :
    (conv d1 d2).kappa2 = d1.kappa2 + d2.kappa2 := by
  have t1 : d1.total = 1 := h1
  have t2 : d2.total = 1 := h2
  have m1 : d1.mean = 0 := c1
  have m2 : d2.mean = 0 := c2
  simp only [kappa2]
  rw [rawMoment_conv_two, t1, t2, m1, m2]; ring

/-- **T5 (fourth cumulant).** For independent centered probability distributions the fourth cumulants
add: `κ₄(d₁ ⋆ d₂) = κ₄ d₁ + κ₄ d₂` — the `-3·E[X²]²` correction is exactly what cancels the
cross term `6·E[X²]·E[Y²]` from the fourth moment of the sum. -/
theorem kappa4_conv (d1 d2 : Dist) (h1 : d1.IsProb) (h2 : d2.IsProb)
    (c1 : d1.IsCentered) (c2 : d2.IsCentered) :
    (conv d1 d2).kappa4 = d1.kappa4 + d2.kappa4 := by
  have t1 : d1.total = 1 := h1
  have t2 : d2.total = 1 := h2
  have m1 : d1.mean = 0 := c1
  have m2 : d2.mean = 0 := c2
  simp only [kappa4]
  rw [rawMoment_conv_four, rawMoment_conv_two, t1, t2, m1, m2]; ring

/-! ## The cumulant map and its monoid-homomorphism onto `Ladder.Cumulants` -/

/-- The `(κ₂, κ₄)` pair of a distribution, valued in the `Ladder` `Cumulants` combine-monoid. -/
def cumulantsOf (d : Dist) : Cumulants := { kappa2 := d.kappa2, kappa4 := d.kappa4 }

@[simp] theorem cumulantsOf_kappa2 (d : Dist) : (cumulantsOf d).kappa2 = d.kappa2 := rfl
@[simp] theorem cumulantsOf_kappa4 (d : Dist) : (cumulantsOf d).kappa4 = d.kappa4 := rfl

/-- **T5 (homomorphism form).** `cumulantsOf` carries convolution to the `Cumulants` monoid's
addition: `cumulantsOf (d₁ ⋆ d₂) = cumulantsOf d₁ + cumulantsOf d₂`. Convolution ↦ cumulant
addition — the bridge underpinning T3, stated once. -/
theorem cumulantsOf_conv (d1 d2 : Dist) (h1 : d1.IsProb) (h2 : d2.IsProb)
    (c1 : d1.IsCentered) (c2 : d2.IsCentered) :
    cumulantsOf (conv d1 d2) = cumulantsOf d1 + cumulantsOf d2 := by
  ext
  · simpa using kappa2_conv d1 d2 h1 h2 c1 c2
  · simpa using kappa4_conv d1 d2 h1 h2 c1 c2

end Dist

/-! ## T3/T4 — the linearized SSPRC deviation, and its identity with the Willink combine -/

open _root_.PropertyKindCalculus.Uncertainty.Dist

/-- The point mass at `0` — the convolution identity and the empty-model deviation. -/
def deltaZero : Dist := [(0, 1)]

@[simp] theorem deltaZero_isProb : deltaZero.IsProb := by simp [deltaZero, IsProb, total]
@[simp] theorem deltaZero_isCentered : deltaZero.IsCentered := by
  simp [deltaZero, IsCentered, mean, expect]
@[simp] theorem cumulantsOf_deltaZero : cumulantsOf deltaZero = 0 := by
  ext <;> simp [deltaZero, cumulantsOf, kappa2, kappa4, rawMoment, expect]

/-- A **sensitized input**: a sensitivity coefficient `cᵢ`, the input's (centered) deviation
distribution `Zᵢ`, and the input's declared moment data `mᵢ`. The linear-model deviation along
input `i` is `cᵢ·Zᵢ`. -/
abbrev SensitizedInput := ℝ × Dist × MomentData ℝ

/-- The linearized-SSPRC **combined deviation**: convolve the per-input scaled deviations
`cᵢ·Zᵢ`. For a linear model this is exactly the SSPRC deviation distribution of the measurand. -/
def combinedDeviation (xs : List SensitizedInput) : Dist :=
  xs.foldr (fun t acc => conv (scale t.1 t.2.1) acc) deltaZero

/-- The `(cᵢ, mᵢ)` term list the Willink/GUM combines consume. -/
def termsOf (xs : List SensitizedInput) : List (ℝ × MomentData ℝ) :=
  xs.map (fun t => (t.1, t.2.2))

theorem combinedDeviation_isProb (xs : List SensitizedInput)
    (hp : ∀ t ∈ xs, (t.2.1 : Dist).IsProb) : (combinedDeviation xs).IsProb := by
  induction xs with
  | nil => simp [combinedDeviation]
  | cons t xs ih =>
    have ht : (t.2.1 : Dist).IsProb := hp t (List.mem_cons_self)
    have htail : ∀ s ∈ xs, (s.2.1 : Dist).IsProb := fun s hs => hp s (List.mem_cons_of_mem _ hs)
    simpa [combinedDeviation] using
      isProb_conv _ _ (isProb_scale _ _ ht) (ih htail)

theorem combinedDeviation_isCentered (xs : List SensitizedInput)
    (hc : ∀ t ∈ xs, (t.2.1 : Dist).IsCentered) : (combinedDeviation xs).IsCentered := by
  induction xs with
  | nil => simp [combinedDeviation]
  | cons t xs ih =>
    have ht : (t.2.1 : Dist).IsCentered := hc t (List.mem_cons_self)
    have htail : ∀ s ∈ xs, (s.2.1 : Dist).IsCentered := fun s hs => hc s (List.mem_cons_of_mem _ hs)
    simpa [combinedDeviation] using
      isCentered_conv _ _ (isCentered_scale _ _ ht) (ih htail)

/-- **T4 — the SSPRC reference gap is `Σ cᵢ·E(Zᵢ)`.** The combined deviation's mean is the weighted
sum of the per-input deviation means. For a linear model every `Zᵢ` is centered, so the mean is `0`
and `R = f(E(X))` equals `E(Y)`; a non-zero term is a non-linearity signature the linearized methods
cannot see. -/
theorem mean_combinedDeviation (xs : List SensitizedInput)
    (hp : ∀ t ∈ xs, (t.2.1 : Dist).IsProb) :
    (combinedDeviation xs).mean = (xs.map (fun t => t.1 * t.2.1.mean)).sum := by
  induction xs with
  | nil => simp [combinedDeviation, deltaZero, mean, expect]
  | cons t xs ih =>
    have ht : (t.2.1 : Dist).IsProb := hp t (List.mem_cons_self)
    have htail : ∀ s ∈ xs, (s.2.1 : Dist).IsProb := fun s hs => hp s (List.mem_cons_of_mem _ hs)
    have hacc : (combinedDeviation xs).IsProb := combinedDeviation_isProb xs htail
    have hs : (scale t.1 t.2.1).total = 1 := by
      have : (t.2.1 : Dist).total = 1 := ht
      simpa [total_scale] using this
    have hat : (combinedDeviation xs).total = 1 := hacc
    simp only [combinedDeviation, List.foldr_cons, List.map_cons, List.sum_cons] at *
    rw [mean_conv, hs, hat, mean_scale, ih htail]; ring

/-- **T3 — Willink is the `(κ₂,κ₄)`-projection of the linearized SSPRC.** If each input's deviation
distribution `Zᵢ` is a centered probability distribution realizing its declared moments
(`κ₂ Zᵢ = uᵢ²`, `κ₄ Zᵢ = wᵢ`), then the cumulants of the convolved combined deviation are *exactly*
the Willink combined cumulants `(Σcᵢ²uᵢ², Σcᵢ⁴wᵢ)`. So convolving the separately-propagated inputs
and truncating at the fourth cumulant reproduces `willink` — the lower rung of the ladder. -/
theorem cumulantsOf_combinedDeviation (xs : List SensitizedInput)
    (hp : ∀ t ∈ xs, (t.2.1 : Dist).IsProb)
    (hc : ∀ t ∈ xs, (t.2.1 : Dist).IsCentered)
    (hk2 : ∀ t ∈ xs, (t.2.1 : Dist).kappa2 = t.2.2.variance)
    (hk4 : ∀ t ∈ xs, (t.2.1 : Dist).kappa4 = t.2.2.fourthCumulant) :
    cumulantsOf (combinedDeviation xs) = willinkCumulants (termsOf xs) := by
  induction xs with
  | nil => simp [combinedDeviation, termsOf, willinkCumulants]
  | cons t xs ih =>
    have ht2 : (t.2.1 : Dist).IsProb := hp t (List.mem_cons_self)
    have htc : (t.2.1 : Dist).IsCentered := hc t (List.mem_cons_self)
    have htk2 : (t.2.1 : Dist).kappa2 = t.2.2.variance := hk2 t (List.mem_cons_self)
    have htk4 : (t.2.1 : Dist).kappa4 = t.2.2.fourthCumulant := hk4 t (List.mem_cons_self)
    have hpTail : ∀ s ∈ xs, (s.2.1 : Dist).IsProb := fun s hs => hp s (List.mem_cons_of_mem _ hs)
    have hcTail : ∀ s ∈ xs, (s.2.1 : Dist).IsCentered := fun s hs => hc s (List.mem_cons_of_mem _ hs)
    have hk2Tail : ∀ s ∈ xs, (s.2.1 : Dist).kappa2 = s.2.2.variance :=
      fun s hs => hk2 s (List.mem_cons_of_mem _ hs)
    have hk4Tail : ∀ s ∈ xs, (s.2.1 : Dist).kappa4 = s.2.2.fourthCumulant :=
      fun s hs => hk4 s (List.mem_cons_of_mem _ hs)
    -- head contribution as a Willink term
    have headTerm : cumulantsOf (scale t.1 t.2.1) = termCumulants (t.1, t.2.2) := by
      ext
      · simp [cumulantsOf, termCumulants, kappa2_scale, htk2]
      · simp [cumulantsOf, termCumulants, kappa4_scale, htk4]
    have hAccProb : (combinedDeviation xs).IsProb := combinedDeviation_isProb xs hpTail
    have hAccCent : (combinedDeviation xs).IsCentered := combinedDeviation_isCentered xs hcTail
    simp only [combinedDeviation, List.foldr_cons] at *
    rw [cumulantsOf_conv _ _ (isProb_scale _ _ ht2) hAccProb (isCentered_scale _ _ htc) hAccCent,
      headTerm, ih hpTail hcTail hk2Tail hk4Tail]
    rw [show termsOf (t :: xs) = (t.1, t.2.2) :: termsOf xs from rfl, willinkCumulants_cons]

end PropertyKindCalculus.Uncertainty

end Blanket
