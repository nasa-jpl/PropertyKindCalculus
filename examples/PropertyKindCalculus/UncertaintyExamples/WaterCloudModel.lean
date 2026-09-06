/-
# Stage 4 capstone — the Water Cloud Model soil-moisture forward, kinded end to end

The workstream's science-model capstone, written in the calculus' **rigorous quantity discipline**:
every quantity carries a kind-of-property, the model's numeric constants live — as kinded
quantities — in a single configuration structure, and a naked `Float` appears *only* at the emission
boundary where the model meets the (scalar) uncertainty propagators. This mirrors the
soil-moisture-model's `ConfigKinds`/`AvsKinds` discipline (`METROLOGICAL_RIGOR.md`): the config is
the metrologist's form of every numeric constant, and the kernel body is literal-free.

**The model.** The Water Cloud Model (Attema & Ulaby 1978), the standard first-order
vegetation-scattering forward used to invert radar backscatter for soil moisture, predicts the
co-polarised backscatter `σ⁰` from soil moisture `mv`, a vegetation descriptor `ndvi`, and a canopy
attenuation rate `b`:

    σ⁰ = veg + τ·(soil − veg),   veg = a·ndvi,  soil = c·mv + d,  τ = exp(−2·b·ndvi)          (WCM)

equivalently `σ⁰ = a·ndvi·(1 − τ) + τ·(c·mv + d)`: a canopy volume-scattering term plus the soil
backscatter `c·mv + d` (linear in soil moisture) attenuated two-ways through the canopy by the
transmissivity `τ`. The calibration coefficients `a, c, d` (and the two-way factor `2`) are the
**configuration**; `mv, ndvi, b` are the **uncertain inputs**.

**Why the kinds.** Read off the model, the four coefficient/covariate kinds are forced and distinct:
`a : σ⁰·ndvi⁻¹`, `c : σ⁰·mv⁻¹`, `d : σ⁰`, `b : ndvi⁻¹` (so `b·ndvi` is dimension one and can be
exponentiated). Three of the intermediate kinds — the `pureNumber` coefficient `−2`, the
`attenExponent` `−2·b·ndvi`, and the `attenuation` `τ` — are all *dimension one*, so a dimension-only
checker waves every confusion among them through; only the **kind** check keeps them apart (the
`#check_failure` probes at the end certify the rejections). Nothing in the kernel is a bare number:
each product carries the `ProductKind` edge it stands on, `exp` its `TranscendentalKind` edge, and the
result kind `σ⁰ : backscatter` is forced by construction.

**The pipeline, unchanged.** Because a kinded operation is its magnitude by construction
(`Quantity.mul h a b |>.magnitude = a.magnitude * b.magnitude`, definitionally), the `.magnitude`
projection at the emission boundary is *op-for-op* the scalar forward the propagators evaluate — so
the whole Stage-0…Stage-4 pipeline runs on the kinded kernel with no second model. One kernel, five
rungs, every number a checked fact:

  1. **Forward** — the predicted `σ⁰` at the input means.
  2. **Autograd Jacobian** — one TorchLean reverse pass yields `∂σ⁰/∂(mv,ndvi,b)`, matched to the
     hand-derived closed forms (differentiates through the kinded `exp`).
  3. **GUM / Willink** — the linearized combined standard uncertainty.
  4. **SSPRC** — recovers the mean including the small `exp`-curvature offset the linearized rungs miss.
  5. **Allocation** (Stage 4) — spends the SSPRC budget by contribution, ranking the dominant input
     and dropping the negligible attenuation rate; SSPRC on the allocated `ns` holds at half the budget.

Self-contained by necessity: PKC cannot import the downstream `soil-moisture-model` (that package
already *requires* PKC — a dependency cycle), so the WCM kinds and kernel are written fresh here.
Depends on TorchLean (the autograd column of rung 2).
-/
import PropertyKindCalculus.Uncertainty
import PropertyKindCalculus.Uncertainty.Sensitivity
import PropertyKindCalculus.Index.Commands
import PropertyKindCalculus.DocGenMath

namespace PropertyKindCalculus.UncertaintyExamples.WaterCloudModel

open PropertyKindCalculus PropertyKindCalculus.Paradigm PropertyKindCalculus.Uncertainty
open PropertyKindCalculus.Uncertainty.Allocation
open PropertyKindCalculus.Paradigm (TapeBuilder)

/-! ## The kinds-of-property (the opt-in registry)

Each kind is declared with the kind equation it stands for and — for the products/`exp` — the
opt-in algebra edges the kernel writes at its call sites. All ratio-scale, so the kind arithmetic is
defined; all dimension one, so a dimension checker cannot separate them (that is the point). -/

/-- σ⁰ — the co-polarised backscatter coefficient: the model's output. -/
def backscatter : KindOfProperty := { id := "WCM backscatter coefficient σ⁰", scale := .ratio }
/-- The vegetation index `ndvi` — the canopy covariate. -/
def vegetationIndex : KindOfProperty := { id := "vegetation index NDVI", scale := .ratio }
/-- Volumetric soil moisture `mv` — the retrieval target. -/
def soilMoisture : KindOfProperty := { id := "volumetric soil moisture", scale := .ratio }
/-- The pure number — the identity of the kind algebra; here the two-way coefficient `−2`. Edge:
`pureNumber · attenRate → attenRate` (the `−2·b` step). -/
def pureNumber : KindOfProperty := { id := "WCM pure number", scale := .ratio }
/-- The attenuation exponent `−2·b·ndvi` — dimension one precisely because `b : ndvi⁻¹`, but not a
generic pure number: the one quantity `exp` consumes. Produced by `attenRate · vegetationIndex →
attenExponent`; consumed only by `exp`. -/
def attenExponent : KindOfProperty := { id := "canopy attenuation exponent", scale := .ratio }
/-- The vegetation attenuation `τ = exp(−2·b·ndvi)` — the two-way canopy transmissivity. Produced by
`exp : attenExponent → attenuation`; consumed by `attenuation · backscatter → backscatter` (it scales
a backscatter within its kind). -/
def attenuation : KindOfProperty := { id := "vegetation attenuation τ", scale := .ratio }
/-- `a : σ⁰·ndvi⁻¹` — the vegetation backscatter gain (the `a·ndvi` term is a backscatter). -/
def vegGain : KindOfProperty := { id := "vegetation backscatter gain (σ⁰ per NDVI)", scale := .ratio }
/-- `b : ndvi⁻¹` — the canopy attenuation rate (`−2·b·ndvi` is the `attenExponent`). -/
def attenRate : KindOfProperty := { id := "canopy attenuation rate (per NDVI)", scale := .ratio }
/-- `c : σ⁰·mv⁻¹` — the soil-moisture backscatter gain (the `c·mv` term is a backscatter). -/
def soilGain : KindOfProperty := { id := "soil-moisture backscatter gain (σ⁰ per moisture)", scale := .ratio }
-- `d : backscatter` — the bare-soil offset is added directly to σ⁰, so its kind is `backscatter`.

/-! ## The kind algebra the kernel stands on, witnessed

The six edges below are exactly the ones `wcmForwardQ` writes; and the three dimension-one roles are
pairwise distinct kinds, which is what lets the type system separate them where a dimension checker
cannot. (Per the calculus' trust model, `ProductKind.ofRatio` signs any ratio-scale triple, so an
edge's *truth* is the author's claim — a witness is to the kind algebra what an axiom is to a proof;
these are the enumerable trusted base, and the `#check_failure` probes certify the forbidden edges.) -/

/-- The product/transcendental edges of the WCM forward. -/
theorem wcm_kind_algebra :
    ProductKind pureNumber attenRate attenRate                    -- −2 · b
      ∧ ProductKind attenRate vegetationIndex attenExponent       -- (−2·b) · ndvi
      ∧ TranscendentalKind attenExponent attenuation              -- exp : exponent → attenuation
      ∧ ProductKind vegGain vegetationIndex backscatter           -- a · ndvi
      ∧ ProductKind soilGain soilMoisture backscatter             -- c · mv
      ∧ ProductKind attenuation backscatter backscatter :=        -- τ · (soil − veg)
  ⟨ProductKind.ofRatio _ _ _, ProductKind.ofRatio _ _ _, ⟨rfl, rfl⟩,
   ProductKind.ofRatio _ _ _, ProductKind.ofRatio _ _ _, ProductKind.ofRatio _ _ _⟩

/-- The three dimension-one roles are pairwise distinct kinds: the coefficient `−2` is not the
exponent `−2·b·ndvi` is not the transmissivity `τ`. A dimension checker sees `1 = 1 = 1`. -/
theorem attenuation_roles_distinct :
    pureNumber ≠ attenExponent ∧ pureNumber ≠ attenuation ∧ attenExponent ≠ attenuation := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## The configuration — every numeric constant, as a kinded quantity

`WcmConfig` is the sole place a numeral is written: each calibration coefficient (and the two-way
factor) is a `Quantity` of its forced kind. `deployed` is carrier-generic (`{α} [NumCarrier α]`), so
the *same* configuration instantiates at `Float` (evaluation), at the TorchLean tape (autograd), and
would at `ℝ` (proofs). The numerals are `Nat`-ratio structural literals (`NumCarrier` embeds
`Coe Nat α`, not `OfNat α n`). -/

/-- Lift a structural literal `n : ℕ` into the numeric carrier (via `NumCarrier`'s `Coe Nat α`) —
used only inside `deployed`, to author the configuration's magnitudes. -/
def natLit {α : Type} [NumCarrier α] (n : Nat) : α := (n : α)

/-- The deployed WCM calibration: the vegetation gain `a`, soil-moisture gain `c`, bare-soil offset
`d`, and the two-way optical-path factor `2` — each a kinded quantity. -/
structure WcmConfig (α : Type) where
  /-- Vegetation backscatter gain `a` (kind `vegGain`). -/
  a : Quantity vegGain α
  /-- Soil-moisture backscatter gain `c` (kind `soilGain`). -/
  c : Quantity soilGain α
  /-- Bare-soil backscatter offset `d` (kind `backscatter`). -/
  d : Quantity backscatter α
  /-- The two-way optical-path factor `2` (kind `pureNumber`). -/
  two : Quantity pureNumber α

/-- The deployed calibration `a = 0.12, c = 0.10, d = 0.02, two = 2` — carrier-generic, so it is the
one configuration read at every carrier. The only numerals in the module live here. -/
def deployed {α : Type} [NumCarrier α] : WcmConfig α where
  a := ⟨natLit 12 / natLit 100⟩
  c := ⟨natLit 1 / natLit 10⟩
  d := ⟨natLit 1 / natLit 50⟩
  two := ⟨natLit 2⟩

/-! ## The kinded forward kernel — literal-free

`wcmForwardQ` reads its coefficients from `cfg` and builds `σ⁰` through kind-witnessed products, a
kind-witnessed `exp`, and same-kind `±`; the only inline symbol is the carrier's additive identity
`0` (for the negation `0 − 2`, since `NumCarrier` has no `Neg`). The result kind `backscatter` is
forced by the parameter kinds. -/

/-- **The Water Cloud Model forward** `σ⁰ = veg + τ·(soil − veg)` over any branchless numeric carrier,
kinded throughout. `.magnitude` is the scalar WCM forward, op-for-op. -/
@[pkc_math "\\sigma^0 = a\\,\\mathrm{NDVI} + e^{-2\\,b\\,\\mathrm{NDVI}}\\,(c\\,m_v + d - a\\,\\mathrm{NDVI})"]
def wcmForwardQ {α : Type} [NumCarrier α] (cfg : WcmConfig α)
    (mv : Quantity soilMoisture α) (ndvi : Quantity vegetationIndex α)
    (b : Quantity attenRate α) : Quantity backscatter α :=
  -- τ = exp(−2·b·ndvi): the exponent (−2·b)·ndvi has kind `attenExponent`; `exp` carries it to `τ`.
  let negTwo : Quantity pureNumber α := (⟨(0 : α)⟩ : Quantity pureNumber α) - cfg.two
  let arg : Quantity attenExponent α :=
    Quantity.mul (ProductKind.ofRatio attenRate vegetationIndex attenExponent)
      (Quantity.mul (ProductKind.ofRatio pureNumber attenRate attenRate) negTwo b) ndvi
  let τ : Quantity attenuation α :=
    Quantity.exp (⟨rfl, rfl⟩ : TranscendentalKind attenExponent attenuation) arg
  -- the two backscatter terms
  let veg : Quantity backscatter α :=
    Quantity.mul (ProductKind.ofRatio vegGain vegetationIndex backscatter) cfg.a ndvi
  let soil : Quantity backscatter α :=
    Quantity.mul (ProductKind.ofRatio soilGain soilMoisture backscatter) cfg.c mv + cfg.d
  veg + Quantity.mul (ProductKind.ofRatio attenuation backscatter backscatter) τ (soil - veg)

/-! ## The emission boundary — where the model meets the (scalar) propagators

The uncertainty pipeline (`Mcm`, `Ssprc`, `Sensitivity`, `Allocation`) consumes a scalar model
`List α → α`. Here — and *only* here — the raw carrier inputs are wrapped into kinded quantities and
the kinded output is projected back with `.magnitude`; that projection is definitionally the scalar
WCM forward, so the propagators see exactly the model `wcmForwardQ` specifies, with no naked twin. -/

/-- The kinded forward as the arity-3 `List Float → Float` the propagators consume (config at `Float`). -/
def modelF : List Float → Float
  | [m, n, b] => (wcmForwardQ deployed ⟨m⟩ ⟨n⟩ ⟨b⟩).magnitude
  | _ => 0.0

/-- The same kinded forward presented to the autograd bridge — the config instantiates at the tape
carrier `TapeBuilder .scalar`, so one reverse pass differentiates through the kinded `exp`. -/
def modelTape : Sensitivity.ScalarModel
  | [m, n, b] => (wcmForwardQ deployed ⟨m⟩ ⟨n⟩ ⟨b⟩).magnitude
  | _ => 0

/-! ## The uncertain inputs — kinded quantities with a stated uncertainty

Each input is an `UncertainQuantity k Float`: a kinded point value paired with its `InputDist`. `mv`
is the retrieval target, `ndvi` the vegetation covariate, `b` the canopy attenuation rate carried
per-pixel with its calibration uncertainty. The propagators read the `.dist` descriptors and the
`.value.magnitude` means at the boundary. -/

/-- `mv ~ Normal(0.25, σ=0.03)` — mid-range volumetric soil moisture. -/
def mvU : UncertainQuantity soilMoisture Float := .atMean (InputDist.normal 0.25 0.03)
/-- `ndvi ~ Uniform(0.5, δ=0.1)` — a moderately vegetated pixel. -/
def ndviU : UncertainQuantity vegetationIndex Float := .atMean (InputDist.uniform 0.5 0.1)
/-- `b ~ Triangular(0.15, δ=0.03)` — the canopy attenuation rate with calibration uncertainty. -/
def bU : UncertainQuantity attenRate Float := .atMean (InputDist.triangular 0.15 0.03)

/-- The three input distributions, in model order. -/
def inputs : List (InputDist Float) := [mvU.dist, ndviU.dist, bU.dist]
/-- The reference point `E(X) = (mv̄, ndvī, b̄) = (0.25, 0.5, 0.15)` — the kinded means, projected. -/
def means : List Float := [mvU.value.magnitude, ndviU.value.magnitude, bU.value.magnitude]

/-! ## Kind safety — the confusions the type system rejects

Reusing the inputs' own kinded point values (no naked numerals): the forward is well-kinded only in
the right argument order; a covariate in the wrong slot, or a kind-1 role swapped for another, is a
compile error a dimension checker would pass. -/

-- Well-kinded: the forward classifies as a `backscatter`.
#check (wcmForwardQ deployed mvU.value ndviU.value bU.value : Quantity backscatter Float)
-- A vegetation index cannot be passed where soil moisture is expected.
#check_failure (wcmForwardQ deployed ndviU.value ndviU.value bU.value)
-- The canopy rate `b` cannot be passed where the covariate `ndvi` is expected.
#check_failure (wcmForwardQ deployed mvU.value bU.value bU.value)

/-! ## Rung 1 — the forward prediction

At the means `τ = exp(−0.15) = 0.860708`, `veg = 0.06`, `soil = 0.045`, so
`σ⁰ = 0.06 + 0.860708·(0.045 − 0.06) = 0.047089`. This is also the linearized methods' output mean
`R = f(E(X))`. -/

#eval s!"forward  σ⁰(E(X)) = {modelF means}   (expect 0.047089)"

-- σ⁰ at the means, to the closed-form value 0.06 + exp(−0.15)·(−0.015).
#guard Float.abs (modelF means - 0.047089380353624133) < 1e-6
-- A physically valid (positive) backscatter — a compile-time non-vacuity witness.
#guard modelF means > 0.0

/-! ## Rung 2 — the autograd Jacobian equals the closed-form columns

One TorchLean reverse pass over the kinded kernel (through the kinded `exp`) yields `cᵢ = ∂σ⁰/∂Xᵢ` at
the means. The closed forms (with `τ = exp(−0.15)`, `soil−veg = −0.015`) are

    ∂σ⁰/∂mv   = τ·c                          = 0.0860708
    ∂σ⁰/∂ndvi = a·(1−τ) + (−2b·τ)·(soil−veg) = 0.0205882
    ∂σ⁰/∂b    = (−2·ndvi·τ)·(soil−veg)       = 0.0129106

and reverse-mode AD reproduces every column to 6 decimals — the `.magnitude` of the kinded model
differentiates exactly as the scalar one. These `cᵢ` feed the GUM/Willink combine (rung 3) and the
allocation (rung 5). -/

/-- The autograd sensitivity columns `∂σ⁰/∂(mv, ndvi, b)` at the means, from one reverse pass. -/
def cs : List Float := (Sensitivity.gradient modelTape means).toOption.getD []

#eval s!"autograd  c = {cs}   (closed form [0.0860708, 0.0205882, 0.0129106])"

#guard cs.length == 3
-- ∂σ⁰/∂mv = τ·c.
#guard Float.abs (cs[0]! - 0.08607079764250578)  < 1e-6
-- ∂σ⁰/∂ndvi = a·(1−τ) − 2b·τ·(soil−veg).
#guard Float.abs (cs[1]! - 0.020588228722905824) < 1e-6
-- ∂σ⁰/∂b = −2·ndvi·τ·(soil−veg).  Positive here because soil−veg < 0.
#guard Float.abs (cs[2]! - 0.012910619646375867) < 1e-6

/-! ## Rung 3 — GUM / Willink combined standard uncertainty

The autograd `cᵢ` zipped with the inputs' moments feed the linearized combine. GUM gives
`u_c = √(Σ cᵢ²uᵢ²) ≈ 0.002847`; the Willink cumulants method returns the same `u_Y` to second order. -/

/-- The `(cᵢ, momentsᵢ)` term list, autograd-sourced — the Stage-1 `extract` feeding the combine. -/
def terms : List (Float × MomentData Float) :=
  (Sensitivity.coefficients modelTape inputs).toOption.getD []

/-- GUM combined standard uncertainty from the autograd sensitivities. -/
def gum : Float := gumStdUnc terms
/-- Willink cumulants combine `(u_Y, γ_Y)` from the same terms. -/
def willink : Float × Float := willinkCombine terms

#eval s!"GUM  u_c(σ⁰) ≈ {gum}   |  Willink u_Y ≈ {willink.1}  γ_Y ≈ {willink.2}"

#guard terms.length == 3
-- GUM u_c ≈ 0.002847 (= √(Σ cᵢ²uᵢ²)).
#guard Float.abs (gum - 0.00284698) < 1e-5
-- Willink's u_Y is the same second cumulant — GUM is its κ₄-projection (ladder theorem T2).
#guard Float.abs (willink.1 - gum) < 1e-9

/-! ## Rung 4 — SSPRC recovers the non-linear mean

The derivative-free SSPRC pipeline on a flat `[100, 100, 100]` budget (300 evaluations + 1 reference,
vs the Monte Carlo reference's 20 000 draws). Its combined `E(σ⁰)` picks up the small `exp`-curvature
offset above the linearized mean `R = f(E(X)) = 0.047089` — the non-linearity the GUM/Willink rungs
structurally miss — and its `u(σ⁰)` agrees with the other rungs (weak non-linearity at these input
uncertainties, so the rungs cluster to ~1 %). -/

/-- Per-input systematic sample counts — the flat baseline. -/
def nsFlat : List Nat := [100, 100, 100]
/-- The SSPRC combined `(E(σ⁰), u(σ⁰))`. -/
def ssprc : Float × Float := Ssprc.run modelF inputs nsFlat
/-- The reference value `R = f(E(X))` — also the linearized methods' output mean. -/
def R : Float := Ssprc.reference modelF inputs
/-- The Monte Carlo reference `(E(σ⁰), u(σ⁰))`, 20 000 joint draws. -/
def mcm : Float × Float := Mcm.run modelF inputs 20000 0x5EED1234

#eval s!"SSPRC  E={ssprc.1}  u={ssprc.2}   (R={R};  E−R={ssprc.1 - R};  evals={Ssprc.evalCount nsFlat})"
#eval s!"MCM    E={mcm.1}  u={mcm.2}   (20000 draws)"

-- SSPRC's mean agrees with the 20 000-draw Monte Carlo reference…
#guard Float.abs (ssprc.1 - mcm.1) < 1e-4
#guard Float.abs (ssprc.2 - mcm.2) < 1.5e-4
-- …and it lies *above* the linearized mean R by the exp-curvature offset (≈ +0.000100)…
#guard ssprc.1 - R > 5e-5
#guard Float.abs ((ssprc.1 - R) - 0.000100) < 3e-5
-- …which the reference value R = f(E(X)) = σ⁰(means) is, exactly.
#guard Float.abs (R - 0.047089380353624133) < 1e-6
-- SSPRC's u(σ⁰) agrees with the linearized GUM to ~1 % (weak non-linearity).
#guard Float.abs (ssprc.2 - gum) < 5e-5
-- The additive budget: 301 evaluations, vs Monte Carlo's 20 000.
#guard Ssprc.evalCount nsFlat == 301

/-! ## Rung 5 — sensitivity-driven allocation

The per-input contributions `wᵢ = |cᵢ|·uᵢ` rank the inputs by their share of the combined
uncertainty: `w ≈ [0.00258, 0.00119, 0.00016]`. **Soil moisture dominates** (the retrieval target —
the budget belongs on the signal, not the calibration), `ndvi` is second, and the canopy rate `b` is
a distant third at ~16× less. `allocate` apportions the whole budget in that ratio; at
`dropRatio = 0.1` the negligible `b` is dropped outright. And SSPRC on the allocated `ns` reproduces
the mean at *half* the flat budget, because the samples it cuts are `b`'s and `ndvi`'s over-sampling,
not the soil-moisture signal. -/

/-- The per-input contributions `wᵢ = |cᵢ|·uᵢ` from the autograd sensitivities. -/
def ws : List Float := contributions terms
/-- The sensitivity-driven counts at the flat 300-sample budget. -/
def ns300 : List Nat := allocateFromTerms 300 terms
/-- A halved budget of 150 samples, allocated. -/
def ns150 : List Nat := allocateFromTerms 150 terms
/-- SSPRC on the halved, allocated budget. -/
def ssprc150 : Float × Float := Ssprc.run modelF inputs ns150

#eval s!"contribs  w = {ws}"
#eval s!"allocate 300 = {ns300}  (Σ={ns300.foldl (·+·) 0})   drop 0.1 = {allocate 300 ws 0.1}"
#eval s!"allocate 150 = {ns150}   SSPRC@150  E={ssprc150.1}  u={ssprc150.2}  evals={Ssprc.evalCount ns150}"

-- Soil moisture is the dominant contributor; the canopy rate b is the least.
#guard ws[0]! > ws[1]! && ws[1]! > ws[2]!
#guard ws[0]! > 2.0 * ws[2]!
-- Proportional split at 300: mv the most, b the fewest, budget spent exactly.
#guard ns300 == [197, 91, 12]
#guard ns300.foldl (· + ·) 0 == 300
-- The sample ranking follows the contribution ranking: N_mv ≥ N_ndvi ≥ N_b.
#guard ns300[0]! ≥ ns300[1]! && ns300[1]! ≥ ns300[2]!
-- At dropRatio 0.1 the negligible b (w_b < 0.1·w_mv) is dropped; its budget goes to the survivors.
#guard allocate 300 ws 0.1 == [205, 95, 0]
-- Halving the budget still spends it whole, and keeps mv's samples nearly intact…
#guard ns150.foldl (· + ·) 0 == 150
#guard ns150[0]! ≥ 90
-- …so SSPRC on the halved allocation still recovers the mean and the uncertainty…
#guard Float.abs (ssprc150.1 - ssprc.1) < 1e-4
#guard Float.abs (ssprc150.2 - ssprc.2) < 1e-4
-- …at 151 evaluations — half the flat 301, and ~132× fewer than the Monte Carlo reference.
#guard Ssprc.evalCount ns150 == 151

/-! ## Rung 6 — the budget at the boundary

The join of the uncertainty stack and the `Provenance` stack: the forward's boundary is
declared, and the rung-5 contributions attach to its output port as a `PortBudget` —
one term per influencing *source*, checked by `#kind_budget` against the assembled
graph. The report carries the metrology in both directions: the three uncertain inputs
are the terms and their quadrature is the GUM `u_c` of rung 3, and the four calibration
parameters render as `unbudgeted source(s)` — the WCM calibration is carried without
an uncertainty, and the boundary now says so instead of leaving it implicit. -/

/-- The forward's declared boundary: the three uncertain inputs, the four calibration
parameters a deployment binds, and the σ⁰ output. -/
def wcmBoundary : Provenance.Contract String String where
  name := "WCM forward (σ⁰)"
  members := ["PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.wcmForwardQ"]
  ports := [
    ⟨"wcmForwardQ/cfg.a", "vegGain", .param⟩,
    ⟨"wcmForwardQ/cfg.c", "soilGain", .param⟩,
    ⟨"wcmForwardQ/cfg.d", "backscatter", .param⟩,
    ⟨"wcmForwardQ/cfg.two", "pureNumber", .param⟩,
    ⟨"wcmForwardQ/mv", "soilMoisture", .input⟩,
    ⟨"wcmForwardQ/ndvi", "vegetationIndex", .input⟩,
    ⟨"wcmForwardQ/b", "attenRate", .input⟩,
    ⟨"wcmForwardQ/result", "backscatter", .output⟩]
  exits := []

/--
info: kind contract over 1 steps:
contract 'WCM forward (σ⁰)': 8 ports, 0 exits
params: wcmForwardQ/cfg.a, wcmForwardQ/cfg.c, wcmForwardQ/cfg.d, wcmForwardQ/cfg.two
boundary agrees: true
-/
#guard_msgs in #kind_contract wcmBoundary

/-- **The σ⁰ budget-per-output-port**: one term per uncertain input, each the
output-kind contribution `|cᵢ|·u(xᵢ)` of rung 5, attached to the boundary's output.
The combined line is the quadrature of the terms — the GUM `u_c` of rung 3, recomputed
at the boundary rather than copied to it. -/
def sigma0Budget : PortBudget :=
  { port := "wcmForwardQ/result", kind := "backscatter",
    terms := [("wcmForwardQ/mv", ws[0]!), ("wcmForwardQ/ndvi", ws[1]!),
              ("wcmForwardQ/b", ws[2]!)] }

/--
info: budget for 'wcmForwardQ/result' : backscatter on 'WCM forward (σ⁰)': 3 term(s) over 7 influencing source(s)
  term wcmForwardQ/mv: 0.002582
  term wcmForwardQ/ndvi: 0.001189
  term wcmForwardQ/b: 0.000158
  combined: 0.002847
  unbudgeted source(s): wcmForwardQ/cfg.a, wcmForwardQ/cfg.c, wcmForwardQ/cfg.d, wcmForwardQ/cfg.two
-/
#guard_msgs (whitespace := lax) in #kind_budget sigma0Budget wcmBoundary

-- The self-index renders the attachment: one row, port and kind and terms and combined.
/--
info: Uncertainty budgets at the boundary (1 row(s))
Budget | Port | Kind | Terms | Combined
sigma0Budget | wcmForwardQ/result | backscatter | 3 | 0.002847
-/
#guard_msgs (whitespace := lax) in
#pkc_index "port-budgets" PropertyKindCalculus.UncertaintyExamples

-- The attachment's quadrature is rung 3's GUM combine — same terms, same number.
#guard Float.abs (sigma0Budget.combined - gum) < 1e-12

/-- **The coverage tolerance the budget licenses**: `k = 2` times the combined standard
uncertainty, a `Quantity` at the output port's kind — exactly what a `boundedBy`
relation names as its tolerance. Distribution-free, the factor buys at least
`1 − 1/k² = 75 %` coverage (`Coverage.coverageBound_stdUnc`); under the Gaussian
reading it is the usual 95 %. -/
def sigma0CoverageTol : Quantity backscatter Float := ⟨2.0 * sigma0Budget.combined⟩

-- The tolerance is a real, positive backscatter quantity.
#guard sigma0CoverageTol.magnitude > 0.0

end PropertyKindCalculus.UncertaintyExamples.WaterCloudModel
