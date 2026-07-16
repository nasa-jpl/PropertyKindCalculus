import Verso
import VersoManual
import VersoBlueprint
-- Every realized node below is linked to a real declaration via `(lean := "PropertyKindCalculus.…")`
-- and is elaborated for its proved/`sorry` status, so the chapter imports the Stage-0 uncertainty
-- library, the Stage-1 `Ladder` (T1/T2 over `ℝ`) and `Sensitivity` autograd bridge, and the Stage-2
-- `Ssprc` executable pipeline (`Float`) and `Convolution` (T3/T4/T5 over `ℝ`). The `Sensitivity`
-- import pulls TorchLean into the blueprint build, deliberately, so the sensitivity coefficients are
-- a formal lean-linked node rather than prose. Only the numerical-adequacy capstone remains informal
-- (unbuilt). The chapter cites the two source papers, so it also imports the blueprint's `References`.
import PropertyKindCalculus.Uncertainty
import PropertyKindCalculus.Uncertainty.Ladder
import PropertyKindCalculus.Uncertainty.Convolution
import PropertyKindCalculus.Uncertainty.Sensitivity
import PropertyKindCalculus.Uncertainty.Adequacy.Absorption
import PropertyKindCalculus.Uncertainty.Adequacy.Sterbenz32
import PropertyKindCalculus.Uncertainty.Adequacy.Soundness
import PropertyKindCalculus.Uncertainty.Adequacy.DagBound
import PropertyKindCalculusBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Uncertainty quantification and numerical adequacy" =>

The representation-parametric quantity of R10 carries a model's numbers at whatever carrier a
task needs — `ℝ` to prove, `Float` to run, `FP32` to bound rounding. This chapter puts
that parametricity to work on two questions a metrology model must answer but the calculus so far
does not: _given the uncertainty of the input quantities, what is the uncertainty of the output?_
and _does the floating-point representation of the model lose information that matters at the
scale of those uncertainties?_ Both are developed against one shared, additive descriptor placed
on a quantity — never a change to the carrier tower. The design is recorded in full in the
project's `UNCERTAINTY.md`; this chapter is its blueprint face. Stages 0–3 are built and
CI-checked — the reference layer and worked examples, the GUM and Willink combines, the autograd
sensitivity coefficients, the derivative-free SSPRC pipeline, the five ladder theorems (T1,
cumulant additivity; T2, $`\mathrm{gum} = \mathrm{willink}|_{\kappa_4=0}`; T3, Willink as the
projection of the linearized SSPRC; T4, affine reference equals the mean; T5, convolution adds
cumulants), and the numerical-adequacy layer (the executable analysis carrier, and the theorems A1
absorption, A2 Sterbenz, A3 verdict soundness over `ℝ`); only the *universal* adequacy capstone —
soundness over an arbitrary model and input box — remains *planned*.

# Two orthogonal axes, and why their properties compose

A science model is written *once* as a carrier-polymorphic kernel over `[NumCarrier α]` (the WO1
discipline of the previous chapter). On top of that single source sit _two orthogonal
parametrization axes_:

- *the numeric carrier* $`R` (Axis N) — *how* the numbers are represented: `ℝ` for
  proof, an autograd tape for sensitivity, `FP32`/`RInterval` for numerical adequacy, `CudaT`/
  Tensor for GPU execution, `Float` for a fast CPU reference;
- *the uncertainty descriptor* (Axis U) — *what is known about an input's dispersion*: a
  per-quantity distribution carrying its moments, an inverse cumulative distribution function,
  and a support range.

The value of parametrizing both is that the guarantees *compose* — the same model yields a
proof, a sensitivity, a numerical-adequacy certificate, and a GPU run as different
interpretations, not as four re-implementations:

- *Proof carrier (`ℝ`).* The three uncertainty methods below are one provably nested
  ladder; numerical adequacy is a theorem, not a heuristic.
- *the autograd tape (sensitivity).* Exact sensitivity coefficients $`c_i = \partial f/\partial X_i`
  for the linearized methods, and local surrogates for the sampling method.
- *the uncertainty descriptor (noise).* Measurement uncertainty becomes a first-class,
  composable property of a quantity, in the spirit of the VIM.
- *`FP32`/`RInterval` (no information loss).* A certificate that the model does not silently drop
  a small-but-significant input uncertainty — *at the scale that the same descriptor defines*.
- *`Float`/`CudaT` (fast execution).* The identical model runs, batched, on CPU and GPU.

# The input uncertainty descriptor

:::group "uncertainty"
The uncertainty layer rests on one additive descriptor placed alongside a quantity's magnitude.
It has two faces, matching its two consumers: carrier-parametric *moment data* (what the
linearized methods consume and what the `ℝ`-level theorems are proved about), and a
*sampler* (the inverse-CDF, the single primitive shared by the Monte Carlo and systematic
methods). The support range is carried too, because it is exactly the datum the numerical-adequacy
check needs — the architectural hinge that makes the two halves of this chapter one design.
:::

:::definition "def_uq_momentData" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.MomentData")
The *moment data* of an input: its mean, variance ($`\kappa_2 = u^2`), fourth cumulant
($`\kappa_4 = w`), and third cumulant ($`\kappa_3`, asymmetry). Carrier-parametric — a bare record
over any $`R` — so it exists at `ℝ` for proofs and `Float` for execution alike. The
cumulant constants of the named distributions (normal, uniform, triangular, arc-sine) are the
values tabulated by Willink {Manual.citep willink_evaluation_of_measurement_uncertainty_based_on_moments}[].
:::

:::proof "def_uq_momentData"
Realized. A four-field structure `MomentData R`; the named distributions are *values* built by
smart constructors (`InputDist.normal`, `.uniform`, `.triangular`, `.arcsine`), each filling in
its Willink-Table-1 cumulants — the open-world, values-not-constructors convention the whole
project follows.
:::

:::definition "def_uq_inputDist" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.InputDist")
The *input uncertainty descriptor*: the moment data, an optional rigorous support $`[\mathrm{lo},
\mathrm{hi}]`, and an inverse-CDF sampler. Feeding a random probability to the sampler gives Monte
Carlo; feeding a systematic probability $`(j-\tfrac12)/N` gives the systematic sampling of the
efficient method — one primitive, two methods.
:::

:::proof "def_uq_inputDist"
Realized. `InputDist R` bundles `MomentData` with a `support` and an `invCDF`. The paired
`UncertainQuantity k R` places it alongside a kinded `Quantity k R` as additive metadata, exactly
the pattern R11 used for vector carriers — the carrier tower is untouched.
:::

# The method ladder: GUM ⊂ Willink ⊂ SSPRC

For a model $`Y = f(X_1,\dots,X_k)` with mutually independent, uncertain inputs, three methods
estimate the uncertainty of $`Y`, in increasing fidelity and cost. They are *one* pipeline —
extract each input's contribution, combine the independent contributions, summarize — differing
only in what a contribution is:

- *GUM / law of propagation.* Linearize and combine variances only:
  $$`u_c(Y) = \sqrt{\textstyle\sum_i c_i^2\, u^2(X_i)}, \qquad c_i = \partial f/\partial X_i.`
  A symmetric, Gaussian answer.
- *Willink's cumulants method* {Manual.citep willink_evaluation_of_measurement_uncertainty_based_on_moments}[].
  The same linearization, but combine the _second and fourth_ cumulants,
  $`u_Y^2 = \sum_i c_i^2 u_i^2` and $`w_Y = \sum_i c_i^4 w_i`, form the excess
  $`\gamma_Y = w_Y/u_Y^4`, and read an expanded-uncertainty half-width off the Pearson family via
  the coverage-factor $`k_p(\gamma_Y)`. This recovers the *tail shape* (kurtosis) GUM discards.
- *The SSPRC method* {Manual.citep degenhardt_efficient_alternative_to_monte_carlo}[]. No
  linearization: systematically sample each input, propagate each *separately* through the model,
  reconstruct each input's deviation distribution, and combine them by _convolution_. It
  captures full non-linearity and each input's individual uncertainty contribution, at a fraction
  of the model evaluations a random Monte Carlo needs.

The organizing fact is that these are *provably nested*. All three rest on the additivity of
cumulants under independent summation — Willink's
$`\kappa_r\!\bigl(\sum_j a_j Z_j\bigr) = \sum_j a_j^{\,r}\,\kappa_r(Z_j)`. GUM keeps only
$`\kappa_2`; Willink keeps $`\kappa_2` and $`\kappa_4`; SSPRC's convolution combines *all*
cumulants numerically (Willink himself calls his method "convolution of the components in the
linearized formulation"). So the ladder is a chain of homomorphisms between the methods'
contribution types, and each coarser rung is a *projection* of the finer one — the claim the
ladder theorems below discharge, all five now proved over `ℝ`: T1 and T2 relate GUM and Willink;
T5 shows convolution adds cumulants; T3 uses it to identify Willink with the $`(\kappa_2,\kappa_4)`
truncation of the linearized SSPRC; and T4 pins the SSPRC reference to the mean for an affine model.
The sensitivity coefficients $`c_i` the two linearized rungs need come from the autograd bridge
below, not by hand.

:::definition "def_uq_gum" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.gumStdUnc")
The GUM combined standard uncertainty $`\sqrt{\sum_i c_i^2 u_i^2}`, over a list of sensitivity /
moment-data pairs. The coarsest rung.
:::

:::proof "def_uq_gum"
Realized. `gumStdUnc` folds the $`\kappa_2` contributions. Stage 0 supplied the $`c_i` explicitly;
Stage 1 now sources them from the autograd carrier (one reverse pass over the write-once model at
the input means), leaving this fold unchanged — the Degenhardt example checks the two agree, both
giving $`u_c = 1.662`.
:::

:::definition "def_uq_willink" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.willinkCombine")
Willink's cumulant combine → $`(u_Y, \gamma_Y)`, with the Pearson coverage-factor fits
$`k_{0.95}`, $`k_{0.99}` giving the expanded-uncertainty half-width. The middle rung.
:::

:::proof "def_uq_willink"
Realized. `willinkCombine` combines $`\kappa_2` and $`\kappa_4`; `willinkK95`/`willinkK99` are the
rational Pearson-percentile fits (Willink eqs. 6/7); `willinkHalfWidth99` composes them.
:::

:::definition "def_uq_mcm" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.Mcm.run")
The Monte Carlo *reference* propagator: sample the joint input distribution, push each draw
through the model, report the sample mean and standard uncertainty of the output. Makes no
linearization and no combination assumption, so it is the yardstick the cheaper rungs are
validated against.
:::

:::proof "def_uq_mcm"
Realized. `Mcm.run` over the `Float` carrier, drawing each input through its `invCDF`. Efficiency
is not its job — fidelity is.
:::

:::definition "def_uq_sensitivity" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.Sensitivity.gradient")
The *sensitivity bridge*: the coefficients $`c_i = \partial f/\partial X_i` that GUM and Willink
need are obtained by instantiating the write-once model at an autograd carrier and running one
reverse pass at the input means — not by hand. This is the `extract` step of the two linearized
rungs, and the narrow, precise role of automatic differentiation here, since the SSPRC method is
derivative-free.
:::

:::proof "def_uq_sensitivity"
Realized (Stage 1, `Sensitivity.gradient`). The model kernel — the *same* source run at `Float`
for Monte Carlo — is interpreted at TorchLean's reverse-mode `TapeBuilder` carrier; each input
enters as a differentiable leaf and `backwardScalar` reads every $`c_i` from one pass, with no
model rewrite. On the Degenhardt fictive model the bridge returns $`(c_1, c_2, c_3) = (5, 5, 2.25)`
and reproduces the GUM $`u_c = 1.662` exactly (the `DegenhardtSensitivity` example). The op class is
`exp`/`log`/`sqrt` with arithmetic; trigonometric models await tape VJP nodes.
:::

:::theorem "thm_uq_cumulant_additivity" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.willinkCumulants_cons")
*Cumulant additivity (T1).* Combining independent contributions adds their cumulants: the
measurand's combined $`(\kappa_2, \kappa_4)` for an input list is the head input's contribution
plus the combined cumulants of the tail. Equivalently the contribution type is a commutative monoid
under `combine` — *and that it is a monoid is the independence assumption made explicit*. This is
Willink's $`\kappa_r(\sum_j a_j Z_j) = \sum_j a_j^{\,r}\,\kappa_r(Z_j)` for $`r \in \{2, 4\}`, the
fact the whole ladder rests on.
:::

:::proof "thm_uq_cumulant_additivity"
Realized over `ℝ`: `willinkCumulants_cons`, with the `Cumulants` `AddCommMonoid` instance (the
`combine`/`empty` monoid laws) providing the associativity/commutativity/unit that make the
independent fold well-defined.
:::

:::theorem "thm_uq_gum_is_willink" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.gum_eq_willink_of_normal") (tags := "capstone")
*GUM is the $`\kappa_2`-projection of Willink (T2).* The second cumulant of the Willink combine is
exactly the GUM combined variance, so $`\mathrm{gum}` is the cumulant-forgetting coarsening of
$`\mathrm{willink}`. And when every input's fourth cumulant vanishes ($`w_i = 0`, as for normal
inputs) the excess $`\gamma_Y` is zero, the Pearson coverage factor collapses to the standard-normal
percentile ($`k_{0.95}(0) = 1.96`), and the Willink expanded-uncertainty half-width equals GUM's
Gaussian half-width $`1.96\,u_c`. Uses {uses "def_uq_gum"}[the GUM combine] and
{uses "def_uq_willink"}[Willink's combine], resting on {uses "thm_uq_cumulant_additivity"}[cumulant additivity].
:::

:::proof "thm_uq_gum_is_willink"
Realized over `ℝ` (theorem T2 of `UNCERTAINTY.md`, `gum_eq_willink_of_normal`; `#print axioms`
shows it sorry-free — no `sorryAx`). Two parts: `willinkCumulants_kappa2` — the variance fold is
literally the GUM one — and the shape collapse $`w_i = 0 \Rightarrow \gamma_Y = 0 \Rightarrow k_p`
is the standard-normal percentile, so the half-widths coincide. Establishes the top edge of the
ladder; the lower edge — that Willink is the fourth-cumulant truncation of the linearized SSPRC,
because convolution adds cumulants — is theorem T3 below.
:::

# The SSPRC method and the lower ladder rungs

The two linearized rungs replace the model by its gradient at the input means. The *SSPRC method*
{Manual.citep degenhardt_efficient_alternative_to_monte_carlo}[] does no such thing: it keeps the
full model but evaluates it *cheaply* by sampling each input systematically and propagating each
one separately. Its four steps are systematic sampling (each input at the equidistant probabilities
$`P_j = (j-\tfrac12)/N_i` through its inverse CDF), separated propagation (vary one input, hold the
rest at their means, form the deviations $`a_{i,j} = f(\dots,x_{i,j},\dots) - R` from the reference
$`R = f(E(X))`), reconstruction of each input's deviation distribution, and *convolution* of those
distributions into the measurand's. Because the sample counts *add* ($`N_s = \sum_i N_i`) rather
than multiply, it reaches Monte Carlo fidelity at a fraction of the model evaluations — and, keeping
the full model, it recovers the *non-linear* mean the linearized rungs cannot.

:::definition "def_uq_ssprc" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.Ssprc.run")
The *SSPRC pipeline*: from the model, the input descriptors, and a per-input sample count, produce the
combined $`(E(Y), u(Y))` by systematic sampling, separated propagation, and convolution — a
derivative-free method whose evaluation budget is additive in the inputs.
:::

:::proof "def_uq_ssprc"
Realized (Stage 2, `Ssprc.run`) over the `Float` carrier. `run` reads $`E(Y) = R + \sum_i E(A_i)` and
$`\mathrm{Var}(Y) = \sum_i \mathrm{Var}(A_i)` off the per-input deviation distributions (means and
variances add under convolution, so the combinatorial convolution need not be materialized);
`runConv` performs the actual discrete convolution and agrees, cross-checking the engine. On the
Degenhardt fictive model with 100 systematic samples per input — 300 evaluations against the Monte
Carlo reference's 20 000 — it returns $`E(Y) = 11.5875` (recovering the non-linear $`+0.3375` offset
that GUM cannot see) and $`u(Y) \approx 1.69`, closer to the Monte Carlo value than GUM's 1.662 (the
`DegenhardtSsprc` example).
:::

:::theorem "thm_uq_convolution_cumulants" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.Dist.cumulantsOf_conv")
*Convolution adds cumulants (T5).* For independent centered probability distributions the second and
fourth cumulants are additive under convolution: $`\kappa_r(d_1 \star d_2) = \kappa_r(d_1) +
\kappa_r(d_2)` for $`r \in \{2,4\}`. Equivalently the cumulant map is a homomorphism from the
convolution operation onto the `Cumulants` monoid. This is the mathematical bridge under T3.
:::

:::proof "thm_uq_convolution_cumulants"
Realized over `ℝ` (`Convolution.lean`): convolution is *defined* as the distribution of the sum of
independent contributions — every pairwise sum weighted by the product — and the additivity is
*proved* from the factorization of the joint expectation (`kappa2_conv`, `kappa4_conv`; the
$`-3\,E[X^2]^2` correction is exactly what cancels the cross term $`6\,E[X^2]E[Y^2]` in the fourth
moment of the sum), not assumed. Sorry-free (`#print axioms` → `propext`, `Classical.choice`,
`Quot.sound`).
:::

:::theorem "thm_uq_ssprc_willink" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.cumulantsOf_combinedDeviation") (tags := "capstone")
*Willink is the $`(\kappa_2,\kappa_4)`-projection of the linearized SSPRC (T3).* If each input's
deviation distribution is a centered probability distribution realizing its declared moments, then
the cumulants of the convolved combined deviation are *exactly* the Willink combined cumulants
$`(\sum_i c_i^2 u_i^2,\ \sum_i c_i^4 w_i)`. So convolving the separately-propagated inputs and
truncating at the fourth cumulant reproduces $`\mathrm{willink}` — the lower edge of the ladder,
whose upper edge is {uses "thm_uq_gum_is_willink"}[T2]. Rests on
{uses "thm_uq_convolution_cumulants"}[convolution adding cumulants].
:::

:::proof "thm_uq_ssprc_willink"
Realized over `ℝ` (`cumulantsOf_combinedDeviation`): induction over the input list, each step the
scaling law $`\kappa_r(c_i \cdot Z_i) = c_i^{\,r}\,\kappa_r(Z_i)` followed by the convolution
homomorphism T5, landing on `willinkCumulants` term by term. Together with T2 this closes the ladder
$`\mathrm{GUM} \subset \mathrm{Willink} \subset \mathrm{SSPRC}` as a chain of homomorphisms
(the `SsprcNesting` example applies it to concrete distributions, pinning $`(\kappa_2,\kappa_4) =
(41, -1186)`). Sorry-free.
:::

:::theorem "thm_uq_affine_reference" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.combinedDeviation_isCentered")
*The SSPRC reference equals the mean for an affine model (T4).* When every input's deviation
distribution is centered — the case of a linear/affine model — the combined deviation is centered, so
the reference value $`R = f(E(X))` equals $`E(Y)`. The non-linearity signature $`E(Y) - R` is exactly
the non-vanishing of $`\sum_i c_i\,E(Z_i)` when a deviation distribution is *not* centered — the gap
the Degenhardt fictive example exhibits (0.3375) and the linearized rungs structurally miss.
:::

:::proof "thm_uq_affine_reference"
Realized over `ℝ` (`combinedDeviation_isCentered`, with `mean_combinedDeviation` giving the general
gap $`\sum_i c_i\,E(Z_i)`): the mean of a convolution is the sum of the means (weighted by the unit
totals), so a fold of centered contributions is centered. Sorry-free.
:::

# Numerical adequacy of the floating-point representation

A floating-point representation is *numerically adequate* for a model, given the input ranges and
uncertainties, exactly when evaluating it loses no information significant *at the scale of those
uncertainties*. The qualifier is what makes the notion checkable, and it is why this half of the
chapter shares Axis U's descriptor: the yardstick is the very $`c_i\,u_i` and support the
uncertainty methods already carry. The textbook failure — adding a small floating-point number to
a large one and losing the small one — becomes precise: an input whose uncertainty contribution
$`c_i\,u_i` falls below half a unit in the last place of the accumulated sum is *numerically
invisible*, a silent corruption of the uncertainty result. Its exact-cancellation dual (a
difference of near-equal quantities is exact by Sterbenz, yet amplifies *relative* uncertainty)
is the same two views — floating-point and uncertainty — meeting again.

The idiomatic realization is *numerical adequacy as a carrier*: because the model is WO1 over
`[NumCarrier α]`, instantiating it at an analysis carrier that tracks each value's magnitude and
carried uncertainty, and checks each operation for swamping and cancellation, yields the adequacy
report *for free* — no model rewrite. The check is sound because the swamping threshold is exactly
half a unit in the last place, a fact proved on the rounding grid over `ℝ` and grounded in
TorchLean's binary32 `FP32` unit-in-the-last-place lemmas (`Adequacy.Fp32Grounding`, which imports
the genuine — `noncomputable` — Flocq port); the executable carrier computes the same threshold over
`Float`.

:::definition "def_uq_adequacy" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.Adequacy")
The *adequacy analysis carrier*: a value carrying its magnitude, its propagated uncertainty, and an
accumulated report of adequacy violations. As a `NumCarrier`, any write-once model instantiates at it
and is analyzed for floating-point information loss with no rewrite — the *runtime certificate*, the
pragmatic first target of the numerical-adequacy layer.
:::

:::proof "def_uq_adequacy"
Realized (Stage 3, `Adequacy`) over the `Float` carrier. Addition runs a swamping check (the
smaller-magnitude operand's uncertainty against half the sum's ulp), subtraction a cancellation check
(relative uncertainty reaching 100%); the `NumCarrier` instance closes with these plus the arithmetic
and `MathCarrier` fields, so the *same* kernel the earlier rungs evaluate runs here to emit the
report. The `AdequacySwamping` example flags a large-accumulator model and certifies its
small-accumulator variant clean — one WO1 kernel, checked for free.
:::

:::theorem "thm_uq_absorption" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.Adequacy.absorb")
*Absorption (A1).* On the rounding grid of spacing `u` (a ulp), a representable value perturbed by
strictly less than half a ulp rounds back unchanged: $`|y| < u/2 \Rightarrow
\mathrm{round}_u(x + y) = x`. The perturbation carries *no* information into the result — floating-point
swamping made precise — and its converse (`resolve`) shows a perturbation of at least half a ulp does
move the result, so half a ulp is the *exact* absorption threshold.
:::

:::proof "thm_uq_absorption"
Realized over `ℝ` (`Adequacy.Absorption.absorb`, with `resolve` the converse): on the uniform grid
`u·ℤ`, `round_u(x+y) = u·round((x+y)/u)`, and `|y| < u/2` places `(x+y)/u` within a half-integer of
`x/u`, so it rounds to `x/u`. The binary32 realization is TorchLean's `neuralRound` nearest-point
optimality and `neuralUlp` (`Adequacy.Fp32Grounding`). Sorry-free.
:::

:::theorem "thm_uq_sterbenz" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.Adequacy.flx_sterbenz")
*Sterbenz (A2).* The difference of two positive floating-point numbers representable at precision
`p` that lie within a factor of two of each other ($`y \le x \le 2y`) is *itself* representable at
precision `p` — so near-equal subtraction is *exact*, introducing no rounding error. Its dual is the
uncertainty hazard: that exact difference can have *relative* uncertainty ≥ 100% (`relUnc_amplifies`).
:::

:::proof "thm_uq_sterbenz"
Realized over `ℝ` (`Adequacy.Sterbenz32.flx_sterbenz`), the real-number analogue of TorchLean's
`neural_generic_format_FLX_sterbenz`: align both operands to the smaller exponent, and the factor-of-two
condition bounds the difference's mantissa below `2^p`. `sub_exact_on_grid` gives the grid form (the
difference rounds to itself). Sorry-free. Lifting this to the FLT/`fexp32` format binary32 actually
uses (gradual underflow) is a follow-up sub-stage, and a TorchLean PR.
:::

:::theorem "thm_uq_adequacy_verdict" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.Adequacy.verdict_sound") (tags := "capstone")
*Adequacy verdict soundness (A3).* At an addition site, the carrier's flag — the operand's
uncertainty is below half the accumulator's ulp — holds *if and only if* the contribution is
genuinely lost (the rounded sum is unchanged by that uncertainty). So the flag is *sound* (flag ⟹
lost) and *complete* (lost ⟹ flag): the theorem that makes the carrier's report trustworthy. Rests
on {uses "thm_uq_absorption"}[absorption and its converse].
:::

:::proof "thm_uq_adequacy_verdict"
Realized over `ℝ` (`Adequacy.Soundness.verdict_sound`): the forward direction is A1 `absorb`, the
reverse is the contrapositive of `resolve`, giving the biconditional `unc < ½ ulp ↔ fl(s + unc) = s`
for a representable accumulator and an uncertainty within one ulp. The `AdequacyLadder` example applies
it to concrete values with a sorry-free axiom profile. This is the per-site soundness that grounds the
runtime carrier.
:::

:::theorem "thm_uq_adequacy_soundness" (parent := "uncertainty") (lean := "PropertyKindCalculus.Uncertainty.Adequacy.dag_fp32_box_faithful") (tags := "capstone")
*Universal adequacy soundness (A3′, the capstone).* Abstract a write-once model as a binary32
evaluation DAG of `+`/`−`. For *any* two inputs — in particular every input in a box around a nominal
one — the `FP32`-computed measurand's *variation* reproduces the exact `ℝ`-computed variation up to a
proven, DAG-additive rounding budget; and when no site rounds anywhere (flag-free — no absorption at
any addition, every subtraction in the Sterbenz {uses "thm_uq_sterbenz"}[A2] regime), the bound
collapses to *equality*. This lifts the per-site verdict {uses "thm_uq_adequacy_verdict"}[A3] across a
whole evaluation, and is the theorem that binds the layer to R10's exec/spec refinement.
:::

:::proof "thm_uq_adequacy_soundness"
Realized over `ℝ`/`FP32` (Stage 3.1, `Adequacy.DagBound`). The forward-error accumulation
`dag_fp32_error_bound` composes the per-operation half-ulp bounds
(`Adequacy.Fp32Grounding.{add32,sub32}_within_half_ulp`, the genuine `FP32.{add,sub}_abs_error`) with
the triangle inequality along the DAG; applying it at both inputs and one more triangle step gives the
box-faithfulness bound `dag_fp32_box_faithful`, and `dag_fp32_box_exact_of_flagFree` is the flag-free
equality. Sorry-free (`#print axioms` → `[propext, Classical.choice, Quot.sound]`), instantiated on
concrete DAGs in the `AdequacyDag` example. Honest scope: the DAG covers `+`/`−` (the operations
A1/A2/A3 cover); extending to `×`/`÷` and the executable-carrier bridge are sub-stages 3.2–3.3 in
`UNCERTAINTY.md` §6.
:::

# Worked examples (checked facts)

Nine examples reproduce a headline number (or a theorem) as a `#guard`, so the
`UncertaintyExamples` library building under CI is what makes the claims true rather than
asserted — the project's reflection-tests discipline applied to metrology. The first two are the
Stage-0 reference numbers; the next two are the Stage-1 autograd and ladder facts; the next two are
the Stage-2 SSPRC pipeline and its ladder theorems; the last three are the Stage-3 adequacy carrier,
its per-site theorems, and the Stage-3.1 DAG capstone A3′.

- `PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive` — the non-linear fictive model
  $`Y = (X_1 + X_2^2)\,X_3` of Degenhardt
  {Manual.citep degenhardt_efficient_alternative_to_monte_carlo}[] §3.1, with a normal, a uniform,
  and a triangular input. The Monte Carlo reference gives $`E(Y) \approx 11.60`,
  $`u(Y) \approx 1.70` (matching the paper's $`11.5875`, $`1.691`); the reference value
  $`R = f(E(X)) = 11.25`, and the gap $`E(Y) - R = 0.34` is the non-linearity signature of the
  $`X_2^2` term — exactly what the linearized rungs cannot see. The GUM cross-check gives
  $`u_c \approx 1.662`, visibly *under* the Monte Carlo value: the linearization drops the
  curvature, which is the whole motivation for the higher rungs.
- `PropertyKindCalculus.UncertaintyExamples.WillinkGaugeBlock` — the gauge-block calibration of
  Willink {Manual.citep willink_evaluation_of_measurement_uncertainty_based_on_moments}[] Table 4
  (the GUM example H.1), evaluated by the cumulants method: combining the six error variables'
  variances and fourth cumulants gives $`u_Y = 33.4\,\mathrm{nm}`, excess $`\gamma_Y = 0.124`, and
  a 99% expanded-uncertainty half-width $`h_{0.99} = 87.6\,\mathrm{nm}` — 5% narrower than the GUM
  procedure's 93 nm at the same coverage, because the (mostly negative) fourth cumulants pull the
  tails of the output toward normal. That narrowing *is* the difference between the GUM rung and
  the Willink rung, reproduced as a checked number.
- `PropertyKindCalculus.UncertaintyExamples.DegenhardtSensitivity` — the Stage-1 autograd bridge on
  the *same* fictive kernel: interpreting it at the reverse-mode tape carrier returns the
  sensitivity coefficients $`(c_1, c_2, c_3) = (5, 5, 2.25)` to machine precision (matching the
  hand-computed $`\partial Y/\partial X_i` at the means), and feeding them through `gumStdUnc`
  reproduces $`u_c = 1.662` exactly — the write-once model differentiated with no rewrite.
- `PropertyKindCalculus.UncertaintyExamples.LadderNesting` — T1/T2 applied to a concrete
  all-Gaussian term list over `ℝ` (`gum = willink|κ₄=0` as a closed proof term, `#print axioms`
  confirming no `sorryAx`), together with the executable `Float` shadow of the collapse: for
  normal-only inputs the Willink 95% half-width is exactly $`1.96\,u_c`.
- `PropertyKindCalculus.UncertaintyExamples.DegenhardtSsprc` — the Stage-2 SSPRC pipeline on the
  *same* fictive model {Manual.citep degenhardt_efficient_alternative_to_monte_carlo}[]: 100
  systematic samples per input (300 model evaluations against the Monte Carlo reference's 20 000, a
  factor $`\approx 67`) recover $`E(Y) = 11.5875` — including the non-linear $`+0.3375` offset the
  linearized rungs cannot produce — and $`u(Y) \approx 1.69`, closer to the Monte Carlo value than
  GUM's 1.662; the actual convolution (`runConv`) reproduces the moment read-off to machine precision.
- `PropertyKindCalculus.UncertaintyExamples.SsprcNesting` — the T3/T4/T5 ladder theorems applied to
  two concrete centered distributions over `ℝ`: convolution adds their cumulants (T5), the convolved
  combined deviation has exactly the Willink cumulants $`(41, -1186)` (T3), and an all-centered
  (affine) input list yields a centered combined deviation, so $`E(Y) = R` (T4) — with `#print axioms`
  confirming no `sorryAx`.
- `PropertyKindCalculus.UncertaintyExamples.AdequacySwamping` — the executable `Adequacy` carrier on
  two write-once kernels: `bias + x` with a small input uncertainty is flagged *swamped* under a large
  accumulator ($`10^8`, where $`\tfrac12\,\mathrm{ulp}_{32} = 4 > 1`) and certifies *clean* under a
  small one ($`100`); `a − b` of near-equal uncertain operands is flagged *catastrophic cancellation*
  (relative uncertainty ≥ 100%) and certifies clean when the operands are well separated — the same
  kernel, checked for free at each configuration.
- `PropertyKindCalculus.UncertaintyExamples.AdequacyLadder` — the adequacy theorems A1 (absorption,
  $`\mathrm{round}_8(80+1) = 80`), A2 (Sterbenz, $`3 - 2` of two `FLX 24` numbers is `FLX 24`), and A3
  (the verdict biconditional) applied to concrete values over `ℝ`, with `#print axioms` confirming no
  `sorryAx`.
- `PropertyKindCalculus.UncertaintyExamples.AdequacyDag` — the Stage-3.1 capstone A3′ instantiated on
  concrete model DAGs (a three-input accumulator, an add/sub variant, a deeper five-input tree): the
  `FP32` measurand's variation over an input box equals the `ℝ` one up to the DAG-additive rounding
  budget, and *exactly* when no site rounds (flag-free) — again with `#print axioms` confirming no
  `sorryAx`.
