import Verso
import VersoManual
import VersoBlueprint
-- Every realized node below is linked to a real declaration via `(lean := "PropertyKindCalculus.…")`
-- and is elaborated for its proved/`sorry` status, so the chapter imports the Stage-0 uncertainty
-- library, the Stage-1 `Ladder` (T1/T2 over `ℝ`), and the Stage-1 `Sensitivity` autograd bridge —
-- the last pulls TorchLean into the blueprint build, deliberately, so the sensitivity coefficients
-- are a formal lean-linked node rather than prose. Only the SSPRC method and the numerical-adequacy
-- capstone remain informal (unbuilt). The chapter cites the two source papers, so it also imports
-- the blueprint's `References`.
import PropertyKindCalculus.Uncertainty
import PropertyKindCalculus.Uncertainty.Ladder
import PropertyKindCalculus.Uncertainty.Sensitivity
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
project's `UNCERTAINTY.md`; this chapter is its blueprint face. Stages 0 and 1 are built and
CI-checked — the reference layer and worked examples, the GUM and Willink combines, the autograd
sensitivity coefficients, and the first two ladder theorems (T1, cumulant additivity; T2,
$`\mathrm{gum} = \mathrm{willink}|_{\kappa_4=0}`); the SSPRC method, the remaining ladder rungs, and
the numerical-adequacy capstone are *planned*.

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
ladder theorems below discharge (T1 and T2 proved over `ℝ`; T3, linking Willink to the linearized
SSPRC, planned with the sampling method). The sensitivity coefficients $`c_i` the two linearized
rungs need come from the autograd bridge below, not by hand.

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
because convolution adds cumulants — is the planned theorem T3.
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
`[NumCarrier α]`, instantiating it at an analysis carrier that tracks each value's magnitude
interval and carried uncertainty, and checks each operation for swamping and cancellation, yields
the adequacy report *for free* — no model rewrite. The check is sound because the ranges come from
TorchLean's proven-sound interval arithmetic and the swamping bound from its `FP32` unit-in-the-
last-place lemmas.

:::theorem "thm_uq_adequacy_soundness" (parent := "uncertainty") (tags := "capstone, planned") (effort := "large") (priority := "high")
*Adequacy soundness.* If the analysis carrier reports no absorption or harmful cancellation on an
input box, then for every input in that box the `FP32`-computed measurand's uncertainty equals the
`ℝ`-computed one up to a proven bound. This turns "no loss of information" into a proof
rather than a hope, and it is the theorem that binds the numerical-adequacy layer to R10's
exec/spec refinement.
:::

:::proof "thm_uq_adequacy_soundness"
Planned (capstone A3 of `UNCERTAINTY.md`). Composes three pieces: the soundness of the interval
carrier's enclosures, the per-operation `FP32` rounding bounds, and an absorption theorem (A1)
under a magnitude gap — the last to be authored from TorchLean's `neuralRound` nearest-point
optimality and unit-in-the-last-place lemmas, together with an `FP32` Sterbenz instance (A2)
transported from the proven unbounded-exponent case.
:::

# Worked examples (checked facts)

Four examples reproduce a headline number (or a theorem) as a `#guard`, so the
`UncertaintyExamples` library building under CI is what makes the claims true rather than
asserted — the project's reflection-tests discipline applied to metrology. The first two are the
Stage-0 reference numbers; the last two are the Stage-1 autograd and ladder facts.

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
