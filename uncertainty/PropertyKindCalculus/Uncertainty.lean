/-
# `PropertyKindCalculus.Uncertainty` — Stage 0 of the uncertainty workstream

The exportable root of the uncertainty library. See `UNCERTAINTY.md` for the full plan.

Stage 0 delivers the reference layer:
  * `Carriers`         — `NumCarrier Float`, so a WO1 `[NumCarrier α]` model runs at `Float`.
  * `Sampling`         — PRNG + inverse-CDF quantiles (the primitive shared by MCM and SSPRC).
  * `InputDist`        — the carrier-parametric moment data + the input descriptor, with the
                         named distributions (normal/uniform/triangular/arc-sine) as values.
  * `UncertainQuantity`— a kinded quantity paired with its `InputDist`.
  * `Mcm`              — the Monte Carlo reference propagator.
  * `Combine`          — the linearized GUM and Willink moment-combine methods.
  * `Evidence`         — the orthogonal combination: evidence *across* repeated measurements of one
                         measurand. The GUM 4.2 Type A evaluation from `n` indications, the `t`-based
                         coverage factor (Table G.2), Welch–Satterthwaite effective degrees of
                         freedom, and inverse-variance pooling — with the Type B → Type A transition
                         as a *displacement*, since pooling a statement of ignorance with data would
                         let an asserted half-width anchor the estimate forever.
  * `Ssprc`            — the derivative-free SSPRC pipeline (systematic sampling, separated
                         propagation, empirical deviation distributions, discrete convolution).
  * `Allocation`       — sensitivity-driven per-input sample allocation: split an SSPRC budget by
                         each input's uncertainty contribution `|cᵢ|·uᵢ` (Stage 4, `ns` for `run`).
  * `Adequacy`         — the executable numerical-adequacy carrier (Stage 3 runtime certificate):
                         a WO1 `[NumCarrier α]` model run over it flags floating-point swamping and
                         catastrophic cancellation at the scale of the input uncertainties.

Worked, paper-grounded examples live in the `UncertaintyExamples` library.
Mathlib- and TorchLean-free.
-/
import PropertyKindCalculus.Uncertainty.Carriers
import PropertyKindCalculus.Uncertainty.Sampling
import PropertyKindCalculus.Uncertainty.InputDist
import PropertyKindCalculus.Uncertainty.UncertainQuantity
import PropertyKindCalculus.Uncertainty.Mcm
import PropertyKindCalculus.Uncertainty.Combine
import PropertyKindCalculus.Uncertainty.Evidence
import PropertyKindCalculus.Uncertainty.Ssprc
import PropertyKindCalculus.Uncertainty.Allocation
import PropertyKindCalculus.Uncertainty.Adequacy
