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

Worked, paper-grounded examples live in the `UncertaintyExamples` library.
Mathlib- and TorchLean-free.
-/
import PropertyKindCalculus.Uncertainty.Carriers
import PropertyKindCalculus.Uncertainty.Sampling
import PropertyKindCalculus.Uncertainty.InputDist
import PropertyKindCalculus.Uncertainty.UncertainQuantity
import PropertyKindCalculus.Uncertainty.Mcm
import PropertyKindCalculus.Uncertainty.Combine
