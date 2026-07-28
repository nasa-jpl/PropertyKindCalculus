/-
# Worked example — Stage 3.3: the executable↔spec adequacy bridge

Stages 3–3.2 proved the adequacy verdicts (A1 absorption, A2 Sterbenz, A3 soundness) over `ℝ` and,
for A2, over the genuine binary32 format. But the *runtime* `Adequacy` carrier computes over Lean's
opaque host `Float`, which no theorem can certify. Stage 3.3 closes the gap on TorchLean's
**computable** `IEEE32Exec` model, whose every operation is provably `round₃₂` of the exact real
result. This example shows both sides of that bridge:

  * **Certified (symbolic).** `exec_ulp` — when the executable ULP query answers
    (`ulpExp? x = some k`; it answers on exactly the finite fragment, `none` on NaNs and
    infinities), `2^k` reproduces the spec `ulp₃₂` of the decoded value; and `exec_verdict` — the
    kernel's absorption verdict `absorbs s δ` *certifies* the specification's absorption
    `round₃₂ (toReal s + toReal δ) = toReal s`. These hold for *every* finite decode (symbolic in
    `s`, `δ`), and the axiom prints confirm no `sorryAx`.
  * **Executable (concrete).** The same `ulpExp?`/`absorbs` are *run* on concrete float32 bit
    patterns with `#guard` — unlike the `noncomputable` `FP32`/`round₃₂` spec, `IEEE32Exec` reduces
    in the kernel. At `2²⁵` the ULP is `4` (`ulpExp? = some 2`), so a perturbation of `1` (below the
    half-ULP `2`) is absorbed while a perturbation of `4` is not; at `10⁸` the ULP is `8`
    (`ulpExp? = some 3`), so `1` is absorbed and `8` is not. These are exactly the
    swamping/adequacy decisions of `AdequacySwamping`, now taken by a verdict that `exec_verdict`
    proves equal to the `round₃₂` specification.

Mathlib- and TorchLean-backed.
-/
import PropertyKindCalculus.Uncertainty.Adequacy.ExecBridge

namespace PropertyKindCalculus.UncertaintyExamples.AdequacyExecBridge

open PropertyKindCalculus.Uncertainty.Adequacy
open TorchLean.Floats
open TorchLean.Floats.IEEE754
open TorchLean.Floats.IEEE754.IEEE32Exec

/-! ## Certified: the executable check equals the specification (symbolic, finite fragment) -/

/-- **Executable ULP = specified ULP.** When the query answers `k`, `2^k` is exactly
`ulp₃₂ (toReal x)`. -/
theorem exec_ulp {x : IEEE32Exec} {k : Int} (hk : ulpExp? x = some k) :
    neuralBpow binaryRadix k = ulp₃₂ (toReal x) :=
  exec_ulp_grounds hk

/-- **Executable verdict certifies the spec.** When the kernel reports `δ` absorbed into `s`, the
exact real sum rounds back to `toReal s` under the binary32 specification `round₃₂`. -/
theorem exec_verdict {s δ : IEEE32Exec} {ds dδ : TorchLean.Floats.IEEE754.IEEE32Exec.Dyadic}
    (hs : toDyadic? s = some ds) (hδ : toDyadic? δ = some dδ)
    (hfin : isFinite (add s δ) = true) (hverdict : absorbs s δ = true) :
    round₃₂ (toReal s + toReal δ) = toReal s :=
  exec_verdict_sound hs hδ hfin hverdict

/-! ## Executable: the verdict actually computes (concrete bit patterns) -/

-- At `2²⁵`, ULP = 4 = 2², half-ULP = 2.
#guard ulpExp? (33554432 : IEEE32Exec) = some 2
#guard absorbs (33554432 : IEEE32Exec) 1 = true    -- 1 < 2  → absorbed
#guard absorbs (33554432 : IEEE32Exec) 4 = false   -- 4 ≥ 2  → survives

-- At `10⁸`, ULP = 8 = 2³, half-ULP = 4 (the `AdequacySwamping` accumulator scale).
#guard ulpExp? (100000000 : IEEE32Exec) = some 3
#guard absorbs (100000000 : IEEE32Exec) 1 = true   -- 1 < 4  → absorbed (swamped)
#guard absorbs (100000000 : IEEE32Exec) 8 = false  -- 8 ≥ 4  → survives

/-! ## Sorry-free — the axiom profile of the Stage-3.3 bridge theorems -/

#print axioms exec_ulp
#print axioms exec_verdict

end PropertyKindCalculus.UncertaintyExamples.AdequacyExecBridge
