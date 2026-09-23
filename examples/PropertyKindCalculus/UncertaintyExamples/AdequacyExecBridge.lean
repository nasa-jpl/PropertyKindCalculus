/-
# Worked example — Stage 3.3: the executable↔spec adequacy bridge

Stages 3–3.2 proved the adequacy verdicts (A1 absorption, A2 Sterbenz, A3 soundness) over `ℝ` and,
for A2, over the genuine binary32 format. But the *runtime* `Adequacy` carrier computes over Lean's
opaque host `Float`, which no theorem can certify. Stage 3.3 closes the gap on TorchLean's
**computable** `IEEE32Exec` model, whose every operation is provably `round32` of the exact real
result. This example shows both sides of that bridge:

  * **Certified (symbolic).** `exec_ulp` — when the executable ULP query answers
    (`ulpExp? x = some k`; it answers on exactly the finite fragment, `none` on NaNs and
    infinities), `2^k` reproduces the spec `ulp32` of the decoded value; and `exec_verdict` — the
    kernel's absorption verdict `absorbs s δ` *certifies* the specification's absorption
    `round32 (toReal s + toReal δ) = toReal s`. These hold for *every* finite decode (symbolic in
    `s`, `δ`), and the axiom prints confirm no `sorryAx`.
  * **Executable (concrete).** The same `ulpExp?`/`absorbs` are *run* on concrete float32 bit
    patterns with `#guard` — unlike the `noncomputable` `FP32`/`round32` spec, `IEEE32Exec` reduces
    in the kernel. At `2²⁵` the ULP is `4` (`ulpExp? = some 2`), so a perturbation of `1` (below the
    half-ULP `2`) is absorbed while a perturbation of `4` is not; at `10⁸` the ULP is `8`
    (`ulpExp? = some 3`), so `1` is absorbed and `8` is not. These are exactly the
    swamping/adequacy decisions of `AdequacySwamping`, now taken by a verdict that `exec_verdict`
    proves equal to the `round32` specification.

Mathlib- and TorchLean-backed.
-/

module

public import PropertyKindCalculus.Uncertainty.Adequacy.ExecBridge
meta import PropertyKindCalculus.Uncertainty.Adequacy.ExecBridge

@[expose] public section Blanket

namespace PropertyKindCalculus.UncertaintyExamples.AdequacyExecBridge

open PropertyKindCalculus.Uncertainty.Adequacy
open TorchLean.Floats
open TorchLean.Floats.IEEE754
open TorchLean.Floats.IEEE754.IEEE32Exec
open FloatLib.Floats (ExecFloat)
open FloatLib.Floats.ExecFloat.Binary (isFinite toModel)
open FloatLib.Floats.Formats.Flocq (bpow)
open FloatLib.Numerics (binaryRadix)

/-! ## Certified: the executable check equals the specification (symbolic, finite fragment) -/

/-- **Executable ULP = specified ULP.** When the query answers `k`, `2^k` is exactly
`ulp32 (toReal x)`. -/
theorem exec_ulp {x : ExecFloat.Binary 8 23} {k : Int} (hk : ulpExp? x = some k) :
    bpow binaryRadix k = ulp32 (toModel x).toReal :=
  exec_ulp_grounds hk

/-- **Executable verdict certifies the spec.** When the kernel reports `δ` absorbed into `s`, the
exact real sum rounds back to `toReal s` under the binary32 specification `round32`. -/
theorem exec_verdict {s δ : ExecFloat.Binary 8 23} {ds dδ : FloatLib.Numerics.Dyadic}
    (hs : (toModel s).toDyadic? = some ds) (hδ : (toModel δ).toDyadic? = some dδ)
    (hfin : isFinite (ExecFloat.add s δ) = true) (hverdict : absorbs s δ = true) :
    round32 ((toModel s).toReal + (toModel δ).toReal) = (toModel s).toReal :=
  exec_verdict_sound hs hδ hfin hverdict

/-! ## Executable: the verdict actually computes (concrete bit patterns) -/

-- At `2²⁵`, ULP = 4 = 2², half-ULP = 2.
#guard ulpExp? (33554432 : ExecFloat.Binary 8 23) = some 2
#guard absorbs (33554432 : ExecFloat.Binary 8 23) 1 = true    -- 1 < 2  → absorbed
#guard absorbs (33554432 : ExecFloat.Binary 8 23) 4 = false   -- 4 ≥ 2  → survives

-- At `10⁸`, ULP = 8 = 2³, half-ULP = 4 (the `AdequacySwamping` accumulator scale).
#guard ulpExp? (100000000 : ExecFloat.Binary 8 23) = some 3
#guard absorbs (100000000 : ExecFloat.Binary 8 23) 1 = true   -- 1 < 4  → absorbed (swamped)
#guard absorbs (100000000 : ExecFloat.Binary 8 23) 8 = false  -- 8 ≥ 4  → survives

/-! ## Sorry-free — the axiom profile of the Stage-3.3 bridge theorems -/

/-- info: 'PropertyKindCalculus.UncertaintyExamples.AdequacyExecBridge.exec_ulp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exec_ulp
/-- info: 'PropertyKindCalculus.UncertaintyExamples.AdequacyExecBridge.exec_verdict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exec_verdict

end PropertyKindCalculus.UncertaintyExamples.AdequacyExecBridge

end Blanket
