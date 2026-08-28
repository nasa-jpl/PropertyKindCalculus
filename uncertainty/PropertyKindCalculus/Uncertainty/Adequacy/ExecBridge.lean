/-
`PropertyKindCalculus.Uncertainty.Adequacy.ExecBridge` — the **executable↔spec bridge** for the
adequacy layer (Stage 3.3, `UNCERTAINTY.md` §6).

The adequacy story so far has two mirrored halves that never met in a proof:

  * a **specification** over `ℝ` — `Grid`/`Absorption`/`Soundness` (A1/A3) and `Fp32Grounding`
    (the genuine binary32 `round32`/`ulp32`), all `noncomputable`; and
  * an **executable** carrier — `Adequacy.lean`'s swamping/cancellation checks, which compute over
    Lean's host `Float`.

Lean's `Float` is an opaque FFI type carrying no proof obligations, so the host `Float` verdict is
*fundamentally* uncertifiable — no theorem can relate `Float.log2`/`Float.exp2` to `ulp32`. Stage 3.3
therefore certifies the check on TorchLean's **computable** `IEEE32Exec` model instead, where every
operation is "decode → exact dyadic → round once" and is provably `round32` of the exact real result.
The residual `Float32 ↔ IEEE32Exec` step is an *assumption typeclass* upstream
(`RuntimeFloat32MatchesIEEE32Exec`), not an axiom — the honest, irreducible hardware trust boundary.

This module re-exposes, under adequacy-layer names, the executable primitives of the Stage-3.3
TorchLean bridge (`NN/Floats/IEEEExec/Bridge/FP32/Ulp.lean`, upstream form: the ULP query is the
*partial* `ulpExp? : IEEE32Exec → Option Int`, `none` on NaNs and infinities rather than an
artificial spacing) and states the capstone:

  * `exec_ulp_grounds` / `exec_half_ulp_grounds` — when the *executable* ULP query answers
    (`ulpExp? x = some k`, with `k` computed from the bit pattern by `Nat.log2` + `fexp32`), `2^k`
    is exactly the specified `ulp32` / `eps32` of the decoded value — and the query answers on
    precisely the finite fragment (`ulpExp?_isSome`). The `eps32` form is the very half-ulp
    threshold `Soundness.AbsorptionFlag` uses.
  * **A3/A1 executable — `exec_verdict_sound`.** The kernel's absorption verdict `absorbs s δ` (the
    float32 sum is unchanged) *certifies* the specification's absorption: the exact real sum rounds
    back to `s` under `round32`. This is the executable image of `Soundness.verdict_sound`'s flag⟹lost
    direction, realized at the genuine binary32 rounding rather than the abstract uniform grid — the
    computed verdict is provably the specified one, on the finite fragment. The
    `exec_verdict_sound_of_isFinite` form takes only the three executable finiteness checks (the
    dyadic decoding witnesses are recovered, not assumed).

Proved sorry-free; the executable side is exercised (`#eval`/`#guard`) in the `AdequacyExecBridge`
example. Mathlib- and TorchLean-backed.
-/
import PropertyKindCalculus.Uncertainty.Adequacy.Soundness
import PropertyKindCalculus.Uncertainty.Adequacy.Fp32Grounding
import NN.Floats.IEEEExec.Bridge.FP32.Ulp

namespace PropertyKindCalculus.Uncertainty.Adequacy

open TorchLean.Floats
open TorchLean.Floats.IEEE754
open TorchLean.Floats.IEEE754.IEEE32Exec

/-- **The executable ULP is the specified ULP.** When the bit-level ULP query answers —
`ulpExp? x = some k`, with `k` computed directly from `x`'s decoded dyadic payload with `Nat.log2`
and the integer exponent selector `fexp32`; it answers on exactly the finite fragment
(`ulpExp?_isSome`) — then `2^k` reproduces exactly the real, `noncomputable` `ulp32 (toReal x)`.
The first half of the "`Float.ulp` matching `ulp32`" the Stage-3.3 plan asks for, on the
certifiable `IEEE32Exec` model rather than opaque host `Float`. -/
theorem exec_ulp_grounds {x : IEEE32Exec} {k : Int} (hk : ulpExp? x = some k) :
    neuralBpow binaryRadix k = ulp32 (toReal x) :=
  neuralBpow_eq_ulp32_of_ulpExp?_eq_some hk

/-- **The executable half-ULP is the specified half-ULP.** `eps32` is the threshold `AbsorptionFlag`
compares an operand's uncertainty against; here it is recovered from the executable `ulpExp?`
answer. -/
theorem exec_half_ulp_grounds {x : IEEE32Exec} {k : Int} (hk : ulpExp? x = some k) :
    neuralBpow binaryRadix k / 2 = eps32 (toReal x) := by
  rw [exec_ulp_grounds hk]

/-- **A3/A1 at the executable binary32 kernel — Stage 3.3.** When the executable kernel reports an
operand absorbed (`absorbs s δ = true`, i.e. the float32 sum equals `s` unchanged), the specification
*agrees*: the exact real sum rounds back to `toReal s` under `round32`. This is the executable image
of `Soundness.verdict_sound`'s flag ⟹ contribution-lost direction — the abstract grid `gridRound u`
replaced by the genuine binary32 rounding `round32` — so the *computed* adequacy verdict is provably
the *specified* one, on the finite fragment (`toDyadic? s/δ = some _`, `isFinite (add s δ)`). -/
theorem exec_verdict_sound {s δ : IEEE32Exec} {ds dδ : TorchLean.Floats.IEEE754.IEEE32Exec.Dyadic}
    (hs : toDyadic? s = some ds) (hδ : toDyadic? δ = some dδ)
    (hfin : isFinite (add s δ) = true) (hverdict : absorbs s δ = true) :
    round32 (toReal s + toReal δ) = toReal s :=
  round32_add_eq_left_of_absorbs hs hδ hfin hverdict

/-- `exec_verdict_sound` from the three *executable* finiteness checks alone: the dyadic decoding
witnesses are recovered from `isFinite`, not assumed — the form a kernel driver can discharge
entirely by running `isFinite`/`absorbs`. -/
theorem exec_verdict_sound_of_isFinite {s δ : IEEE32Exec}
    (hs : isFinite s = true) (hδ : isFinite δ = true)
    (hfin : isFinite (add s δ) = true) (hverdict : absorbs s δ = true) :
    round32 (toReal s + toReal δ) = toReal s :=
  round32_add_eq_left_of_absorbs_of_isFinite hs hδ hfin hverdict

end PropertyKindCalculus.Uncertainty.Adequacy
