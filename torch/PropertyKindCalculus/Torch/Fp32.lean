/-
# Torch.Fp32 — the TorchLean instance of the R10 exec/spec refinement bridge

The abstract bridge `CarrierRefinement` (core) says how an *exec* carrier stands in
for a *spec* carrier: a forgetful `toSpec`, a spec-side `round`, and the law
`toSpec (x +ᴱ y) = round (toSpec x +ˢ toSpec y)`. This module instantiates it at
genuine **IEEE-754 binary32**, using TorchLean's float stack:

  * `FP32` — TorchLean's binary32 *rounding spec* (`NF binaryRadix fexp32 rnd32`, a
    Flocq-style format with no overflow). Its addition is, by definition, "compute
    in ℝ, then round", so the bridge law holds **unconditionally**:
    `(a + b).val = fp32Round (a.val + b.val)`. Hence `CarrierRefinement FP32 ℝ`, and
    the R10 capstone `Quantity.add_refines` specializes to FP32 with no extra proof.
  * `IEEE32Exec` — TorchLean's *executable* binary32 (a `UInt32` of bits, with NaN
    and infinities). Here the bridge holds only on the **finite path**: if both
    operands decode to finite values and the result does not overflow, the
    executable sum forgotten to ℝ equals the FP32-rounding of the real sum
    (`toReal_add_eq_fp32Round`). Overflow is an *explicit side condition* — the
    silent failure the unconditional abstract bridge cannot see, surfaced here as a
    hypothesis (`Quantity.add_refines_exec`).

This is the only PropertyKindCalculus library that depends on TorchLean. It is a
plain (non-`module`) file: Lean permits a non-module file to import the
module-system TorchLean modules, while the PropertyKindCalculus core stays
Mathlib- and module-free.
-/

import PropertyKindCalculus.QuantityRefinement
import PropertyKindCalculus.QuantityReal
import NN.Floats.IEEEExec.Bridge.FP32.Ops

open TorchLean.Floats          -- `FP32`
open TorchLean.Floats.IEEE754  -- `IEEE32Exec`, `Dyadic`

namespace PropertyKindCalculus

/-! ## The FP32 rounding-spec carrier and its (unconditional) refinement of ℝ -/

/-- TorchLean's `FP32` (binary32 rounding spec) is a numeric carrier: zero and
addition from the `NF` format. -/
noncomputable instance instCarrierFP32 : Carrier FP32 where
  zero := 0
  add := (· + ·)

/-- **`FP32` refines `ℝ` (R10), unconditionally.** Forget by `.val`, round by
`fp32Round`. The bridge law is `(a + b).val = fp32Round (a.val + b.val)`, which
holds *by computation*: `NF` addition is `ofReal (a.val + b.val)` and
`(ofReal x).val = roundR x = fp32Round x` for the binary32 parameters. `FP32` has no
overflow, so no side condition is needed — this is the lawful spec side of the
bridge. -/
noncomputable instance instCarrierRefinementFP32 : CarrierRefinement FP32 ℝ where
  toSpec := fun x => x.val
  round := IEEE32Exec.fp32Round
  toSpec_zero := by
    show (0 : FP32).val = (0 : ℝ)
    exact IEEE32Exec.fp32Round_zero
  toSpec_add := fun _ _ => rfl

/-- **The R10 capstone at genuine binary32.** For any kind, the `FP32` sum forgotten
to `ℝ` is the FP32-rounding of the real sum — `Quantity.add_refines` specialized to
the `FP32 → ℝ` refinement above, with no further proof. A law proved over the lawful
`ℝ` carrier therefore descends to FP32 with one rounding step. -/
theorem Quantity.add_refines_fp32 {k : KindOfProperty} (h : DifferenceKind k)
    (x y : Quantity k FP32) :
    (Quantity.toSpec (Quantity.add h x y) : Quantity k ℝ)
      = Quantity.roundBy (CarrierRefinement.round (E := FP32))
          (Quantity.add h (Quantity.toSpec x) (Quantity.toSpec y)) :=
  Quantity.add_refines h x y

/-! ## The executable carrier and its conditional refinement -/

/-- TorchLean's executable binary32 `IEEE32Exec` is a numeric carrier: zero and the
executable addition. (It is deliberately *not* given a `CarrierRefinement`, because
its bridge law holds only on the finite path — see below.) -/
instance instCarrierIEEE32 : Carrier IEEE32Exec where
  zero := 0
  add := IEEE32Exec.add

/-- Forget a kind-`k` executable-binary32 quantity to its real magnitude. -/
noncomputable def Quantity.toRealExec {k : KindOfProperty}
    (x : Quantity k IEEE32Exec) : Quantity k ℝ :=
  ⟨IEEE32Exec.toReal x.magnitude⟩

/-- **Executable refinement, conditional (R10).** For kind-`k` quantities carried at
the *executable* binary32, **if** both summands decode to finite values and the sum
does not overflow, then forgetting the executable sum to `ℝ` equals the
FP32-rounding of the real sum. The finiteness/no-overflow hypotheses are the
explicit side condition: where they fail (overflow to ∞, a NaN operand), the
refinement does not hold — exactly the silent failure the unconditional spec-side
bridge abstracts away, made visible here. Lifts TorchLean's
`toReal_add_eq_fp32Round` along the kind index. -/
theorem Quantity.add_refines_exec {k : KindOfProperty} (h : DifferenceKind k)
    (x y : Quantity k IEEE32Exec) {dx dy : IEEE32Exec.Dyadic}
    (hx : IEEE32Exec.toDyadic? x.magnitude = some dx)
    (hy : IEEE32Exec.toDyadic? y.magnitude = some dy)
    (hfin : IEEE32Exec.isFinite (IEEE32Exec.add x.magnitude y.magnitude) = true) :
    (Quantity.add h x y).toRealExec
      = Quantity.roundBy IEEE32Exec.fp32Round (Quantity.add h x.toRealExec y.toRealExec) := by
  show (Quantity.mk (IEEE32Exec.toReal (IEEE32Exec.add x.magnitude y.magnitude))
        : Quantity k ℝ)
      = Quantity.mk
          (IEEE32Exec.fp32Round
            (IEEE32Exec.toReal x.magnitude + IEEE32Exec.toReal y.magnitude))
  rw [IEEE32Exec.toReal_add_eq_fp32Round x.magnitude y.magnitude hx hy hfin]

end PropertyKindCalculus
