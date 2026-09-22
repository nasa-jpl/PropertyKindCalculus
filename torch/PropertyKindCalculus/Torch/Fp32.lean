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

module

public import PropertyKindCalculus.QuantityRefinement
public import PropertyKindCalculus.QuantityReal
public import NN.Proofs.RuntimeApprox.IEEE32.Arithmetic

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open TorchLean.Floats          -- `FP32`, `round32`
open TorchLean.Floats.IEEE754  -- the `IEEE32Exec` theorem namespace (`fp32Round`, `toReal_*`)
open FloatLib.Floats (ExecFloat)
open FloatLib.Floats.ExecFloat.Binary (isFinite toModel)
open FloatLib.Floats.Formats.Flocq (round_preserves_generic generic_format_zero)

namespace PropertyKindCalculus

/-- **The executable IEEE-754 binary32 carrier**: FloatLib's configured `ExecFloat.Binary 8 23`
(eight exponent bits, twenty-three stored fraction bits), the word TorchLean's runtime-approximation
theorems are stated over. Named here once so every kinded statement about executable binary32 reads
against one carrier. -/
abbrev IEEE32Exec : Type := ExecFloat.Binary 8 23

/-- The real magnitude of an executable binary32 word: decode to FloatLib's model and read its real
value (`0` for a non-finite word). -/
noncomputable abbrev IEEE32Exec.toReal (x : IEEE32Exec) : ℝ := (toModel x).toReal

/-- Binary32 rounding fixes `0`: it is on the grid. -/
theorem fp32Round_zero : IEEE32Exec.fp32Round 0 = 0 :=
  round_preserves_generic rnd32 0 generic_format_zero

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
    exact fp32Round_zero
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
  add := ExecFloat.add

/-- Forget a kind-`k` executable-binary32 quantity to its real magnitude. -/
noncomputable def Quantity.toRealExec {k : KindOfProperty}
    (x : Quantity k IEEE32Exec) : Quantity k ℝ :=
  ⟨IEEE32Exec.toReal x.magnitude⟩

/-- **Executable refinement, conditional (R10).** For kind-`k` quantities carried at
the *executable* binary32, **if** the executable sum is finite (neither operand a NaN or
an infinity, no overflow), then forgetting the executable sum to `ℝ` equals the
FP32-rounding of the real sum. The finiteness hypothesis is the explicit side
condition: where it fails (overflow to ∞, a NaN operand), the refinement does not
hold — exactly the silent failure the unconditional spec-side bridge abstracts away,
made visible here. Lifts TorchLean's `toReal_add_eq_fp32Round_of_isFinite` along the
kind index. -/
theorem Quantity.add_refines_exec {k : KindOfProperty} (h : DifferenceKind k)
    (x y : Quantity k IEEE32Exec)
    (hfin : isFinite (ExecFloat.add x.magnitude y.magnitude) = true) :
    (Quantity.add h x y).toRealExec
      = Quantity.roundBy IEEE32Exec.fp32Round (Quantity.add h x.toRealExec y.toRealExec) := by
  show (Quantity.mk (IEEE32Exec.toReal (ExecFloat.add x.magnitude y.magnitude))
        : Quantity k ℝ)
      = Quantity.mk
          (IEEE32Exec.fp32Round
            (IEEE32Exec.toReal x.magnitude + IEEE32Exec.toReal y.magnitude))
  rw [IEEE32Exec.toReal, IEEE32Exec.toReal_add_eq_fp32Round_of_isFinite hfin]

/-! ## The multiplicative surface at binary32

`Quantity.mul` and `Quantity.div` ask for `[ScalarCarrier R]` beside `[Mul R]` / `[Div R]`:
the carrier-side attestation that a magnitude is *one number*, so that the carrier's `*` is
the multiplication of magnitudes and not a componentwise operation on an array. Both
binary32 carriers qualify — a binary32 value is a single number — exactly as `Float` does. -/

/-- **`FP32` is a scalar carrier.** A binary32 rounding-spec magnitude is one number. -/
instance instScalarCarrierFP32 : ScalarCarrier FP32 := ⟨⟩

/-- **`IEEE32Exec` is a scalar carrier.** So is the executable bit-level binary32. -/
instance instScalarCarrierIEEE32 : ScalarCarrier IEEE32Exec := ⟨⟩

/-- **`FP32` refines `ℝ` multiplicatively, unconditionally.** `NF` multiplication is
`ofReal (a.val * b.val)` — compute in `ℝ`, then round — so the bridge law is `rfl`, exactly
as it is for addition. -/
noncomputable instance instMulRefinementFP32 : MulRefinement FP32 ℝ where
  toSpec_mul _ _ := rfl

/-- **`FP32` refines `ℝ` in division, unconditionally** — and the word is load-bearing.
`NF` division is `ofReal (a.val / b.val)`, so at a zero denominator *both* sides read `ℝ`'s
total convention `x / 0 = 0` and the law holds by `rfl` with nothing to exclude. That is a
property of a specification format, not a reprieve for a machine: `IEEE32Exec.div` by zero
produces an infinity or a NaN, and the refinement there carries `dy.mant ≠ 0` as a
hypothesis (`Quantity.div_refines_exec`). The spec rung cannot see the hazard; the exec rung
is where it must be discharged. -/
noncomputable instance instDivRefinementFP32 : DivRefinement FP32 ℝ where
  toSpec_div _ _ := rfl

/-- **The kind-crossing R10 capstone at genuine binary32.** For a licensed product
`ProductKind k₁ k₂ k`, the `FP32` product forgotten to `ℝ` is the FP32-rounding of the real
product — `Quantity.mul_refines` specialized, with no further proof. -/
theorem Quantity.mul_refines_fp32 {k₁ k₂ k : KindOfProperty} (h : ProductKind k₁ k₂ k)
    (x : Quantity k₁ FP32) (y : Quantity k₂ FP32) :
    (Quantity.toSpec (Quantity.mul h x y) : Quantity k ℝ)
      = Quantity.roundBy (CarrierRefinement.round (E := FP32))
          (Quantity.mul h (Quantity.toSpec x) (Quantity.toSpec y)) :=
  Quantity.mul_refines h x y

/-- **And for a licensed quotient** `QuotientKind k₁ k₂ k` — the rung a ratio, a conversion
factor, or a weighted mean's denominator rides. -/
theorem Quantity.div_refines_fp32 {k₁ k₂ k : KindOfProperty} (h : QuotientKind k₁ k₂ k)
    (x : Quantity k₁ FP32) (y : Quantity k₂ FP32) :
    (Quantity.toSpec (Quantity.div h x y) : Quantity k ℝ)
      = Quantity.roundBy (CarrierRefinement.round (E := FP32))
          (Quantity.div h (Quantity.toSpec x) (Quantity.toSpec y)) :=
  Quantity.div_refines h x y

/-- **Executable multiplicative refinement, conditional (R10).** If the executable product
is finite, forgetting it to `ℝ` equals the FP32-rounding of the real product. Lifts
TorchLean's `toReal_mul_eq_fp32Round_of_isFinite` along the kind product. -/
theorem Quantity.mul_refines_exec {k₁ k₂ k : KindOfProperty} (h : ProductKind k₁ k₂ k)
    (x : Quantity k₁ IEEE32Exec) (y : Quantity k₂ IEEE32Exec)
    (hfin : isFinite (ExecFloat.mul x.magnitude y.magnitude) = true) :
    (Quantity.mul h x y).toRealExec
      = Quantity.roundBy IEEE32Exec.fp32Round
          (Quantity.mul h x.toRealExec y.toRealExec) := by
  show (Quantity.mk (IEEE32Exec.toReal (ExecFloat.mul x.magnitude y.magnitude))
        : Quantity k ℝ)
      = Quantity.mk
          (IEEE32Exec.fp32Round
            (IEEE32Exec.toReal x.magnitude * IEEE32Exec.toReal y.magnitude))
  rw [IEEE32Exec.toReal, IEEE32Exec.toReal_mul_eq_fp32Round_of_isFinite hfin]

/-- **Executable division refinement, conditional (R10) — and this is the one that carries
the zero denominator.** Beside the finiteness hypotheses the product needs, division needs
`hy0 : dy.significand ≠ 0`: the divisor's decoded significand is not zero. Where the spec-side
`DivRefinement FP32 ℝ` is unconditional because `ℝ` totalizes `x / 0` to `0`, the executable
format does not — it produces an infinity or a NaN, and no rounding of a real quotient
equals either. So the metrological license a mean's denominator needs (`WeightedCarving`'s
`total_ne_zero`) reappears here as an arithmetic hypothesis on the same computation, at the
rung where it can actually fail. Lifts `toReal_div_eq_fp32Round` along the kind quotient. -/
theorem Quantity.div_refines_exec {k₁ k₂ k : KindOfProperty} (h : QuotientKind k₁ k₂ k)
    (x : Quantity k₁ IEEE32Exec) (y : Quantity k₂ IEEE32Exec) {dx dy : FloatLib.Numerics.Dyadic}
    (hx : (toModel x.magnitude).toDyadic? = some dx)
    (hy : (toModel y.magnitude).toDyadic? = some dy)
    (hy0 : dy.significand ≠ 0)
    (hfin : isFinite (ExecFloat.div x.magnitude y.magnitude) = true) :
    (Quantity.div h x y).toRealExec
      = Quantity.roundBy IEEE32Exec.fp32Round
          (Quantity.div h x.toRealExec y.toRealExec) := by
  show (Quantity.mk (IEEE32Exec.toReal (ExecFloat.div x.magnitude y.magnitude))
        : Quantity k ℝ)
      = Quantity.mk
          (IEEE32Exec.fp32Round
            (IEEE32Exec.toReal x.magnitude / IEEE32Exec.toReal y.magnitude))
  rw [IEEE32Exec.toReal, IEEE32Exec.toReal_div_eq_fp32Round hx hy hy0 hfin]

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
