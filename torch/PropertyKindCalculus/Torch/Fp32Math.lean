/-
# Torch.Fp32Math — the binary32 carriers as function carriers (`MathCarrier`)

The function-layer companion to `Torch.Fp32`. TorchLean's `MathFunctions` surface is, by
design, exactly the base `MathCarrier` surface, so both binary32 carriers instantiate it
directly:

  * `FP32` — the rounding *spec* (noncomputable, like its `MathFunctions` instance);
  * `IEEE32Exec` — the *executable* binary32 (computable).

Two absences are deliberate and are the metrological content of this file:

  * Neither carrier is a `MathCarrierExt`. The extended surface (`tan`, the inverse trig,
    `atan2`, `cbrt`, rounding, rational `rpow`) is **not** in TorchLean's `MathFunctions`,
    so the executable carrier has a strictly *smaller function vocabulary* than the `ℝ`
    specification carrier — a fact the type system now records rather than hides.
  * Neither is a `LawfulMathCarrier`. `sin² + cos² = 1` and `exp(a+b) = exp a · exp b` are
    not floating-point identities; the function laws hold only at the `ℝ` proof carrier.
    This is the same exec/spec gap `Torch.Fp32` draws for `+` (`FP32` is a `Carrier` but
    not a `LawfulCarrier`), now for the transcendental functions — closed, where needed,
    by relating each float operation to the rounding of its real specification.

This is the only PropertyKindCalculus library that depends on TorchLean; the core spine
stays Mathlib- and TorchLean-free.
-/

module

public import PropertyKindCalculus.Torch.Fp32
public import PropertyKindCalculus.QuantityFunction
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals

@[expose] public section Blanket

open TorchLean.Floats          -- `FP32`
open FloatLib.Numerics (MathFunctions)

namespace PropertyKindCalculus

/-- **`FP32` (binary32 rounding spec) is a function carrier.** Its operations are
TorchLean's `MathFunctions` for the `NF` format — noncomputable, like the format's
rounding. It is intentionally neither a `MathCarrierExt` (its function vocabulary is the
base surface only) nor a `LawfulMathCarrier` (the function identities fail in
binary32). -/
noncomputable instance instMathCarrierFP32 : MathCarrier FP32 where
  exp := MathFunctions.exp
  log := MathFunctions.log
  sin := MathFunctions.sin
  cos := MathFunctions.cos
  sinh := MathFunctions.sinh
  cosh := MathFunctions.cosh
  tanh := MathFunctions.tanh
  sqrt := MathFunctions.sqrt
  abs := MathFunctions.abs
  pi := MathFunctions.pi

/-- **`IEEE32Exec` (executable binary32) is a function carrier.** Computable — a
`Quantity k IEEE32Exec` reduces under `#eval`. Same two deliberate absences as `FP32`. -/
instance instMathCarrierIEEE32 : MathCarrier IEEE32Exec where
  exp := MathFunctions.exp
  log := MathFunctions.log
  sin := MathFunctions.sin
  cos := MathFunctions.cos
  sinh := MathFunctions.sinh
  cosh := MathFunctions.cosh
  tanh := MathFunctions.tanh
  sqrt := MathFunctions.sqrt
  abs := MathFunctions.abs
  pi := MathFunctions.pi

end PropertyKindCalculus

end Blanket
