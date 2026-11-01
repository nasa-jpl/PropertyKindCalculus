/-
# Worked example — uncertified vs. certified: the same swamping kernel at `Adequacy` and `Adequacy32`

`AdequacySwamping` runs the write-once kernel `accModel bias x = bias + x` at `Adequacy`, the
**illustrative** carrier: binary64 `Float` values, the binary32 ulp *emulated* (`Adequacy.ulp32`,
read off the exponent bits). Its verdict is a *claim about a picture* of binary32 — a binary64 sum
compared against a binary32 spacing. No theorem reaches it: nothing relates that binary64 sum to
`round₃₂`, and the flag's threshold `unc < ½ ulp32` is a rule of thumb, not IEEE's rounding.

`Adequacy32` runs the *same kernel* at **genuine binary32** (`Float32` values and uncertainties).
Its flag is `absorbs`-shaped — the at-risk uncertainty added to the sum leaves it bit-for-bit
unchanged — and `Adequacy32.add_flag_sound` **certifies** it: when the flag fires on finite operands,
`round₃₂ (v + δ) = v` over `ℝ` (core's model-backed `Float32` → FloatLib's native bridge →
TorchLean's `absorbs` theorem). The verdict a run emits is the specified one, by theorem.

The two carriers agree on the textbook cases — and **disagree exactly where a rule of thumb and
IEEE rounding part ways**: at a *tie*. An uncertainty of exactly half a ulp is *not* below
`½ ulp32`, so the emulation does not flag it; genuine binary32 rounds the tie to even, so on an
even-mantissa sum the uncertainty *is* absorbed and the certified carrier flags it. The emulation
cannot see the even/odd distinction because its arithmetic is not the arithmetic in question.

Everything here is a **checked fact** (the module builds under CI).
-/

module

public import PropertyKindCalculus.Uncertainty
public import PropertyKindCalculus.Uncertainty.Adequacy32
meta import PropertyKindCalculus.Uncertainty
meta import PropertyKindCalculus.Uncertainty.Adequacy32

@[expose] public section Blanket

namespace PropertyKindCalculus.UncertaintyExamples.AdequacyCertified

open PropertyKindCalculus PropertyKindCalculus.Paradigm PropertyKindCalculus.Uncertainty

/-- The write-once kernel of `AdequacySwamping`: a small measured quantity added to a bias. -/
def accModel {α : Type} [NumCarrier α] (bias x : α) : α := bias + x

/-! ## Binary32 constants, exact, from their bit patterns -/

/-- `2⁻²³` as `Float32` — one ulp of binary32 at `1`. -/
def ulpAtOne32 : Float32 := Float32.ofBits 0x34000000
/-- `2⁻²⁴` as `Float32` — half a ulp of binary32 at `1`. -/
def halfUlpAtOne32 : Float32 := Float32.ofBits 0x33800000
/-- `1 + 2⁻²³` as `Float32` — the next binary32 after `1`, odd mantissa. -/
def oneUp32 : Float32 := Float32.ofBits 0x3F800001

#guard ulpAtOne32 == Float32.ofScientific 11920928955078125 true 23
#guard halfUlpAtOne32 == Float32.ofScientific 59604644775390625 true 24
#guard (1.0 : Float32) + ulpAtOne32 == oneUp32

/-! ## The textbook cases: both carriers agree -/

/-- Illustrative: `1e8 + (1 ± 1)` — `1 < ½ ulp32(1e8) = 4`, flagged. -/
def swamped64 : Adequacy := accModel (Adequacy.exact 1e8) (Adequacy.input 1.0 1.0)
/-- Certified: the same at genuine binary32 — `1e8 + 1 = 1e8` in `Float32`, flagged by theorem. -/
def swamped32 : Adequacy32 := accModel (Adequacy32.exact 1e8) (Adequacy32.input 1.0 1.0)

#guard swamped64.report.absorptions == 1
#guard swamped32.report.absorptions == 1

/-- Illustrative: `100 + (1 ± 1)` — `1 ≫ ½ ulp32(100)`, clean. -/
def clean64 : Adequacy := accModel (Adequacy.exact 100.0) (Adequacy.input 1.0 1.0)
/-- Certified: `100 + 1 ≠ 100` in `Float32`, clean. -/
def clean32 : Adequacy32 := accModel (Adequacy32.exact 100.0) (Adequacy32.input 1.0 1.0)

#guard clean64.report.absorptions == 0
#guard clean32.report.absorptions == 0

/-! ## The tie: where they disagree

`1 + (0 ± 2⁻²⁴)`: the uncertainty is *exactly* half a ulp of binary32 at `1`.

  * The emulation asks `2⁻²⁴ < ½ · ulp32(1) = 2⁻²⁴` — false — and reports the sum adequate.
  * Genuine binary32 computes `1 + 2⁻²⁴`: a tie, rounded to even, which is `1` — the uncertainty is
    absorbed, and `add_flag_sound` says the exact real sum `1 + 2⁻²⁴` rounds back to `1` under
    `round₃₂`. The certified carrier flags it.

On the *odd*-mantissa neighbour `1 + 2⁻²³` the tie rounds *up*, the uncertainty survives, and both
carriers agree the sum is adequate — the emulation only by coincidence, since it never looked at the
mantissa. -/

/-- Illustrative, at the tie: not flagged (`2⁻²⁴ < 2⁻²⁴` is false). -/
def tieEven64 : Adequacy :=
  accModel (Adequacy.exact 1.0) (Adequacy.input 0.0 (Adequacy.pow2 (-24)))
/-- Certified, at the tie on an even mantissa: flagged — `1 + 2⁻²⁴` rounds to even, i.e. to `1`. -/
def tieEven32 : Adequacy32 :=
  accModel (Adequacy32.exact 1.0) (Adequacy32.input 0.0 halfUlpAtOne32)
/-- Certified, at the tie on an odd mantissa: not flagged — `(1 + 2⁻²³) + 2⁻²⁴` rounds up. -/
def tieOdd32 : Adequacy32 :=
  accModel (Adequacy32.exact oneUp32) (Adequacy32.input 0.0 halfUlpAtOne32)

#guard Adequacy.isAdequate tieEven64 == true       -- the picture says adequate…
#guard tieEven32.report.absorptions == 1           -- …genuine binary32 absorbed the uncertainty
#guard Adequacy32.isAdequate tieEven32 == false
#guard tieOdd32.report.absorptions == 0
-- the flag at the tie is exactly `absorbed`, the predicate `add_flag_sound` certifies:
#guard Adequacy32.absorbed 1.0 halfUlpAtOne32 == true
#guard Adequacy32.absorbed oneUp32 halfUlpAtOne32 == false

/-- What the certified flag *means* here, as the theorem states it: `1 + 2⁻²⁴`, as a real, rounds
back to `1` under `round₃₂`. Instantiating `add_flag_sound` at the run's operands. -/
theorem tieEven_round32 :
    PropertyKindCalculus.Fp32.round32
        ((FloatLib.Floats.ExecFloat.Binary.toModel (FloatLib.Floats.ExecFloat.Binary.ofFloat32 (1.0 : Float32))).toReal +
          (FloatLib.Floats.ExecFloat.Binary.toModel (FloatLib.Floats.ExecFloat.Binary.ofFloat32 halfUlpAtOne32)).toReal) =
      (FloatLib.Floats.ExecFloat.Binary.toModel (FloatLib.Floats.ExecFloat.Binary.ofFloat32 (1.0 : Float32))).toReal :=
  Adequacy32.add_flag_sound (by native_decide) (by native_decide) (by native_decide)

end PropertyKindCalculus.UncertaintyExamples.AdequacyCertified

end Blanket
