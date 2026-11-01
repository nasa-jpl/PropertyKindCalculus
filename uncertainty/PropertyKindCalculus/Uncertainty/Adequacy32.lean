/-
`PropertyKindCalculus.Uncertainty.Adequacy32` — the **certified runtime adequacy carrier** over
`Float32` (Stage 3.3 closed from the runtime side).

`Adequacy` runs the swamping/cancellation checks over binary64 `Float` and *emulates* the binary32
ulp with `exp2 (floor (log2 …))`; the sum it judges is a binary64 sum, so no theorem can connect
its verdict to `round₃₂`. This carrier computes in `Float32` itself. On the pinned toolchain
`Float32` is `structure Float32 where toModel : Float32.Model` with `+`, `-`, `isFinite`, `toBits`
defined through core's IEEE binary32 model, and FloatLib's native bridge
(`ExecFloat.Binary.ofFloat32_add_of_isFinite`) carries a finite `Float32` sum to the
`ExecFloat.Binary 8 23` sum — the executable model TorchLean's `absorbs`/`round_add_eq_left_of_absorbs`
and `ExecBridge.exec_verdict_sound` are stated over.

The swamping test is therefore `absorbs`-shaped — *the at-risk uncertainty added to the sum leaves
the sum unchanged* — so `add_flag_sound` is a theorem, not a mapping: when the flag fires on finite
operands, the exact real sum rounds back under `round₃₂`. No `log2`/`exp2` (the `opaque` externs)
appear. What stays trusted is exactly what FloatLib names: the compiled `lean_float32_*` primitives
agree with `Float32.Model`.
-/

module

public import PropertyKindCalculus.Uncertainty.Carriers
public import PropertyKindCalculus.Uncertainty.Adequacy
public import PropertyKindCalculus.Uncertainty.Adequacy.ExecBridge
public import FloatLib.Floats.Formats.IEEE754.Native.AddSub
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel.MulDiv
public import Batteries.Data.Float.Lemmas

@[expose] public section Blanket

namespace PropertyKindCalculus.Uncertainty

open PropertyKindCalculus.Paradigm

/-- **The certified numerical-adequacy carrier**: `Adequacy` with `Float32` magnitudes and
uncertainties. -/
structure Adequacy32 where
  /-- The computed magnitude (over `Float32`). -/
  value : Float32
  /-- The absolute uncertainty contribution carried to this value. -/
  unc : Float32
  /-- The accumulated adequacy report. -/
  report : AdequacyReport := {}
  deriving Repr

namespace Adequacy32

def input (v u : Float32) : Adequacy32 := { value := v, unc := u }
def exact (v : Float32) : Adequacy32 := { value := v, unc := 0.0 }
def isAdequate (a : Adequacy32) : Bool := a.report.absorptions == 0 && a.report.cancellations == 0
def mapVal (f : Float32 → Float32) (a : Adequacy32) : Adequacy32 := { a with value := f a.value }

/-- The at-risk uncertainty at an addition: the smaller-magnitude operand's. -/
def riskUnc (a b : Adequacy32) : Float32 := if a.value.abs ≤ b.value.abs then a.unc else b.unc

/-- **The swamping test**, `absorbs`-shaped: a positive at-risk uncertainty that, added to the
binary32 sum, leaves it *bit-for-bit* unchanged — the same equality TorchLean's `absorbs` decides
on the model (so `−0 + δ = δ` is never a hit, and NaN never equals itself). -/
def absorbed (v δ : Float32) : Bool := decide (0.0 < δ) && ((v + δ).toBits == v.toBits)

/-- **Addition with a swamping check** (compare `Adequacy.add`). -/
protected def add (a b : Adequacy32) : Adequacy32 :=
  let v := a.value + b.value
  let m := a.report.merge b.report
  { value := v, unc := a.unc + b.unc,
    report := if absorbed v (riskUnc a b) then { m with absorptions := m.absorptions + 1 } else m }

/-- **Subtraction with a cancellation check** (compare `Adequacy.sub`). -/
protected def sub (a b : Adequacy32) : Adequacy32 :=
  let v := a.value - b.value
  let u := a.unc + b.unc
  let flagged := decide (0.0 < u) && decide (v.abs ≤ u) && decide (v.abs < a.value.abs)
  let m := a.report.merge b.report
  { value := v, unc := u,
    report := if flagged then { m with cancellations := m.cancellations + 1 } else m }

protected def mul (a b : Adequacy32) : Adequacy32 :=
  { value := a.value * b.value,
    unc := a.value.abs * b.unc + b.value.abs * a.unc,
    report := a.report.merge b.report }

protected def div (a b : Adequacy32) : Adequacy32 :=
  { value := a.value / b.value,
    unc := (a.value.abs * b.unc + b.value.abs * a.unc) / (b.value * b.value),
    report := a.report.merge b.report }

instance : Zero Adequacy32 := ⟨exact 0.0⟩
instance : One Adequacy32 := ⟨exact 1.0⟩
instance : Add Adequacy32 := ⟨Adequacy32.add⟩
instance : Sub Adequacy32 := ⟨Adequacy32.sub⟩
instance : Mul Adequacy32 := ⟨Adequacy32.mul⟩
instance : Div Adequacy32 := ⟨Adequacy32.div⟩
instance : Min Adequacy32 :=
  ⟨fun a b => if a.value ≤ b.value then { a with report := a.report.merge b.report }
              else { b with report := a.report.merge b.report }⟩
instance : Max Adequacy32 :=
  ⟨fun a b => if a.value ≤ b.value then { b with report := a.report.merge b.report }
              else { a with report := a.report.merge b.report }⟩
instance : Coe Nat Adequacy32 := ⟨fun n => exact n.toFloat32⟩

/-- Transcendentals propagate value and uncertainty to first order as `Adequacy` does; the
derivative is taken at `Float32` (the `opaque` externs `Float32.exp`/`log`/… are the carrier's
*values*, not part of any verdict). -/
instance : MathCarrier Adequacy32 where
  exp a := { a with value := a.value.exp, unc := a.value.exp.abs * a.unc }
  log a := { a with value := a.value.log, unc := a.unc / a.value.abs }
  sin a := { a with value := a.value.sin, unc := a.value.cos.abs * a.unc }
  cos a := { a with value := a.value.cos, unc := a.value.sin.abs * a.unc }
  sinh a := { a with value := a.value.sinh, unc := a.value.cosh.abs * a.unc }
  cosh a := { a with value := a.value.cosh, unc := a.value.sinh.abs * a.unc }
  tanh a := { a with value := a.value.tanh, unc := (1.0 - a.value.tanh * a.value.tanh).abs * a.unc }
  sqrt a := { a with value := a.value.sqrt, unc := a.unc / (2.0 * a.value.sqrt) }
  abs a := { a with value := a.value.abs }
  pi := exact 3.14159265358979323846

instance : NumCarrier Adequacy32 := {}

/-! ## Soundness of the flag

The chain, each step a theorem: core's `Float32` *is* `Float32.Model` (`Float32.toBits_inj`,
Batteries) → FloatLib's native bridge takes a finite `Float32` sum to the `ExecFloat.Binary 8 23`
sum (`ofFloat32_add_of_isFinite`) → TorchLean's `round_add_eq_left_of_absorbs`, re-exposed as
`ExecBridge.exec_verdict_sound`, reads the absorbed sum as `round₃₂` of the exact real sum. -/

open FloatLib.Floats (ExecFloat)
open FloatLib.Floats.ExecFloat.Binary (ofFloat32 toModel isFinite ofFloat32_add_of_isFinite
  toModel_ofFloat32)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open TorchLean.Floats.IEEE754.IEEE32Exec (absorbs)
open PropertyKindCalculus.Fp32 (round32)

/-- Finiteness is the same question on `Float32` and on its image in the binary32 model. -/
theorem isFinite_ofFloat32 (v : Float32) : isFinite (ofFloat32 v) = v.isFinite := by
  have h := Model.isFinite_toModel (fmt := FloatFormat.binary32) (by decide)
    (Model.ofFloat32Model v.toModel)
  rw [Model.toModel_ofFloat32Model] at h
  exact h.symm

/-- FloatLib's native bridge, read as the model sum of the images (`+` on the model is
`ExecFloat.add` definitionally). -/
theorem add_ofFloat32 {v δ : Float32} (hv : v.isFinite = true) (hδ : δ.isFinite = true) :
    ExecFloat.add (ofFloat32 v) (ofFloat32 δ) = ofFloat32 (v + δ) :=
  (ofFloat32_add_of_isFinite v δ hv hδ).symm

/-- The bit equality the runtime test decides is `Float32` equality (`Float32.toBits_inj`). -/
theorem add_eq_of_absorbed {v δ : Float32} (h : absorbed v δ = true) : v + δ = v :=
  Float32.toBits_inj.mp (eq_of_beq ((Bool.and_eq_true _ _).mp h).2)

/-- The at-risk uncertainty is positive when the flag fires. -/
theorem pos_of_absorbed {v δ : Float32} (h : absorbed v δ = true) : 0.0 < δ :=
  of_decide_eq_true ((Bool.and_eq_true _ _).mp h).1

/-- **The runtime flag is TorchLean's model verdict**: on finite operands, `absorbed v δ` is
`absorbs (ofFloat32 v) (ofFloat32 δ)`. -/
theorem absorbs_of_absorbed {v δ : Float32} (hv : v.isFinite = true) (hδ : δ.isFinite = true)
    (h : absorbed v δ = true) : absorbs (ofFloat32 v) (ofFloat32 δ) = true := by
  have h2 : ExecFloat.add (ofFloat32 v) (ofFloat32 δ) = ofFloat32 v := by
    rw [add_ofFloat32 hv hδ, add_eq_of_absorbed h]
  exact decide_eq_true h2

/-- An absorbed sum of finite operands is finite on the model (it *is* `ofFloat32 v`). -/
theorem isFinite_add_of_absorbed {v δ : Float32} (hv : v.isFinite = true) (hδ : δ.isFinite = true)
    (h : absorbed v δ = true) : isFinite (ExecFloat.add (ofFloat32 v) (ofFloat32 δ)) = true := by
  rw [add_ofFloat32 hv hδ, add_eq_of_absorbed h, isFinite_ofFloat32]; exact hv

/-- **A3 at the runtime carrier — Stage 3.3 closed from the runtime side.** When `absorbed v δ`
fires on finite `Float32` operands, the exact real sum of the values they denote rounds back to
`v` under `round₃₂`: the computed verdict is the specified one. -/
theorem add_flag_sound {v δ : Float32} (hv : v.isFinite = true) (hδ : δ.isFinite = true)
    (h : absorbed v δ = true) :
    round32 ((toModel (ofFloat32 v)).toReal + (toModel (ofFloat32 δ)).toReal) =
      (toModel (ofFloat32 v)).toReal :=
  Adequacy.exec_verdict_sound (isFinite_add_of_absorbed hv hδ h) (absorbs_of_absorbed hv hδ h)

/-- The carrier's `+` raises the absorption count exactly when `absorbed` fires on the sum and the
at-risk uncertainty — so `add_flag_sound` is about the report a model run emits. -/
theorem add_absorptions (a b : Adequacy32) :
    (a + b).report.absorptions =
      (a.report.merge b.report).absorptions +
        (if absorbed (a.value + b.value) (riskUnc a b) then 1 else 0) := by
  show (Adequacy32.add a b).report.absorptions = _
  unfold Adequacy32.add
  by_cases h : absorbed (a.value + b.value) (riskUnc a b) = true <;> simp [h]

-- The flag fires on a textbook swamping — `1 + 2⁻²⁵` is `1` in binary32 — and not when the
-- uncertainty survives: `1 + 2⁻²³` is the next binary32 after `1`.
#guard absorbed 1.0 (Float32.ofScientific 298023223876953125 true 25) = true
#guard absorbed 1.0 (Float32.ofScientific 11920928955078125 true 23) = false

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy32.add_flag_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms add_flag_sound

end Adequacy32

end PropertyKindCalculus.Uncertainty

end Blanket
