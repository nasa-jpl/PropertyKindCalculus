/-
# Validation probes — level quantities (R13 groundwork)

Inhabitation, boundary, and numeric probes for `LevelKind` (`PropertyKindCalculus.Level`):
the decibel as a construction over a ratio-scale root kind rather than a fifth scale type.
The probes check the design's load-bearing claims:

  * the reference and the role are **kind identity** — dBm ≠ dBW, field level ≠ power
    level — while the gain kind provably forgets the reference;
  * the gate profile: order is licensed at the level kind, the certified addition and the
    certified product are structurally unavailable there (`#check_failure`), and the
    torsor pair `sub`/`shift` — the only additive vocabulary — is exact and lands in the
    right kinds;
  * gains compose by the ordinary certified addition (ratio-scale), so an amplifier chain
    needs no new machinery;
  * at `Float`, the chart realizes: 0.2 Pa re 20 µPa is 80 dB, two equal 94 dB sources
    combine to ≈97 dB (never 188), and the same dB figure means ×10 in field or ×10 in
    power depending on the *kind* (root-power vs power) — the fact only a kind layer can
    even state.

EM is deliberately on the page: dBm, dBW, and a field level are the exemplars, because the
level machinery is what a kinded treatment of PhysLib's electromagnetism needs first.
-/

module

public import PropertyKindCalculus
meta import PropertyKindCalculus

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Tests.Level

open PropertyKindCalculus

/-! ## The kinds: acoustics and EM -/

/-- Sound pressure — a root-power quantity (its square is proportional to power). -/
def soundPressure : KindOfProperty := { id := "sound pressure", scale := .ratio }
/-- Sound intensity — a power quantity. -/
def soundIntensity : KindOfProperty := { id := "sound intensity", scale := .ratio }
/-- Electrical power — the root kind of dBm and dBW. -/
def elPower : KindOfProperty := { id := "power", scale := .ratio }
/-- Electric field strength — a root-power quantity (EM). -/
def eField : KindOfProperty := { id := "electric field strength", scale := .ratio }

/-- Sound pressure level, re 20 µPa (ISO 80000-8). -/
def spl : LevelKind := ⟨soundPressure, .rootPower, "20 µPa"⟩
/-- Sound intensity level, re 1 pW/m². -/
def sil : LevelKind := ⟨soundIntensity, .power, "1 pW/m²"⟩
/-- Power level re 1 mW — the dBm (EM/RF). -/
def dBm : LevelKind := ⟨elPower, .power, "1 mW"⟩
/-- Power level re 1 W — the dBW. Same root, same role, different reference. -/
def dBW : LevelKind := ⟨elPower, .power, "1 W"⟩
/-- Electric field level re 1 µV/m — a root-power level (EM). -/
def eFieldLevel : LevelKind := ⟨eField, .rootPower, "1 µV/m"⟩

/-! ## Kind identity: reference and role individuate -/

-- dBm and dBW differ only in reference — and are different kinds.
example : dBm.toKind ≠ dBW.toKind := by decide
-- A field level and a power level are different kinds even before their roots differ.
example : spl.toKind ≠ sil.toKind := by decide
example : eFieldLevel.toKind ≠ dBm.toKind := by decide
-- A level kind is not its root kind.
example : spl.toKind ≠ soundPressure := by decide
-- The gain kind provably forgets the reference: dBm and dBW gains are one kind.
example : dBm.gainKind = dBW.gainKind := rfl
example : dBm.gainKind = LevelKind.gainKind ⟨elPower, .power, "anything"⟩ := rfl

/-! ## The gate profile -/

-- Order is licensed at a level kind (ordinal): a noise limit is a meaningful bound.
#guard ((⟨80⟩ : Quantity spl.toKind Int) ≤ ⟨85⟩)
-- ... and the order gate is discharged for it, `OrderKind`-style, by `trivial`.
example : spl.toKind.scale.AllowsOrder := spl.toKind_allowsOrder

-- The certified addition is structurally unavailable: `DifferenceKind` is unprovable at a
-- level kind, so the scale-checked `Quantity.add` does not elaborate. `L₁ + L₂` rejected
-- as a type error, not a lint.
#check_failure (fun (x y : Quantity spl.toKind Int) =>
  Quantity.add DifferenceKind.ofScale x y)

-- The certified product is unavailable too: a level kind is not ratio-scale.
#check_failure (fun (x y : Quantity spl.toKind Int) =>
  Quantity.mulK soundPressure x y)

-- The unprovability facts, as theorems.
example : ¬ spl.toKind.scale.AllowsDifference := spl.toKind_not_allowsDifference
example : ¬ spl.toKind.IsRational := spl.toKind_not_isRational
example : spl.gainKind.IsRational := spl.gainKind_isRational

/-! ## The torsor, exactly, at `Int` -/

-- The difference of two levels is a *gain* — result-kind pin, and the value.
example : spl.sub (⟨94⟩ : Quantity spl.toKind Int) ⟨80⟩
    = (⟨14⟩ : Quantity spl.gainKind Int) := rfl
-- Shifting a level by a gain is a level — what an amplifier does.
example : spl.shift (⟨80⟩ : Quantity spl.toKind Int) (⟨14⟩ : Quantity spl.gainKind Int)
    = (⟨94⟩ : Quantity spl.toKind Int) := rfl
-- Torsor coherence at the lawful carrier: shift then sub recovers the gain, and the
-- certificate is satisfied by construction.
example (x : Quantity spl.toKind Int) (g : Quantity spl.gainKind Int) :
    spl.sub (spl.shift x g) x = g := by
  apply Quantity.ext; simp [LevelKind.sub, LevelKind.shift, Carrier.add]; omega
example (x y : Quantity spl.toKind Int) : spl.IsGainOf (spl.sub x y) x y :=
  spl.sub_isGainOf x y

-- Gains compose by the *ordinary* certified addition — ratio-scale, gate by `trivial`:
-- a 20 dB stage after a 14 dB stage is a 34 dB chain.
example : Quantity.add DifferenceKind.ofScale
    (⟨20⟩ : Quantity spl.gainKind Int) ⟨14⟩ = ⟨34⟩ := rfl

/-! ## The chart, at `Float` -/

-- 0.2 Pa re 20 µPa: `20·lg(10⁴)` = 80 dB.
#guard Float.abs
    ((spl.ofRoot (⟨0.00002⟩ : Quantity soundPressure Float) ⟨0.2⟩).magnitude - 80.0) < 1e-9

-- The classic: two incoherent 94 dB sources are ≈97 dB — 3 dB up, not 188.
#guard ((spl.combineEnergetic (⟨94⟩ : Quantity spl.toKind Float) ⟨94⟩).magnitude
    - 97.0102999566398).abs < 1e-9

-- Same dB figure, two meanings, told apart by the kind: a ×10 field ratio is 20 dB at a
-- root-power kind, and a ×100 power ratio is 20 dB at a power kind.
#guard ((eFieldLevel.ofRoot (⟨1.0⟩ : Quantity eField Float) ⟨10.0⟩).magnitude
    - 20.0).abs < 1e-9
#guard ((dBm.ofRoot (⟨1.0⟩ : Quantity elPower Float) ⟨100.0⟩).magnitude
    - 20.0).abs < 1e-9
example : eFieldLevel.toKind ≠ dBm.toKind := by decide

-- And the energetic combination is role-independent: two equal field levels also combine
-- ≈3 dB up (incoherent sources add in *power*, whatever the level's role).
#guard ((eFieldLevel.combineEnergetic (⟨40⟩ : Quantity eFieldLevel.toKind Float) ⟨40⟩).magnitude
    - 43.0102999566398).abs < 1e-9

end PropertyKindCalculus.Tests.Level

end -- pkc-blanket-expose
end -- pkc-blanket
