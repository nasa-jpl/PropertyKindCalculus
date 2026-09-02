/-
# The link budget — levels and gains on the catalogue's power kind

The dB layer, on `LevelKind`: dBm and dBW as *levels of the catalogue's 6-45 power*
(Exhibit E minted an ad hoc root; the promotion roots the levels in the standard),
dBV as a root-power level of 6-11.3, and the worked link budget — exact at `Int`.

What the construction enforces, each pinned below:

* **The reference is kind identity** — dBm ≠ dBW by `decide`, though both are
  `10·lg` of a power.
* **Levels never add** — the level kind is ordinal; `DifferenceKind` is unprovable
  there, so 30 dBm + 30 dBm is not 60 dBm *and is not writable*.
* **Gains are the extent** — the reference cancels in every difference, so an
  amplifier's dB figure serves dBm and dBW alike (`rfl`), while a power gain and a
  voltage gain stay two kinds (the 10/20 factor is kind, not convention).
-/

import ForPhysLib.Electromagnetism.Annex.Kinds
import PropertyKindCalculus.Level

namespace ForPhysLib.Electromagnetism.Annex.Levels

open PropertyKindCalculus
open ForPhysLib.Electromagnetism.Annex.Kinds

/-- Power level re 1 mW — the dBm, rooted at the catalogue's 6-45. -/
def dBm : LevelKind := ⟨power, .power, "1 mW"⟩

/-- Power level re 1 W — the dBW: same root, same role, different reference. -/
def dBW : LevelKind := ⟨power, .power, "1 W"⟩

/-- Voltage level re 1 V — the dBV: a *root-power* level (the factor is 20, and
that is part of the kind). -/
def dBV : LevelKind := ⟨voltage, .rootPower, "1 V"⟩

/-- **The reference is kind identity** — dBm and dBW are different kinds. -/
theorem dBm_ne_dBW : dBm.toKind ≠ dBW.toKind := by decide

/-- …but their gains are one kind: the reference cancels in every difference, so an
amplifier's dB figure serves either level. -/
theorem gain_shared : dBm.gainKind = dBW.gainKind := rfl

/-- A power gain is not a voltage gain — the 10/20 role survives into the extent. -/
theorem gain_dBm_ne_gain_dBV : dBm.gainKind ≠ dBV.gainKind := by decide

/-- A level kind is ordinal — no certified sum can form at it. -/
theorem dBm_not_allowsDifference : ¬ dBm.toKind.scale.AllowsDifference :=
  dBm.toKind_not_allowsDifference

-- Two transmitter levels do not add: `DifferenceKind` is unprovable at the ordinal
-- level kind, so the certified sum never forms — 30 dBm + 30 dBm is not writable.
#check_failure fun (x y : Quantity dBm.toKind Int) =>
  Quantity.add DifferenceKind.ofScale x y

/-- **A worked link budget**, exact at `Int`: 30 dBm out, +3 dB Tx antenna, −100 dB
path, +2 dB Rx antenna → −65 dBm at the receiver. Levels shift by gains; gains are
the only thing that ever adds. -/
example :
    dBm.shift (dBm.shift (dBm.shift (⟨30⟩ : Quantity dBm.toKind Int) ⟨3⟩) ⟨-100⟩) ⟨2⟩
      = ⟨-65⟩ := rfl

end ForPhysLib.Electromagnetism.Annex.Levels
