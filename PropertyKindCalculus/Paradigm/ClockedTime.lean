module

public import PropertyKindCalculus.Kind
public import PropertyKindCalculus.Quantity
public import PropertyKindCalculus.Frame

/-!
# Clocked time — a time referenced to a clock

A *time* read off a clock is a point on that clock's axis: an **interval-scale** quantity
(`timestamp`), whose zero is the clock's own arbitrary origin, so two readings subtract into a
**duration** (ratio scale) and nothing else combines them — in particular two readings do not
*add* (the sum moves with the origin), and a reading of one clock is not a reading of another
(the origins differ). The clock is a `Frame`: the identified reference the readings are relative
to, as a coordinate frame is for components.

`ClockedTime clock R` is deliberately **its own structure**, indexed by the clock, and *not* an
`InFrame` alias: `InFrame`'s generic `add` (licensed by a `DifferenceKind`) and `toFrameScalar`
(scalars are frame-invariant, readings are not) are exactly the operations a clock reading must
not have. No `DifferenceKind timestamp` is exposed. The licensed operations are `sub` (reading −
reading = duration), `shift` (reading + duration = reading), and `convert` across clocks under an
explicit `ClockOffset`.

This is the kind of property a time model (MARS's `Time` instance of a network, SysML's
`@TimeModel`) is an instance of, at any carrier `R` — `Nat` ticks, `Rat`, `Real` seconds. -/

public section Interface

namespace PropertyKindCalculus.Paradigm.Clocked

open PropertyKindCalculus

/-- A reading of a clock — interval scale: differences mean something, ratios do not. -/
@[expose] def timestamp : KindOfProperty := { id := "clock timestamp", scale := .interval }

/-- The span between two readings of one clock — ratio scale (a true zero, "twice as long"). -/
@[expose] def duration : KindOfProperty := { id := "duration", scale := .ratio }

theorem timestamp_ne_duration : timestamp ≠ duration := by decide

/-- Durations add (ratio scale licenses `+`). There is *no* such witness for `timestamp`: a
reading is a point on an affine axis, and adding two points is meaningless. -/
theorem duration_difference : DifferenceKind duration := DifferenceKind.ofScale

/-- A duration, at carrier `R`. -/
abbrev Duration (R : Type) := Quantity duration R

/-- **A time referenced to a clock**: a `timestamp` reading on `clock`'s axis. The clock is a
phantom index — the only way to relate readings of two clocks is `ClockedTime.convert` under an
explicit `ClockOffset`. -/
structure ClockedTime (clock : Frame) (R : Type) where
  /-- The reading as a `timestamp` quantity. -/
  q : Quantity timestamp R

/-- **The offset between two clocks**: `b`'s reading minus `a`'s at the same instant (a
duration), the evidence `convert` needs to re-reference a reading. -/
structure ClockOffset (a b : Frame) (R : Type) where
  /-- `b − a`, at any one instant. -/
  d : Duration R

namespace ClockedTime

variable {clock a b : Frame} {R : Type}

/-- A reading from its value on the clock's axis. -/
@[expose] def ofValue (r : R) : ClockedTime clock R := ⟨⟨r⟩⟩

/-- The value on the clock's axis. -/
@[expose] def value (t : ClockedTime clock R) : R := t.q.magnitude

@[simp] theorem value_ofValue (r : R) : (ofValue (clock := clock) r).value = r := rfl

/-- The duration from `u` to `t` — two readings of the *same* clock, by the frame index. -/
@[expose] def sub [Sub R] (t u : ClockedTime clock R) : Duration R := ⟨t.value - u.value⟩

/-- The reading `d` after `t`, on the same clock. -/
@[expose] def shift [Add R] (t : ClockedTime clock R) (d : Duration R) : ClockedTime clock R :=
  ⟨⟨t.value + d.magnitude⟩⟩

@[simp] theorem value_shift [Add R] (t : ClockedTime clock R) (d : Duration R) :
    (t.shift d).value = t.value + d.magnitude := rfl

@[simp] theorem magnitude_sub [Sub R] (t u : ClockedTime clock R) :
    (t.sub u).magnitude = t.value - u.value := rfl

@[ext] theorem ext {t u : ClockedTime clock R} (h : t.value = u.value) : t = u := by
  cases t with | mk q => cases q; cases u with | mk q' => cases q'; cases h; rfl

/-- Re-reference a reading of clock `a` to clock `b` under the offset `b − a`. The *only*
cross-clock operation; there is no relabelling. -/
@[expose] def convert [Add R] (o : ClockOffset a b R) (t : ClockedTime a R) : ClockedTime b R :=
  ⟨⟨t.value + o.d.magnitude⟩⟩

@[simp] theorem value_convert [Add R] (o : ClockOffset a b R) (t : ClockedTime a R) :
    (convert o t).value = t.value + o.d.magnitude := rfl

/-- Converting both readings leaves their duration unchanged (`Int` carrier). -/
theorem sub_convert_int (o : ClockOffset a b Int) (t u : ClockedTime a Int) :
    (convert o t).sub (convert o u) = t.sub u := by
  apply Quantity.ext; simp; omega

/-- Shifting by a duration and reading the duration back are inverse (`Int` carrier; the core
stays Mathlib-free, so the law is stated per carrier). -/
theorem sub_shift_int (t : ClockedTime clock Int) (d : Duration Int) : (t.shift d).sub t = d := by
  apply Quantity.ext; simp; omega

/-- The reading `t.sub u` after `u` is `t` (`Int` carrier). -/
theorem shift_sub_int (t u : ClockedTime clock Int) : u.shift (t.sub u) = t := by
  apply ext; simp; omega

/-- `sub_shift` in ticks (`Nat`, no negatives). -/
theorem sub_shift_nat (t : ClockedTime clock Nat) (d : Duration Nat) : (t.shift d).sub t = d := by
  apply Quantity.ext; simp

/-- `shift_sub` in ticks: needs `u` no later than `t` (truncated subtraction). -/
theorem shift_sub_nat (t u : ClockedTime clock Nat) (h : u.value ≤ t.value) :
    u.shift (t.sub u) = t := by
  apply ext; simp; omega

end ClockedTime

/-- Clock readings in ticks (MARS's `Time Nat`). -/
abbrev TickTime (clock : Frame) := ClockedTime clock Nat

/-- Clock readings on a dense clock (MARS's `Time Rat`). -/
abbrev RatTime (clock : Frame) := ClockedTime clock Rat

end PropertyKindCalculus.Paradigm.Clocked
