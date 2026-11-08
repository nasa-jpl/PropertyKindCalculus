module

public import PropertyKindCalculus.Kind
public import PropertyKindCalculus.Quantity
public import PropertyKindCalculus.Frame

/-!
# Clocked time — a time referenced to a clock

A *time* read off a clock is a point on that clock's axis: an **interval-scale** quantity
(`timestamp`), whose zero is the clock's own arbitrary origin, so two readings subtract into a
**duration** (ratio scale) and nothing multiplies or divides them. The clock is a `Frame`: the
identified reference the readings are relative to, exactly as a coordinate frame is for
components. `ClockedTime clock R` is therefore `InFrame clock .scalar timestamp R`, and the
frame index is what keeps a reading of one clock from being combined with a reading of another.

This is the kind of property a time model (MARS's `Time` instance of a network, SysML's
`@TimeModel`) is an instance of, at any carrier `R` with the needed algebra — `Nat` ticks,
`Rat`, `Real` seconds. `sub`/`shift` are the only operations: a duration between two readings
of the same clock, and a reading moved by a duration. -/

public section Interface

namespace PropertyKindCalculus.Paradigm.Clocked

open PropertyKindCalculus

/-- A reading of a clock — interval scale: differences mean something, ratios do not. -/
@[expose] def timestamp : KindOfProperty := { id := "clock timestamp", scale := .interval }

/-- The span between two readings of one clock — ratio scale (a true zero, "twice as long"). -/
@[expose] def duration : KindOfProperty := { id := "duration", scale := .ratio }

theorem timestamp_ne_duration : timestamp ≠ duration := by decide

/-- Readings subtract (interval scale licenses `−`). -/
theorem timestamp_difference : DifferenceKind timestamp := DifferenceKind.ofScale

/-- Durations add (ratio scale licenses `+`). -/
theorem duration_difference : DifferenceKind duration := DifferenceKind.ofScale

/-- **A time referenced to a clock**: a `timestamp` quantity in the clock's frame. -/
abbrev ClockedTime (clock : Frame) (R : Type) := InFrame clock .scalar timestamp R

/-- A duration, at carrier `R`. -/
abbrev Duration (R : Type) := Quantity duration R

namespace ClockedTime

variable {clock : Frame} {R : Type}

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

/-- Shifting by a duration and reading the duration back are inverse (`Int` carrier; the core
stays Mathlib-free, so the law is stated per carrier). -/
theorem sub_shift_int (t : ClockedTime clock Int) (d : Duration Int) : (t.shift d).sub t = d := by
  apply Quantity.ext; simp; omega

/-- The reading `t.sub u` after `u` is `t` (`Int` carrier). -/
theorem shift_sub_int (t u : ClockedTime clock Int) : u.shift (t.sub u) = t := by
  cases t with | mk q => cases q with | mk r =>
  show (⟨⟨u.value + (r - u.value)⟩⟩ : ClockedTime clock Int) = ⟨⟨r⟩⟩
  congr 2; omega

/-- `sub_shift` in ticks (`Nat`, no negatives). -/
theorem sub_shift_nat (t : ClockedTime clock Nat) (d : Duration Nat) : (t.shift d).sub t = d := by
  apply Quantity.ext; simp

/-- `shift_sub` in ticks: needs `u` no later than `t` (truncated subtraction). -/
theorem shift_sub_nat (t u : ClockedTime clock Nat) (h : u.value ≤ t.value) :
    u.shift (t.sub u) = t := by
  cases t with | mk q => cases q with | mk r =>
  show (⟨⟨u.value + (r - u.value)⟩⟩ : ClockedTime clock Nat) = ⟨⟨r⟩⟩
  simp only [value] at h ⊢; congr 2; omega

end ClockedTime

/-- Clock readings in ticks (MARS's `Time Nat`). -/
abbrev TickTime (clock : Frame) := ClockedTime clock Nat

/-- Clock readings on a dense clock (MARS's `Time Rat`). -/
abbrev RatTime (clock : Frame) := ClockedTime clock Rat

end PropertyKindCalculus.Paradigm.Clocked
