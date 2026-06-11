/-
# Worked example: length, width, height

Demonstrates the three theses of the design discussion as *checked* facts:

  1. `width` and `height` are **distinct kinds** that **specialize** `length`
     (individuated by their examination principle, per Dybkær §7.5).
  2. They are nonetheless **mutually comparable** (they share super-kind
     `length`) — so combining them is *possible*, but only via an explicit
     up-cast to `length`, never silently.
  3. "The width of this pencil" is an **individual property** — a *term*
     that *instantiates* `width`, NOT a subtype of it.

This module is part of the separate `Examples` library; it imports the core
`KindCalculus` library like any downstream consumer would.
-/

import KindCalculus

namespace KindCalculus.Examples

open KindCalculus

/-- The broad rational kind-of-quantity of dimension length. -/
def length : KindOfProperty := { id := "length", scale := .ratio }

/-- A sub-kind of `length`, individuated by its examination principle. -/
def width : KindOfProperty :=
  { id := "width", scale := .ratio, examPrinciple := some "caliper-perpendicular" }

/-- Another sub-kind of `length`, with a different examination principle. -/
def height : KindOfProperty :=
  { id := "height", scale := .ratio, examPrinciple := some "caliper-vertical" }

/-- This application's system of quantities: the direct-parent edges. -/
inductive Edge : KindOfProperty → KindOfProperty → Prop
  | width_length  : Edge width length
  | height_length : Edge height length

-- (1a) width specializes length …
example : Specializes Edge width length := Specializes.of_edge .width_length

-- (1b) … but is a DISTINCT kind: it will not silently unify with length,
--      so it cannot be passed where a bare length (or a height) is required.
example : width ≠ length := by decide
example : width ≠ height := by decide

-- (1c) every one of them is a kind-of-quantity (rational scale ⇒ has magnitude).
example : width.IsQuantity := KindOfProperty.rational_isQuantity rfl

-- (2) width and height are mutually comparable: they share super-kind length.
example : MutuallyComparable Edge width height :=
  ⟨length, Specializes.of_edge .width_length, Specializes.of_edge .height_length⟩

-- (3) the width of a *specific* pencil is an individual property: a TERM that
--     instantiates `width` and characterizes the pencil — not a subtype.
def pencil : Object := { id := "pencil-0001" }
def pencilWidth : IndividualProperty := { kind := width, carrier := pencil }

example : pencilWidth.kind = width := rfl
example : pencilWidth.carrier = pencil := rfl

end KindCalculus.Examples
