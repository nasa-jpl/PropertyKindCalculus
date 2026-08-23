/-
# Validation probes — extent and position as roles on one axis kind

Inhabitation, boundary, and axiom-profile probes for `Extent`/`Position`
(`PropertyKindCalculus.Axis`). The probes check the properties the module exists for:

  * the two roles cannot be swapped (a count handed to a position slot is a type error,
    *including* when it is already kinded — the axis kind alone does not separate them),
    and the relation between them is directional: there is no former with the extent
    where the position goes;
  * every producer of a `Position` hands over the range obligation — the checked gate,
    the last position, the clamping eliminator, and the enumeration — so a consumer never
    re-states `i < n`;
  * the half-open reading and the axis's own closed interval `[0, n−1]` agree, so
    `IccQ.memb` is a range test on an axis with no endpoints spelled by hand;
  * the empty axis yields nothing rather than a fabricated position — `none` from every
    partial producer, an empty enumeration, zero loop iterations;
  * the roles stay *visible*: the incidence harvest reads them as carrier field paths
    (`n.q`, `i.q`), so putting a quantity into a role does not cost the provenance graph
    a port.
-/

import PropertyKindCalculus
import PropertyKindCalculus.KindIncidence

namespace PropertyKindCalculus.Tests.Axis

open PropertyKindCalculus

/-- A probe axis — a lookup table's row axis, in miniature. -/
def rowAxisK : KindOfProperty := { id := "axis probe row axis", scale := .ratio }
/-- A second probe axis: two axes that are both "row-shaped" are still two axes. -/
def colAxisK : KindOfProperty := { id := "axis probe column axis", scale := .ratio }
/-- A nominal probe kind — no order, so no axis interval. -/
def colourK : KindOfProperty := { id := "axis probe colour", scale := .nominal }

/-- An axis of eight positions. -/
def n8 : Extent rowAxisK Nat := ⟨⟨8⟩⟩
/-- The empty axis. -/
def n0 : Extent rowAxisK Nat := ⟨⟨0⟩⟩
/-- A position on the eight-position axis. -/
def p3 : Position rowAxisK Nat := ⟨⟨3⟩⟩

/-! ## The gate — a raw index becomes a position only against the extent that bounds it -/

#guard (n8.posOf? 0).isSome
#guard (n8.posOf? 7).isSome
#guard (n8.posOf? 8).isNone
#guard (n8.posOf? 99).isNone
#guard (n0.posOf? 0).isNone

-- The last position, the clamping eliminator, and the enumeration are the other three
-- producers; each lands on the axis (their theorems below), and each declines to invent
-- a position on an axis that has none.
#guard (n8.lastPos?.map (·.q.magnitude)) == some 7
#guard n0.lastPos?.isNone
#guard (n8.clampPos? 3 |>.map (·.q.magnitude)) == some 3
#guard (n8.clampPos? 99 |>.map (·.q.magnitude)) == some 7
#guard n0.clampPos? 0 |>.isNone
#guard n8.positions.map (·.q.magnitude) == #[0, 1, 2, 3, 4, 5, 6, 7]
#guard n0.positions.size == 0
#guard n8.isEmpty == false
#guard n0.isEmpty == true

/-! ## The axis as an interval — the range obligation, derived from the extent -/

#guard (n8.span?.map (fun I => I.lo.q.magnitude)) == some 0
#guard (n8.span?.map (fun I => I.hi.q.magnitude)) == some 7
#guard (n8.span?.map (fun I => I.memb ⟨7⟩)) == some true
#guard (n8.span?.map (fun I => I.memb ⟨8⟩)) == some false
#guard n0.span?.isNone

-- The half-open reading, executably, on the same numbers.
#guard p3.within n8 == true
#guard (⟨⟨8⟩⟩ : Position rowAxisK Nat).within n8 == false
#guard p3.within n0 == false

/-! ## Walking the axis — in range by construction, nothing asserted in the body -/

/-- The `ForIn` instance yields positions, not bare counts: `i` arrives bound to its axis
and known to be on it. -/
def sumPositions (n : Extent rowAxisK Nat) : Nat := Id.run do
  let mut acc := 0
  for i in n do
    acc := acc + i.q.magnitude
  return acc

#guard sumPositions n8 == 28
#guard sumPositions n0 == 0

/-! ## Boundary (Rule 2) — what the roles make unwritable -/

set_option linter.unusedVariables false in
/-- A step taking both roles of one axis: the shape a bare pair of same-kind counts
leaves open to a swapped call. The extent binder is deliberately unread — the roles are
stated in the *signature*, which is where a call site gets them wrong. -/
def nodeOf (n : Extent rowAxisK Nat) (i : Position rowAxisK Nat) : Quantity rowAxisK Nat :=
  i.q

example : Quantity rowAxisK Nat := nodeOf n8 p3
-- The swap is a type error, which is the whole point …
#check_failure (nodeOf p3 n8)
-- … and being kinded is not enough on its own: a naked `Quantity rowAxisK Nat` fits
-- neither slot, so the role has to be stated where the value is born.
#check_failure (nodeOf n8 (⟨3⟩ : Quantity rowAxisK Nat))
#check_failure (nodeOf (⟨8⟩ : Quantity rowAxisK Nat) p3)

-- Directional: the relation exists only with the extent on the right. There is no
-- `Extent.Within`, so "the count lies within the index" cannot be written at all.
set_option linter.unusedVariables false in
#check_failure (fun (i : Position rowAxisK Nat) (n : Extent rowAxisK Nat) => n.Within i)

-- Kind-gated, as every same-kind comparison in this calculus is: a position on the
-- column axis cannot be tested against the row axis's extent.
#check_failure (fun (i : Position colAxisK Nat) => i.within n8)

-- Scale-gated: an axis presupposes order, so a nominal kind has no interval of
-- positions — the `OrderKind` autoParam cannot be discharged.
theorem colour_no_order : ¬ OrderKind colourK := fun h => h.allowsOrder
#check_failure (Extent.span? (⟨⟨3⟩⟩ : Extent colourK Nat))

/-! ## The guarantees, at concrete witnesses — each producer hands over the obligation -/

example : ∀ p, n8.posOf? 5 = some p → p.Within n8 := fun _ h => Extent.posOf?_within h
example : ∀ p, n8.lastPos? = some p → p.Within n8 := fun _ h => Extent.lastPos?_within h
example : ∀ p, n8.clampPos? 99 = some p → p.Within n8 := fun _ h => Extent.clampPos?_within h
example (h : 5 < n8.positions.size) : (n8.positions[5]).Within n8 :=
  Extent.positions_within h

-- The two readings of "in range" are one fact: `i < n` and `i ∈ [0, n−1]`.
example (I : IccQ rowAxisK Nat) (h : n8.span? = some I) : p3.Within n8 ↔ I.Mem p3.q :=
  Extent.within_iff_mem_span h p3

/-- info: 'PropertyKindCalculus.Extent.posOf?_within' depends on axioms: [propext] -/
#guard_msgs in #print axioms Extent.posOf?_within

/-- info: 'PropertyKindCalculus.Extent.positions_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Extent.positions_within

/-- info: 'PropertyKindCalculus.Extent.within_iff_mem_span' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Extent.within_iff_mem_span

/-! ## The roles stay visible to the incidence harvest

A quantity put into a role is carried by a container, and the harvest reads a container
by its carrier field paths — so stating the role costs the provenance graph nothing: the
step still has two input ports, now *named* by the roles they fill. -/

/--
info: kind ports of 'PropertyKindCalculus.Tests.Axis.nodeOf':
input n.q : rowAxisK
input i.q : rowAxisK
output result : rowAxisK
-/
#guard_msgs in #kind_ports nodeOf

/--
info: kind graph of 'PropertyKindCalculus.Tests.Axis.nodeOf':
input n.q : rowAxisK
input i.q : rowAxisK
output result : rowAxisK
rowAxisK → rowAxisK ⟨i.q⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph nodeOf

end PropertyKindCalculus.Tests.Axis
