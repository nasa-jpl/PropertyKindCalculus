/-
# Validation probes — a portion and its total as roles

Inhabitation, boundary, and axiom-profile probes for `Part`/`Whole`
(`PropertyKindCalculus.PartWhole`). The probes check the properties the module exists for:

  * the two roles cannot be swapped, including when the value is already kinded — same
    kind is the whole difficulty here, since a portion of a thing *is* a quantity of the
    thing's kind;
  * the relation between them is directional: there is no former with the total on the
    left, so "the whole is at most the part" cannot be stated;
  * the fraction eliminator writes the division once, in the only order the roles admit,
    and crosses to a *different* kind under a `QuotientKind` edge — which the scale gate
    genuinely enforces;
  * the roles stay visible to the incidence harvest as carrier field paths (`p.q`, `w.q`),
    and the crossing renders as the edge it is.
-/

module

public import PropertyKindCalculus
meta import PropertyKindCalculus
public import PropertyKindCalculus.KindIncidence
meta import PropertyKindCalculus.KindIncidence
-- Private scope only: the checks below reduce through bodies sealed in the core
-- library; `import all` gives this file the reduction without exposing them.
import all PropertyKindCalculus.Bounds
import all PropertyKindCalculus.IndividualQuantity

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.PartWhole

open PropertyKindCalculus

/-- A probe kind — an unnormalized per-tap weight, the shape a portion is read from. -/
def rawWeightK : KindOfProperty := { id := "part-whole probe raw weight", scale := .ratio }
/-- The role the division *creates*: a share of the total, which neither operand carried. -/
def coverageK : KindOfProperty := { id := "part-whole probe coverage", scale := .ratio }
/-- A second quantity kind — a portion of one total is not a portion of another. -/
def pixelCountK : KindOfProperty := { id := "part-whole probe pixel count", scale := .ratio }
/-- An ordinal probe kind: order but no division, so no fraction of it. -/
def rankK : KindOfProperty := { id := "part-whole probe rank", scale := .ordinal }

/-- One tap's raw weight. -/
def tap : Part rawWeightK Float := ⟨⟨1.5⟩⟩
/-- The kernel's raw total. -/
def total : Whole rawWeightK Float := ⟨⟨6.0⟩⟩

/-! ## The eliminator — the division is written once, here -/

#guard (tap.fractionOf coverageK total).magnitude == 0.25
#guard tap.withinWhole total == true
#guard (⟨⟨9.0⟩⟩ : Part rawWeightK Float).withinWhole total == false
#guard (⟨⟨6.0⟩⟩ : Part rawWeightK Float).withinWhole total == true

/-! ## The carrier bridge — counts reach the eliminator in their roles

The common shape: a portion and its total are born as *counts* and the fraction is wanted
at `Float`. Both sides cross in the same step, each still in its own role, so the pair
reaches `fractionOf` at one carrier without ever being two loose numbers. -/

/-- A count kind — valid items within a window, the shape a coverage is read from. -/
def itemCountK : KindOfProperty := { id := "part-whole probe item count", scale := .ratio }

#guard (((⟨⟨3⟩⟩ : Part itemCountK Nat).castCarrier Nat.toFloat).fractionOf coverageK
  ((⟨⟨4⟩⟩ : Whole itemCountK Nat).castCarrier Nat.toFloat)).magnitude == 0.75
-- Swapped, it is still a type error after the cast — a representation change is not a
-- role change.
#check_failure (Part.fractionOf coverageK
  ((⟨⟨4⟩⟩ : Whole itemCountK Nat).castCarrier Nat.toFloat)
  ((⟨⟨3⟩⟩ : Part itemCountK Nat).castCarrier Nat.toFloat))

/-! ## Boundary (Rule 2) — what the roles make unwritable -/

/-- A normalization step, the shape a bare pair of same-kind magnitudes leaves open to a
swapped call — where the swap is silent, returning a share above one. -/
def normalize (p : Part rawWeightK Float) (w : Whole rawWeightK Float) :
    Quantity coverageK Float :=
  p.fractionOf coverageK w

example : Quantity coverageK Float := normalize tap total
-- The swap is a type error …
#check_failure (normalize total tap)
-- … and the kind alone does not separate the roles: a portion and its total are the same
-- kind of quantity, which is exactly why the role has to be stated where each is born.
#check_failure (normalize (⟨1.5⟩ : Quantity rawWeightK Float) total)
#check_failure (normalize tap (⟨6.0⟩ : Quantity rawWeightK Float))

-- Directional: there is no `Whole.WithinWhole`, so the total cannot be asked to sit
-- inside the portion.
set_option linter.unusedVariables false in
#check_failure (fun (p : Part rawWeightK Float) (w : Whole rawWeightK Float) =>
  w.WithinWhole p)

-- Kind-gated: a portion of one quantity is not a portion of another's total.
#check_failure (fun (p : Part pixelCountK Float) => p.withinWhole total)
#check_failure (fun (p : Part pixelCountK Float) => p.fractionOf coverageK total)

-- Scale-gated: the fraction is a genuine kind crossing, licensed by a `QuotientKind`
-- edge — an ordinal kind divides into nothing, so the autoParam cannot be discharged.
#check_failure ((⟨⟨2.0⟩⟩ : Part rankK Float).fractionOf coverageK ⟨⟨4.0⟩⟩)

/-! ## Axiom profile -/

/-- info: 'PropertyKindCalculus.Part.fractionOf_magnitude' does not depend on any axioms -/
#guard_msgs in #print axioms Part.fractionOf_magnitude

/-- info: 'PropertyKindCalculus.Part.withinWhole_eq_true' depends on axioms: [propext] -/
#guard_msgs in #print axioms Part.withinWhole_eq_true

/-! ## The roles stay visible to the incidence harvest -/

/--
info: kind ports of 'PropertyKindCalculus.Tests.PartWhole.normalize':
input p.q : rawWeightK
input w.q : rawWeightK
output result : coverageK
-/
#guard_msgs in #kind_ports normalize

/--
info: kind graph of 'PropertyKindCalculus.Tests.PartWhole.normalize':
input p.q : rawWeightK
input w.q : rawWeightK
output result : coverageK
rawWeightK / rawWeightK → coverageK ⟨p.q, w.q⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph normalize

end PropertyKindCalculus.Tests.PartWhole

end Blanket
