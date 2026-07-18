/-
# Validation probes — aggregation (R9)

Inhabitation and axiom-profile probes for extensivity. The extensive-aggregation capstone is a
`∀`-quantified law over the mereology of systems; the danger it must avoid is being proved for an
`Extensive` predicate that nothing satisfies. So the probe *builds* a genuine extensive
measurement (leaf-counting mass) and drives the law through a **depth-2** decomposition — the
Rule-2 boundary that exercises the inductive step, not just a single atom — then re-exhibits the
source's non-extensive counterexample so the predicate is shown to be discriminating.
-/

import PropertyKindCalculus

namespace PropertyKindCalculus.Tests.Aggregation

open PropertyKindCalculus

/-- Mass, a ratio kind — the archetypal extensive quantity. -/
def massKind : KindOfProperty := { id := "mass", scale := .ratio }

/-- The number of atomic parts under a decomposition. -/
def countLeaves : Decomposition → Int
  | .atom _      => 1
  | .union a b   => countLeaves a + countLeaves b

/-- A genuinely additive mass measurement: each part reads its own leaf count, so a union reads
the sum of its parts' readings — the defining shape of an extensive quantity. -/
def massOf : Measurement := fun d => { kind := massKind, numeral := countLeaves d, reference := "kg" }

/-- `massOf` is extensive for `massKind`: every part is of kind `massKind` (`ofKind`), and a union
reads as the sum of its parts (`additive`) — both by `rfl`, so the witness is real, not assumed. -/
theorem massOf_extensive : Extensive massKind massOf := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- Three atomic sub-systems. -/
def s₁ : System := { id := "s1" }
def s₂ : System := { id := "s2" }
def s₃ : System := { id := "s3" }

/-- A depth-2 decomposition `(s₁ ⊔ s₂) ⊔ s₃` — nested, so the aggregation recursion is exercised. -/
def whole : Decomposition := .union (.union (.atom s₁) (.atom s₂)) (.atom s₃)

-- Inhabitation (Rule 2 — the non-degenerate, nested case): the value on the *whole* equals the
-- sum over *all three* atomic parts, obtained by applying the capstone to a real decomposition.
theorem r9_whole_eq_leafSum : (massOf whole).numeral = leafSum massOf whole :=
  extensive_additive massOf_extensive whole

-- and it computes to the leaf count, 3.
#guard (massOf whole).numeral == 3
#guard leafSum massOf whole == 3

-- Boundary — the predicate is discriminating: volume on mixing is *not* extensive (96 < 50 + 50),
-- so `Extensive` genuinely rules something out. (Re-exhibits the source counterexample.)
theorem r9_mixing_not_extensive : ¬ Extensive volume volMix := mixing_subadditive.2

/-- info: 'PropertyKindCalculus.extensive_additive' depends on axioms: [propext] -/
#guard_msgs in #print axioms extensive_additive

/-- info: 'PropertyKindCalculus.mixing_subadditive' does not depend on any axioms -/
#guard_msgs in #print axioms mixing_subadditive

end PropertyKindCalculus.Tests.Aggregation
