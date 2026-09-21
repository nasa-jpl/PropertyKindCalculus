/-
# Validation probes — the `Set.Icc` bridge for kind-indexed intervals (`IccQ.toIcc`)

Inhabitation and axiom-profile probes for the Mathlib-backed bridge
`PropertyKindCalculus.IccQ.toIcc` / `mem_toIcc` (`PropertyKindCalculus.BoundsReal`), the
seam that lets an order/analysis theorem quantify over the points of a direction-locked
`IccQ` through Mathlib's `Set.Icc`. The probes check the two properties the module exists
for, at the ℝ carrier the quantity laws are proved over:

  * `toIcc` projects to exactly `Set.Icc lo hi` (the endpoints in the right roles);
  * `mem_toIcc` is definitional (`Iff.rfl`), so a `Set.Icc` membership fact and the box's
    own kinded `IccQ.Mem` are interchangeable with no rewriting — the property a
    downstream corollary relies on to delegate to a Mathlib lemma.

Both `toIcc` and the `Iff.rfl` bridge are `Preorder`-generic and depend on **no axioms** —
the ℝ carrier enters only the probe witnesses (`norm_num`), not the bridge itself; the gate
confirms no `sorryAx`.
-/

import PropertyKindCalculus.BoundsReal
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

namespace PropertyKindCalculus.Tests.BoundsReal

open PropertyKindCalculus

/-- Length, a ratio kind (scale allows order), for the probes below. -/
def lengthK : KindOfProperty := { id := "length", scale := .ratio }

/-- The box `[0, 10]` of lengths over the proof carrier `ℝ`. -/
noncomputable def box : IccQ lengthK ℝ := IccQ.of ⟨0⟩ ⟨10⟩

-- `toIcc` projects to the standard interval with the endpoints in their roles.
example : box.toIcc = Set.Icc (0 : ℝ) 10 := rfl

-- The membership bridge is definitional: a `Set.Icc` fact *is* the box's kinded
-- membership. Carry a `Set.Icc` proof across to the kinded side …
example : box.Mem ⟨5⟩ :=
  (IccQ.mem_toIcc box ⟨5⟩).mp (show (5 : ℝ) ∈ Set.Icc (0 : ℝ) 10 from ⟨by norm_num, by norm_num⟩)

-- … and a kinded `IccQ.Mem` proof (the two directional facts `0 ≤ 5`, `5 ≤ 10`) back to
-- the set.
example : (5 : ℝ) ∈ box.toIcc :=
  (IccQ.mem_toIcc box ⟨5⟩).mpr (show (0 : ℝ) ≤ 5 ∧ (5 : ℝ) ≤ 10 from ⟨by norm_num, by norm_num⟩)

-- The seam is `Iff.rfl` — the two membership statements are the *same* proposition, so a
-- proof of one is a proof of the other with no coercion.
example : ((5 : ℝ) ∈ box.toIcc) = box.Mem ⟨5⟩ := rfl

/-- info: 'PropertyKindCalculus.IccQ.mem_toIcc' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms IccQ.mem_toIcc

end PropertyKindCalculus.Tests.BoundsReal
