/-
# Validation probes — the specialization lift (R2)

Inhabitation, boundary, and functoriality probes for `Quantity.widen`, `Quantity.addAt`,
`Quantity.leAt` and the curated `KindJoin` table (`PropertyKindCalculus.SpecializationLift`).
The probes check the properties the module's discipline rests on:

  * widening moves only the classification index, is the identity along `refl`, and
    composes along `trans`;
  * a registered join elaborates `T + V` through the table, landing *at the join* with the
    magnitude computed — and the join operator **is** the named `addAt` (`rfl`);
  * the lift is one-way and curated: the sum is not available at either sub-kind, an
    unregistered kind pair does not add, and there is no narrowing back down the lattice.
-/

import PropertyKindCalculus

namespace PropertyKindCalculus.Tests.SpecializationLift

open PropertyKindCalculus
open scoped PropertyKindCalculus.OperatorTable

/-- Length, the join of the family. -/
def lengthK : KindOfProperty := { id := "length", scale := .ratio }
/-- Width, individuated by its examination. -/
def widthK : KindOfProperty :=
  { id := "width", scale := .ratio, examPrinciple := some "extent along the minor axis" }
/-- Height, individuated by its examination. -/
def heightK : KindOfProperty :=
  { id := "height", scale := .ratio, examPrinciple := some "extent against gravity" }
/-- Colour, a nominal kind in no lattice with the others. -/
def colourK : KindOfProperty := { id := "colour", scale := .nominal }

/-- The family's direct-parent edges. -/
inductive LenEdge : KindOfProperty → KindOfProperty → Prop where
  | width  : LenEdge widthK lengthK
  | height : LenEdge heightK lengthK

/-- The one curated join entry: width and height meet at length. -/
instance : KindJoin LenEdge widthK heightK lengthK :=
  ⟨.of_edge .width, .of_edge .height, .ofScale⟩

-- Inhabitation: widening re-classifies without touching the magnitude.
example : ((⟨3⟩ : Quantity widthK Int).widen (Specializes.of_edge LenEdge.width)).magnitude = 3 := rfl
-- Functoriality: identity along `refl`, composition along `trans` — both `rfl`.
example (x : Quantity widthK Int) : x.widen (Specializes.refl (E := LenEdge) _) = x := rfl
example (x : Quantity widthK Int) (h₁ : Specializes LenEdge widthK lengthK)
    (h₂ : Specializes LenEdge lengthK lengthK) :
    (x.widen h₁).widen h₂ = x.widen (h₁.trans h₂) := rfl

-- A registered join elaborates and computes, landing at the join: `3 + 4 = 7`, a length.
example : ((⟨3⟩ : Quantity widthK Int) + (⟨4⟩ : Quantity heightK Int)).magnitude = 7 := rfl
-- Result-kind pin (the curation guard), as for the operator table.
example : ((⟨3⟩ : Quantity widthK Int) + (⟨4⟩ : Quantity heightK Int))
    = (⟨7⟩ : Quantity lengthK Int) := rfl
-- The operator is the named form.
example (x : Quantity widthK Int) (y : Quantity heightK Int) :
    x + y = Quantity.addAt (Specializes.of_edge LenEdge.width)
      (Specializes.of_edge LenEdge.height) .ofScale x y := rfl
-- A registered join is a witnessed comparability fact.
example : MutuallyComparable LenEdge widthK heightK :=
  KindJoin.comparable (inferInstance : KindJoin LenEdge widthK heightK lengthK)
-- The comparison at the join is stated on the magnitudes.
example : Quantity.leAt (E := LenEdge) (.of_edge .width) (.of_edge .height) (.ofScale)
    (⟨3⟩ : Quantity widthK Int) (⟨4⟩ : Quantity heightK Int) := by
  show (3 : Int) ≤ 4
  decide

-- Boundary: the sum is not available at either sub-kind — the join, and only the join.
#check_failure (((⟨3⟩ : Quantity widthK Int) + (⟨4⟩ : Quantity heightK Int)
  : Quantity widthK Int))
-- Boundary: an unregistered pair does not add — colour is in no lattice with width.
#check_failure (fun (w : Quantity widthK Int) (c : Quantity colourK Int) => w + c)

end PropertyKindCalculus.Tests.SpecializationLift
