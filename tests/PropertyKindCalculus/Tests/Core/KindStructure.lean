/-
# Validation probes — kind structure (R2, R3, R19)

Inhabitation and axiom-profile regression probes for the *kind-structure* requirement group.
Two checks per verifiable requirement (see `PropertyKindCalculus.Tests`):

  * **inhabitation / non-vacuity** — the requirement's theorem is applied to a *concrete*
    witness whose premise is discharged by `decide`/a constructor, so a theorem that were
    vacuous (empty universal, unsatisfiable premise) could not compile here;
  * **axiom profile** — `#guard_msgs in #print axioms …` pins each theorem's axiom set, so a
    proof relocated behind a `sorry` (which emits *no* warning on its caller) is caught.

R3 and R19 are *expressiveness* requirements: there is no theorem to gate, so the probe is the
typechecking construction itself (a kind is a type, an individual value a term; the object rides
in the type) together with R19's proved distinctness lemma.
-/

module

public import PropertyKindCalculus

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Tests.KindStructure

open PropertyKindCalculus

/-! ## R2 — specialization is a preorder with comparability, not identity -/

/-- A generic super-kind. -/
def propertyK : KindOfProperty := { id := "property", scale := .nominal }
/-- Length, a ratio kind that specializes `propertyK`. -/
def lengthK   : KindOfProperty := { id := "length",   scale := .ratio }
/-- Width, a ratio kind that specializes `lengthK`. -/
def widthK    : KindOfProperty := { id := "width",    scale := .ratio }

/-- The application-supplied direct-parent edges: `widthK ⊑ lengthK ⊑ propertyK`. -/
inductive Edge : KindOfProperty → KindOfProperty → Prop
  | wl : Edge widthK lengthK
  | lp : Edge lengthK propertyK

-- Inhabitation: a genuine two-step chain — `Specializes.trans` applied to *non-reflexive*
-- links, so the transitivity is exercised, not satisfied vacuously by `refl`.
theorem r2_chain : Specializes Edge widthK propertyK :=
  Specializes.trans (Specializes.of_edge .wl) (Specializes.of_edge .lp)

-- Comparability without identity: `widthK` and `lengthK` are mutually comparable (both are
-- lengths) yet distinct — the relation a description logic can record an instance of but not prove.
theorem r2_comparable : MutuallyComparable Edge widthK lengthK :=
  MutuallyComparable.of_specializes (Specializes.of_edge .wl)

/-- Along-x and along-y width: identical id, scale, and (later) dimension — separated *only* by
their examination principle. This is the silent-failure case: a dimension-only checker conflates
them; the examination principle forces distinct kinds. -/
def alongX : KindOfProperty := { id := "w", scale := .ratio, examPrinciple := some "along-x" }
def alongY : KindOfProperty := { id := "w", scale := .ratio, examPrinciple := some "along-y" }

-- Inhabitation: the premise `examPrinciple ≠ examPrinciple` is satisfiable (`decide`), so the
-- distinctness is real, not vacuous. Boundary note: the two kinds agree on *everything else*.
theorem r2_alongX_ne_alongY : alongX ≠ alongY :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- info: 'PropertyKindCalculus.Specializes.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Specializes.trans

/-- info: 'PropertyKindCalculus.KindOfProperty.distinct_of_examPrinciple' does not depend on any axioms -/
#guard_msgs in #print axioms KindOfProperty.distinct_of_examPrinciple

/-! ## R3 — general vs individual is type vs term (expressiveness) -/

-- A kind is a *type*; a particular measured value is a *term* of that type. That this
-- construction elaborates *is* the demonstration (there is no theorem to prove).
/-- This rectangle's length — an individual value (a term) of the kind `lengthK` (a type). -/
def aLength : Quantity lengthK Int := ⟨5⟩
-- A different kind is a *different type*: `aLength`'s kind is fixed in its type.
example : (aLength.magnitude) = 5 := rfl

/-! ## R19 — a quantity characterizes an object; object identity rides in the type -/

/-- Two soil samples (systems). -/
def soilA : System := { id := "soil-A" }
/-- A second soil sample. -/
def soilB : System := { id := "soil-B" }
/-- The water component. -/
def water : Component := { id := "water" }
/-- Volumetric water content, a ratio kind (dimension one). -/
def vwc : KindOfProperty := { id := "vol-water-content", scale := .ratio }

-- Expressiveness: the object rides in the *type* of an `IndividualQuantity`, so a value of
-- `soilA`'s vwc and a value of `soilB`'s vwc inhabit *different types* — combining them across
-- objects is a type error, checked here by the fact that each construction elaborates at its own
-- object index.
/-- `soilA`'s volumetric water content — object `soilA` carried in the type. -/
def vwcA : IndividualQuantity soilA vwc Int := ⟨30⟩
/-- `soilB`'s volumetric water content — a *different type* (object `soilB`). -/
def vwcB : IndividualQuantity soilB vwc Int := ⟨45⟩

/-- The sort both samples instantiate. -/
def soilS : SortOfSystem := ⟨"soil"⟩
/-- A different sort of system altogether. -/
def sedimentS : SortOfSystem := ⟨"sediment"⟩

-- The proved half of R19 at the kind level: two dedicated kinds that agree on component and
-- kind-of-property but differ in *sort* are provably distinct — the premise `soilS ≠ sedimentS`
-- is satisfiable (`decide`), so `distinct_of_sort` is applied non-vacuously.
theorem r19_distinct_by_sort :
    vwc.dedicatedTo soilS water ≠ vwc.dedicatedTo sedimentS water :=
  DedicatedKind.distinct_of_sort (by decide)

/-- info: 'PropertyKindCalculus.DedicatedKind.distinct_of_sort' does not depend on any axioms -/
#guard_msgs in #print axioms DedicatedKind.distinct_of_sort

-- Within one sort, the catalogue cannot individuate — and is not supposed to: dedicating
-- through two objects of one sort lands on one dedicated kind (`dedicatedFor_congr`), while
-- `vwcA`/`vwcB` above are held apart by the quantity *type*.
/-- The probe world's sort claim: every nominal object in this closed world is a soil
sample. `scoped`, because the library deliberately has no blanket `Sorted System`
instance — a test with a closed object population may make the claim for itself, opt-in. -/
scoped instance : Sorted System := ⟨fun _ => soilS⟩

theorem r19_one_catalogue_entry :
    vwc.dedicatedFor soilA water = vwc.dedicatedFor soilB water :=
  KindOfProperty.dedicatedFor_congr rfl water

/-- info: 'PropertyKindCalculus.Tests.KindStructure.r19_one_catalogue_entry' does not depend on any axioms -/
#guard_msgs in #print axioms r19_one_catalogue_entry

end PropertyKindCalculus.Tests.KindStructure

end -- pkc-blanket-expose
end -- pkc-blanket
