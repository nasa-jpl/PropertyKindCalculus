/-
# The interaction algebra — Flater's full tracking of kinds (NIST TN 1943, App. C)

Dybkær's ontology gives the *kinds*; Flater (NIST Technical Note 1943, Appendix C)
adds the *calculus* on them: which kinds legitimately combine, and to what.
Dimensional analysis says torque and energy share a dimension (`M·L²·T⁻²`), yet
they are not the same kind and not interchangeable. The interaction algebra records
the **sanctioned** products as a *partial, curated, ternary* relation —
`torque × angle = energy` is in; `torque × angle = torque` and
`fuelConsumption × rainfall` are out — with the dimensional product demoted to a
*coherence side-condition* (R7) rather than the definition (R5).

This is the layer a description logic structurally cannot host: a partial relation
with an arithmetic side-condition and algebraic *laws* (multiplication and division
inverse; the dimensional homomorphism), proved rather than consistency-checked.
Role chains are binary, regular, and arithmetic-free.

It builds on the `Dimension` library (the forgetful functor
`dim = DimensionedKind.toDimension`), so it lives in the same PhysLib-backed source
tree (`dimension/`) and is built by `lake build Dimension`; the core spine stays
Mathlib-free.
-/
import PropertyKindCalculus.Dimension

open Dimension

namespace PropertyKindCalculus

/-! ## The curated interaction algebra (Flater App. C; R5, R7)

Combination of kinds is a *partial, ternary* relation, not a total binary
function: a pair of input kinds may sanction one output kind (torque × angle →
energy) or none at all (a category error). An application supplies its own
sanctioned products — the algebra is open-world and curated — and each declared
product must be *dimensionally coherent* (R7): forgetting to PhysLib's `Dimension`
must turn the kind product into the dimension product. Bundling the coherence
*obligation* with the relation is what guarantees, by construction, that no
sanctioned product can disagree with the dimension layer. -/

/-- A curated **interaction algebra** over dimensioned kinds (Flater App. C).
`KMul a b c` asserts the sanctioned product `a × b = c`. The relation is
deliberately *partial* (most triples are absent — a category error, not a number)
and *curated* (an application lists exactly the products it sanctions). The field
`kMul_coherent` is the dimensional-coherence obligation R7 imposes on every edge:
a sanctioned kind product must agree with the dimension layer, so the structure
cannot even be formed for an algebra that violates it. -/
structure InteractionAlgebra where
  /-- The sanctioned product edges: `KMul a b c` reads "`a` times `b` yields `c`". -/
  KMul : DimensionedKind → DimensionedKind → DimensionedKind → Prop
  /-- **R7 coherence obligation.** Every sanctioned product is dimensionally
  consistent — `dim` carries it to PhysLib's `Dimension` product. -/
  kMul_coherent : ∀ {a b c : DimensionedKind},
    KMul a b c → c.toDimension = a.toDimension * b.toDimension

namespace InteractionAlgebra

variable (A : InteractionAlgebra)

/-- The **kind quotient**, the division dual of the kind product: `KDiv c b a` reads
"`c` divided by `b` yields `a`", defined as the product read backwards. Partiality
is inherited — there is no quotient unless the matching product was sanctioned, so a
category error stays a category error on the division side too. -/
def KDiv (c b a : DimensionedKind) : Prop := A.KMul a b c

/-- **Multiplication and division are inverse (R5).** `KDiv` is by definition the
converse of `KMul`, so a product and its quotient hold together — the round-trip is
an equivalence, not merely an implication: `a × b = c` ⇔ `c / b = a`. -/
theorem kMul_iff_kDiv (a b c : DimensionedKind) :
    A.KMul a b c ↔ A.KDiv c b a := Iff.rfl

/-- **Dimensional coherence — `dim` is a homomorphism over the interaction algebra
(R7).** Whenever the algebra sanctions `a × b = c`, forgetting to the dimension
layer turns the kind product into PhysLib's `Dimension` product,
`dim c = dim a · dim b`. This is the theorem that licenses *forgetting* to the
dimension layer without losing soundness — and, read the other way, why matching
dimensions are necessary but never sufficient: the kind relation, not `dim`, decides
legality. -/
theorem dim_homomorphism {a b c : DimensionedKind} (h : A.KMul a b c) :
    c.toDimension = a.toDimension * b.toDimension := A.kMul_coherent h

end InteractionAlgebra

/-! ## Named dimensions for the worked algebra

The mechanical dimensions the worked example needs — `force` and `energy` — are the
shared definitions in `PropertyKindCalculus.Dimension` (`energy := force · length`).
Here the `Dim` namespace adds only `torque`, *independently* specified as
`force · length` — the same dimension (`M·L²·T⁻²`) reached two physical ways (work
along a displacement; a moment about a lever arm) — which is exactly why the dimension
layer cannot tell it apart from energy. -/

namespace Dim

/-- Torque / moment, `M·L²·T⁻²` — force about a lever arm: the *same dimension* as
`energy`, a *different* kind. -/
def torque : Dimension := force * length

/-- Torque and energy share a dimension — the dimension layer cannot separate them.
The interaction algebra is what keeps them distinct. -/
theorem torque_eq_energy : torque = energy := rfl

end Dim

/-! ## A worked interaction algebra (SI mechanics)

A concrete, coherent algebra over five mechanical kinds. Its two sanctioned
products — `force × length = energy` (work) and `torque × plane-angle = energy` —
are the smallest set that exhibits the point of the whole layer: `energy` and
`torque` are *distinct kinds with one dimension*, and the curated relation keeps
them apart where the dimension layer cannot. -/

/-- Force, a ratio kind of dimension `M·L·T⁻²`. -/
def forceKind : DimensionedKind :=
  { kind := { id := "force", scale := .ratio }, dim := Dim.force }

/-- Plane angle, a ratio kind of dimension one (Dybkær: a dimensionless quantity). -/
def angleKind : DimensionedKind :=
  { kind := { id := "plane angle", scale := .ratio }, dim := 1 }

/-- Energy / work, a ratio kind of dimension `M·L²·T⁻²`. -/
def energyKind : DimensionedKind :=
  { kind := { id := "energy", scale := .ratio }, dim := Dim.energy }

/-- Torque, a ratio kind of dimension `M·L²·T⁻²` — the *same dimension* as
`energyKind`, a *different* kind. -/
def torqueKind : DimensionedKind :=
  { kind := { id := "torque", scale := .ratio }, dim := Dim.torque }

namespace SIMech

/-- The sanctioned products of the worked SI-mechanics algebra. *Present:*
`force × length = energy` and `torque × plane-angle = energy`. *Absent* by
construction: `torque × plane-angle = torque` — a category error the matching
dimensions would otherwise wave through — and every product involving an unrelated
kind. -/
inductive KMul : DimensionedKind → DimensionedKind → DimensionedKind → Prop
  /-- Work: force along a displacement. -/
  | force_length_energy : KMul forceKind lengthKind energyKind
  /-- Torque turning through a plane angle delivers energy. -/
  | torque_angle_energy : KMul torqueKind angleKind energyKind

/-- Every sanctioned product is dimensionally coherent (R7) — discharged by the
`Dimension`-group computation, case by case. -/
theorem kMul_coherent {a b c : DimensionedKind} (h : KMul a b c) :
    c.toDimension = a.toDimension * b.toDimension := by
  cases h
  · rfl
  · exact (mul_one torqueKind.toDimension).symm

end SIMech

/-- The worked SI-mechanics algebra packaged as a coherent `InteractionAlgebra`: the
curated relation together with its discharged coherence obligation. An application
declares its own algebra exactly like this — by listing products and proving each
coheres. -/
def siMech : InteractionAlgebra where
  KMul := SIMech.KMul
  kMul_coherent := SIMech.kMul_coherent

/-- **Worked instance — torque × plane-angle = energy, and energy is not torque.**
The product is sanctioned, yet `energy ≠ torque` as kinds even though
`dim energy = dim torque`. This is the small example carrying exactly the
information dimensional analysis discards: the algebra distinguishes a moment from
the work it does. -/
theorem torque_angle_work :
    siMech.KMul torqueKind angleKind energyKind
      ∧ energyKind.kind ≠ torqueKind.kind
      ∧ energyKind.toDimension = torqueKind.toDimension :=
  ⟨SIMech.KMul.torque_angle_energy, by decide, rfl⟩

end PropertyKindCalculus
