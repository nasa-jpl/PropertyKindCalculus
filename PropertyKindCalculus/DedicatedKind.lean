/-
# Dedicated kind-of-property

Dybkær, *An Ontology on Property for Physical, Chemical, and Biological Systems*
(2009), Chapter 20: *"Dedicated kind-of-property and systematic terms."*

  * **§20 dedicated kind-of-property** — "kind-of-property with given sort of
    system and any pertinent component."

A bare kind-of-property (Ch. 6) — say *volume fraction* — is generic. A
*dedicated* kind binds it to the **sort of system** it is about — the definition's
own "given sort of system" — and the pertinent **component**, giving the
fully-specified designation used in laboratory medicine: the IUPAC/IFCC "NPU"
syntax

    System(spec) — Component(spec) ; kind-of-property(spec)

e.g. *"Plasma — Glucose ; substance concentration"*, or, in this project's home
domain, *"Soil — Water ; volume fraction"* (volumetric water content). *Plasma*
and *soil* name sorts: the catalogue entry is one entry for every plasma sample
and every soil sample there will ever be. The **particular** system a measured
value characterizes is carried one layer down, as the object index of an
`IndividualQuantity` — dedication to the sort, individuation by the object — and
`dedicatedFor` below is the arrow from that layer to this one.

In four-category terms (Lowe, *The Four-Category Ontology*, 2005, Fig. 7.1) a dedicated
kind is the **top edge** of the ontological square: the substantial universal (the sort)
*characterized by* the attribute (the kind-of-property), refined by Dybkær's pertinent
component — a refinement the square itself does not carry. The diagonal — a substance
*exemplifying* an attribute — is derivative in Lowe, factoring through either path around
the square, and the calculus agrees structurally: there is no primitive object-to-kind
construct. His dispositional route (up the left edge, then across the top) is
`dedicatedFor` — `Sorted.sortOf`, then the catalogue; his occurrent route (across the
bottom, then up the right) is an inhabitant of `IndividualQuantity o k R`, which
characterizes the object and instantiates the kind.

This is the construct the QUDV → OML/OWL2 lineage cannot express. OWL2 can record
that a quantity *has* a sort of system and a component, but it cannot make
*"Soil — Water ; volume fraction"* and *"Soil — Water ; mass fraction"* provably
distinct kinds **while keeping both dedicated to the same sort and component**.
Here that distinctness is a theorem (`distinct_of_kind`) — the *principled* form
of the soil-moisture distinctness that the `Dimension` library currently states
via differing kind-identity strings: volumetric and gravimetric water content are
the *same measurement target* (soil — water), examined as two different
kinds-of-property, so the kinds differ because the *kinds-of-property* differ, not
because of any hand-chosen identity string.
-/

module

public import PropertyKindCalculus.Foundations
public import PropertyKindCalculus.Kind

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus

universe u

/-- **§20 component** — a pertinent component of the sort of system that a dedicated
kind-of-property is about (e.g. *water* in a *soil* sample, *glucose* in
*plasma*). Specified abstractly by identity, mirroring `SortOfSystem`. -/
structure Component where
  /-- Terminological identity of the component (mirrors the OML `id`). -/
  id : String
deriving DecidableEq, Repr

/-- **§20 dedicated kind-of-property** — "kind-of-property with given sort of
system and any pertinent component." Its three projections are the IUPAC/IFCC
`System — Component ; kind-of-property` triple, the `System` slot naming the
sort. -/
structure DedicatedKind where
  /-- The sort of system the dedicated kind is about — the definition's "given
  sort of system". The *particular* system is not stored here: it is the object
  index of the `IndividualQuantity` that instantiates this catalogue entry. -/
  sort : SortOfSystem
  /-- The pertinent component (§20). -/
  component : Component
  /-- The underlying generic kind-of-property (Ch. 6). -/
  kind : KindOfProperty
deriving DecidableEq, Repr

/-- Dedicate a generic kind-of-property to a sort of system and a pertinent
component. -/
def KindOfProperty.dedicatedTo (k : KindOfProperty) (sort : SortOfSystem)
    (component : Component) : DedicatedKind :=
  { sort := sort, component := component, kind := k }

/-- Dedicate a kind through an **object**: the object contributes exactly its sort.
This is the instantiation square closing — the individual layer carries the
particular, the dedicated kind its sort — and `Sorted` is the model's claim about
which sort that is. In square terms, Lowe's dispositional route to exemplification:
up the *instantiated by* edge, then across the top. -/
def KindOfProperty.dedicatedFor {O : Type u} [Sorted O] (k : KindOfProperty)
    (o : O) (component : Component) : DedicatedKind :=
  k.dedicatedTo (Sorted.sortOf o) component

/-- **Two objects of one sort dedicate to one kind.** The catalogue entry cannot
tell two rovers apart, and is not supposed to: individuation is the object
index's job, where combining quantities across the two is a type error. -/
theorem KindOfProperty.dedicatedFor_congr {O : Type u} [Sorted O]
    {k : KindOfProperty} {o₁ o₂ : O} (h : Sorted.sortOf o₁ = Sorted.sortOf o₂)
    (component : Component) :
    k.dedicatedFor o₁ component = k.dedicatedFor o₂ component :=
  congrArg (fun σ => k.dedicatedTo σ component) h

namespace DedicatedKind

/-- The systematic term `System — Component ; kind-of-property` (Ch. 20, in the
ENV 12264 / IUPAC-IFCC syntax), the `System` slot naming the sort. -/
def systematicTerm (d : DedicatedKind) : String :=
  s!"{d.sort.id} — {d.component.id} ; {d.kind.id}"

/-- **§13.3.1 via §20** — a dedicated kind is a *dedicated kind-of-quantity* iff
its underlying kind has magnitude. -/
def IsQuantity (d : DedicatedKind) : Prop := d.kind.IsQuantity

/-- Two dedicated kinds that **agree on sort and component** but differ in the
underlying kind-of-property are distinct.

This is the *principled* form of the soil-moisture distinctness. Volumetric and
gravimetric water content are the **same measurement target** — soil — water —
examined as two different kinds-of-property (*volume fraction* vs *mass
fraction*). They are distinct dedicated kinds **because the kinds-of-property
differ**, not because of any hand-chosen identity string. -/
theorem distinct_of_kind {d₁ d₂ : DedicatedKind} (h : d₁.kind ≠ d₂.kind) :
    d₁ ≠ d₂ := by
  intro he; apply h; rw [he]

/-- Dedicated kinds with the same sort and kind-of-property but a different
component are distinct (e.g. the water content vs. the air content of the same
sort of soil sample). -/
theorem distinct_of_component {d₁ d₂ : DedicatedKind}
    (h : d₁.component ≠ d₂.component) : d₁ ≠ d₂ := by
  intro he; apply h; rw [he]

/-- Dedicated kinds about different sorts of system are distinct (e.g. the water
content of a soil sample vs. that of a sediment core). -/
theorem distinct_of_sort {d₁ d₂ : DedicatedKind}
    (h : d₁.sort ≠ d₂.sort) : d₁ ≠ d₂ := by
  intro he; apply h; rw [he]

end DedicatedKind

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
