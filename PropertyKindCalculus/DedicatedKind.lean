/-
# Dedicated kind-of-property

Dybkær, *An Ontology on Property for Physical, Chemical, and Biological Systems*
(2009), Chapter 20: *"Dedicated kind-of-property and systematic terms."*

  * **§20 dedicated kind-of-property** — "kind-of-property with given sort of
    system and any pertinent component."

A bare kind-of-property (Ch. 6) — say *volume fraction* — is generic. A
*dedicated* kind binds it to the **system** it characterizes (Ch. 3) and the
pertinent **component**, giving the fully-specified designation used in
laboratory medicine: the IUPAC/IFCC "NPU" syntax

    System(spec) — Component(spec) ; kind-of-property(spec)

e.g. *"Plasma — Glucose ; substance concentration"*, or, in this project's home
domain, *"Soil — Water ; volume fraction"* (volumetric water content).

This is the construct the QUDV → OML/OWL2 lineage cannot express. OWL2 can record
that a quantity *has* a system and a component, but it cannot make
*"Soil — Water ; volume fraction"* and *"Soil — Water ; mass fraction"* provably
distinct kinds **while keeping both dedicated to the same system and component**.
Here that distinctness is a theorem (`distinct_of_kind`) — the *principled* form
of the soil-moisture distinctness that the `Dimension` library currently states
via differing kind-identity strings: volumetric and gravimetric water content are
the *same measurement target* (soil — water), examined as two different
kinds-of-property, so the kinds differ because the *kinds-of-property* differ, not
because of any hand-chosen identity string.
-/

import PropertyKindCalculus.Foundations
import PropertyKindCalculus.Kind

namespace PropertyKindCalculus

/-- **§20 component** — a pertinent component of the system that a dedicated
kind-of-property is about (e.g. *water* in a *soil* sample, *glucose* in
*plasma*). Specified abstractly by identity, mirroring `System`. -/
structure Component where
  /-- Terminological identity of the component (mirrors the OML `id`). -/
  id : String
deriving DecidableEq, Repr

/-- **§20 dedicated kind-of-property** — "kind-of-property with given sort of
system and any pertinent component." Its three projections are the IUPAC/IFCC
`System — Component ; kind-of-property` triple. -/
structure DedicatedKind where
  /-- The system the dedicated kind characterizes (Ch. 3). -/
  system : System
  /-- The pertinent component (§20). -/
  component : Component
  /-- The underlying generic kind-of-property (Ch. 6). -/
  kind : KindOfProperty
deriving DecidableEq, Repr

/-- Dedicate a generic kind-of-property to a system and a pertinent component. -/
def KindOfProperty.dedicatedTo (k : KindOfProperty) (system : System)
    (component : Component) : DedicatedKind :=
  { system := system, component := component, kind := k }

namespace DedicatedKind

/-- The systematic term `System — Component ; kind-of-property` (Ch. 20, in the
ENV 12264 / IUPAC-IFCC syntax). -/
def systematicTerm (d : DedicatedKind) : String :=
  s!"{d.system.id} — {d.component.id} ; {d.kind.id}"

/-- **§13.3.1 via §20** — a dedicated kind is a *dedicated kind-of-quantity* iff
its underlying kind has magnitude. -/
def IsQuantity (d : DedicatedKind) : Prop := d.kind.IsQuantity

/-- Two dedicated kinds that **agree on system and component** but differ in the
underlying kind-of-property are distinct.

This is the *principled* form of the soil-moisture distinctness. Volumetric and
gravimetric water content are the **same measurement target** — soil — water —
examined as two different kinds-of-property (*volume fraction* vs *mass
fraction*). They are distinct dedicated kinds **because the kinds-of-property
differ**, not because of any hand-chosen identity string. -/
theorem distinct_of_kind {d₁ d₂ : DedicatedKind} (h : d₁.kind ≠ d₂.kind) :
    d₁ ≠ d₂ := by
  intro he; apply h; rw [he]

/-- Dedicated kinds with the same system and kind-of-property but a different
component are distinct (e.g. the water content vs. the air content of the same
soil sample). -/
theorem distinct_of_component {d₁ d₂ : DedicatedKind}
    (h : d₁.component ≠ d₂.component) : d₁ ≠ d₂ := by
  intro he; apply h; rw [he]

/-- Dedicated kinds about different systems are distinct. -/
theorem distinct_of_system {d₁ d₂ : DedicatedKind}
    (h : d₁.system ≠ d₂.system) : d₁ ≠ d₂ := by
  intro he; apply h; rw [he]

end DedicatedKind

end PropertyKindCalculus
