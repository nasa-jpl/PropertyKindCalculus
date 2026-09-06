/-
# The requirement catalogue — the 27 axes the calculus is specified against

The canonical identity of each blueprint requirement: its identifier (R1 … R27),
a one-line title, the group it belongs to, and its headline status. This is the
*spine* of the traceability matrix — the rows the harvested `@[requirement …]`
annotations are grouped under — so the matrix always shows every requirement, even
one not yet annotated (its row is simply empty of declarations).

Mirrors the discipline of `PropertyKindCalculus.CrossRefs.Sources` and
`Iso80000.References`: the catalogue records only the citable identity of each
requirement; the *design* text lives in the blueprint chapters.
-/

namespace PropertyKindCalculus.Requirements

/-- The groups the requirements fall into, matching the blueprint's
"Requirements" section headings. -/
inductive RequirementGroup where
  /-- R1–R3, R19, R22: how kinds are structured, and how quantities characterize objects
  and named parts of named systems. -/
  | kindStructure
  /-- R4–R6: how operations on kinds are gated. -/
  | operationGating
  /-- R7–R8, R16–R17: keeping the kind layer consistent with dimension and unit layers. -/
  | soundnessBridges
  /-- R9: how values aggregate over parts. -/
  | aggregation
  /-- R10–R11, R20: numeric representation, value representation, and frames/variance. -/
  | representation
  /-- R12–R13: verified classification and unit classification. -/
  | classification
  /-- R14–R15, R18: uncertainty propagation, numerical adequacy, and coverage. -/
  | uncertainty
  /-- R21, R25: what the kind layer costs the author — erasure to the bare carrier,
  and rendering back to mathematics. -/
  | ergonomics
  /-- R23–R27: provenance of values, the audit discipline over a scope, the checked
  measurement model on a boundary, and the licensed distribution of its computation. -/
  | evidence
  deriving Repr, Inhabited, DecidableEq, BEq

/-- The requirement groups in presentation order — the section order of the
traceability matrix. -/
def requirementGroups : List RequirementGroup :=
  [ .kindStructure, .operationGating, .soundnessBridges, .aggregation,
    .representation, .classification, .uncertainty, .ergonomics, .evidence ]

/-- What would *count* as discharging a requirement — an intrinsic property of the
requirement, not of the evidence. Two obligations of fundamentally different
character live in the catalogue:

  * a `verifiable` requirement is a truth-apt claim about the calculus, discharged
    by a **checked theorem** (a `proves` annotation) — "PKC *proves* it";
  * an `expressiveness` requirement is a capability the type system must afford,
    discharged by a **construction that typechecks** (an `exemplifies` annotation)
    — "PKC *demonstrates* it". There is no theorem to prove: that the witnessing
    declaration elaborates under CI *is* the demonstration.

This is a design decision about the *nature* of each requirement, so — unlike
`status`, which is derived from the annotations — it belongs in the catalogue as
citable identity. Recording it lets the matrix report each class in its own honest
vocabulary (`proved` vs `demonstrated`) and lets the headline claim quantify over
the right subset: *all verifiable requirements proved, all expressiveness
requirements demonstrated.* -/
inductive RequirementKind where
  /-- A truth-apt claim, discharged by a checked theorem (`proves`). -/
  | verifiable
  /-- A capability, discharged by a typechecking construction (`exemplifies`). -/
  | expressiveness
  deriving Repr, Inhabited, DecidableEq, BEq

/-- The kind as printed. -/
def RequirementKind.label : RequirementKind → String
  | .verifiable     => "verifiable"
  | .expressiveness => "expressiveness"

/-- The group as printed. -/
def RequirementGroup.label : RequirementGroup → String
  | .kindStructure    => "Kind structure"
  | .operationGating  => "Operation gating"
  | .soundnessBridges => "Soundness bridges"
  | .aggregation      => "Aggregation"
  | .representation   => "Representation parametricity"
  | .classification   => "Classification"
  | .uncertainty      => "Uncertainty and numerical adequacy"
  | .ergonomics       => "Ergonomics and erasure"
  | .evidence         => "Provenance and audit"

/-- The identity of one requirement: its identifier, one-line title, and group.

Note there is deliberately **no `status` field**: a requirement's status
(`proved` / `specified` / `unaddressed`) is *not* an assertion recorded here but a
fact *derived* from the `@[requirement …]` annotations — see
`Requirements.requirementStatus`. Anything a hand-typed status could claim, the
annotations already witness (or fail to), so recording it twice would only
reintroduce the drift this layer exists to eliminate. -/
structure Requirement where
  /-- The identifier, as printed — `"R1"` … `"R27"`. -/
  id : String
  /-- A one-line title. -/
  title : String
  /-- The group the requirement belongs to. -/
  group : RequirementGroup
  /-- Whether the requirement is `verifiable` (discharged by a theorem) or an
  `expressiveness` capability (discharged by a typechecking construction). Most
  requirements are verifiable; this defaults accordingly. -/
  kind : RequirementKind := .verifiable
  deriving Repr, Inhabited

/-- The numeric part of a requirement id (`"R12"` ↦ `12`), for natural sorting. -/
def Requirement.number (r : Requirement) : Nat :=
  (r.id.dropWhile (!·.isDigit)).toNat!

/-- The fixed set of requirements the calculus is specified to meet. The single
source of truth for the traceability matrix's rows. -/
def catalogue : List Requirement :=
  [ { id := "R1",  group := .kindStructure,
      title := "Kinds are first-class and discriminate within a dimension" }
  , { id := "R2",  group := .kindStructure,
      title := "Specialization is a lattice, with comparability but not identity" }
  , { id := "R3",  group := .kindStructure, kind := .expressiveness,
      title := "General versus individual is type versus term" }
  , { id := "R19", group := .kindStructure, kind := .expressiveness,
      title := "A quantity characterizes an object; object identity is carried in the type" }
  , { id := "R22", group := .kindStructure, kind := .verifiable,
      title := "A quantity is dedicated to a named component of a named system; dedications \
                of distinct systems are provably distinct, so a part-quantity of one system \
                cannot stand in for a part-quantity of another" }
  , { id := "R4",  group := .operationGating,
      title := "Operations are gated by kind (the additive law)" }
  , { id := "R5",  group := .operationGating,
      title := "The interaction algebra is a partial, typed, ternary product" }
  , { id := "R6",  group := .operationGating,
      title := "Operator availability is gated by scale, monotonically" }
  , { id := "R7",  group := .soundnessBridges,
      title := "Dimension certifies coherence; it does not decide legality" }
  , { id := "R8",  group := .soundnessBridges, kind := .expressiveness,
      title := "Units are chosen values of a kind" }
  , { id := "R16", group := .soundnessBridges, kind := .verifiable,
      title := "Unit references are faithful: commensurability is an equivalence and \
                the number-and-reference form round-trips" }
  , { id := "R17", group := .soundnessBridges, kind := .verifiable,
      title := "Unit conversion between commensurable units is a faithful round-trip \
                (an exact, reciprocal power-of-radix factor — SI decimal or IEC binary)" }
  , { id := "R9",  group := .aggregation,
      title := "Extensive quantities aggregate additively over parts; intensive ones do not" }
  , { id := "R10", group := .representation,
      title := "A quantity value is parametric in its numeric representation type" }
  , { id := "R11", group := .representation,
      title := "Units are scalar; a vector quantity is a numerical array times one scalar unit" }
  , { id := "R20", group := .representation, kind := .verifiable,
      title := "A vector quantity's numbers are coefficients in a chosen basis, so a reading \
                is indexed by that basis and by the law its coefficients obey when the basis \
                changes; readings in different bases do not combine, the change acts \
                functorially, and a contraction of two readings is basis-independent while \
                each coefficient separately is not" }
  , { id := "R12", group := .classification,
      title := "A classification is a certificate, not an assertion" }
  , { id := "R13", group := .classification,
      title := "Unit classification needs a third category: scale-spanning units" }
  , { id := "R14", group := .uncertainty,
      title := "Output uncertainty is computed by a provably nested ladder of methods" }
  , { id := "R15", group := .uncertainty,
      title := "A floating-point representation is numerically adequate iff it loses no \
                information at the scale of the input uncertainties" }
  , { id := "R18", group := .uncertainty, kind := .verifiable,
      title := "The recorded variance certifies a coverage interval: distribution-free \
                (Chebyshev ≥ 1 − 1/k²), exact for bounded families" }
  , { id := "R21", group := .ergonomics, kind := .verifiable,
      title := "The kind layer erases: the kinded authoring computes exactly the bare-carrier \
                value, and the operator-table form elaborates to the same term as the \
                longhand form — the ceremony is pure" }
  , { id := "R25", group := .ergonomics, kind := .expressiveness,
      title := "A kinded definition renders back as typeset mathematics from its own \
                elaborated source, with the kind bookkeeping suppressed" }
  , { id := "R23", group := .evidence, kind := .expressiveness,
      title := "A value's provenance is recordable and auditable: a kind-typed value-flow \
                graph with a declared boundary contract, checked against what the scope \
                actually computes" }
  , { id := "R24", group := .evidence, kind := .expressiveness,
      title := "An audit is a claim about its scope, never about the library: the unkinded \
                surface of a scope is enumerable, and a blessed scope only grows" }
  , { id := "R26", group := .evidence, kind := .expressiveness,
      title := "A module's behavior is a checked measurement model: a declared boundary \
                carries relation edges whose witnesses are kernel-checked theorems, every \
                relation kind has a conclusion-shape check, a bound names a kinded \
                tolerance, and every rung beyond the witness's own is answered for by a \
                named repair or restatement" }
  , { id := "R27", group := .evidence, kind := .verifiable,
      title := "A module's distribution is licensed by declared extensivity: output ports \
                carry aggregation classes, and recarving or sharding a batch axis is \
                licensed by theorem from those declarations, with the quasi-extensive \
                tolerance tied to the rounding budget where the carrier demands it" } ]

/-- Look up a requirement by id. -/
def requirementById? (id : String) : Option Requirement :=
  catalogue.find? (·.id == id)

end PropertyKindCalculus.Requirements
