/-
# CertifiedIngest — evidence at the boundary (invariant 6)

`Quantity k R` fixes how kinds *leave* the calculus (`.magnitude`), and the operator
table fixes how they *combine*. This module fixes how they **enter**: the ingress dual of
the erasure discipline. An anonymous mint `⟨x⟩ : Quantity k R` is an *unverified
assertion* that the bits `x` are a `k` — the argument-swap hole in constructor clothing.
Inside a fully-kinded architecture no compute definition re-mints (kinds flow by
construction); the mints that remain live at the *boundary*, where raw external data
becomes kinded. This module makes those boundary mints carry evidence, at three tiers
(strongest preferred):

  * **by construction** — the value is produced from already-kinded values through an
    authored crossing, so no check is needed (the incidence geometry from an angle, R_eff
    from the Fresnel core). Nothing here — the crossing *is* the evidence.
  * **checked at the gate** — a per-kind, per-carrier *admissibility predicate*
    (`KindAdmissible`) with a decidable executable face, discharged once by
    `Quantity.certify` into a `CertifiedQuantity`. For batched pixel data — which contains
    NaNs and out-of-range values by design — the check is not `∀ pixel, Holds` but
    *mask-mediated*: `Quantity.certifyBatch` emits a `{0,1}` validity mask alongside the
    quantity (`BatchAdmissible`), the same shape the QC/`w` vocabulary already uses.
  * **adjudicated** — a contract line or cited constant whose truth is external provenance
    (a citation, a documented channel convention). `IngestContract` is that declared,
    *emittable* (JSON) slot table: the residual role assertion lives on exactly one
    reviewable, diffable line, and the emitted document is what the upstream data producer
    signs, so both sides target the same contract.

**What this proves, and what it does not.** No predicate on bits makes "this array is soil
moisture" a theorem — a kind is *provenance*, not a bit pattern, so the checked tier is
necessary, not sufficient. What the paradigm guarantees is that the residual assertion is
*single-sited, named, checked where checkable, and emittable to the producer* — not that
it vanishes. Evidence is discharged at the gate and then *dropped*: downstream arithmetic
consumes a plain `Quantity`, because kinds thereafter flow by construction (threading
interval evidence through the kernels is interval analysis, a separate concern).

This module imports `Lean` for JSON emission (`IngestContract`), so — like `KindEdges` —
it is built by the package glob but kept out of the Mathlib-free, prelude-only
`import PropertyKindCalculus` spine; consumers `import PropertyKindCalculus.CertifiedIngest`
explicitly.
-/

module

public import PropertyKindCalculus.Bounds
public import Lean

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open Lean (ToJson FromJson Json toJson)

namespace PropertyKindCalculus

/-! ## The checked tier — `KindAdmissible` and `CertifiedQuantity` -/

/-- **The checkable face of a kind claim.** A per-kind, per-carrier admissibility
predicate: `Holds` is the specification ("what it means for these bits to be a legitimate
`k`"), `check` is its *executable* decision procedure, and `check_iff` ties them. Registered
as an instance next to the kind declaration (invariant 5, registry-style), so the sanctioned
admissibility of a kind is enumerable exactly as the operator table's edges are.

Necessary, not sufficient: a kind is provenance, and no predicate on bits can *finish* the
claim (range/finiteness/coherence is all that is machine-checkable at the gate). This is the
checked *tier (ii)*; the by-construction tier (i) needs no instance, and the adjudicated tier
(iii) is `IngestContract`. -/
class KindAdmissible (k : KindOfProperty) (R : Type) where
  /-- The admissibility specification on a raw carrier value. -/
  Holds : R → Prop
  /-- The executable decision procedure for `Holds`. -/
  check : R → Bool
  /-- `check` decides `Holds`. -/
  check_iff : ∀ r, check r = true ↔ Holds r

/-- Why a `Quantity.certify` rejected a value: the raw carrier bits failed the kind's
admissibility check. Carries the kind's identity for a legible gate-rejection record. -/
inductive CertError where
  /-- The value failed the admissibility predicate of the named kind. -/
  | inadmissible (kindId : String) : CertError
deriving Repr, DecidableEq, Inhabited

/-- **A quantity bundled with its discharged admissibility evidence** — `cert` is the gate's
receipt, kept in the type rather than asserted at the call site.

Produced *only* by a sanctioned constructor — `Quantity.certify` (checked) or
`CertifiedQuantity.byConstruction` (tier (i)) — so an anonymous `⟨…⟩` mint is, by contrast,
reviewable as a defect. `q` is the plain quantity that flows downstream once the receipt is
dropped. -/
structure CertifiedQuantity (k : KindOfProperty) (R : Type) [inst : KindAdmissible k R] where
  /-- The certified quantity. -/
  q : Quantity k R
  /-- The discharged evidence that `q`'s magnitude is admissible for `k`. -/
  cert : inst.Holds q.magnitude

/-- **The one checked mint.** Discharge the kind's admissibility check on a raw carrier
value; on success return the value bundled with its evidence, on failure a legible
`CertError`. This is the sanctioned boundary constructor for the checked tier — the
per-call `⟨x⟩` an audit flags is replaced by exactly one `certify` at the gate. -/
def Quantity.certify (k : KindOfProperty) (R : Type) [inst : KindAdmissible k R] (r : R) :
    Except CertError (CertifiedQuantity k R) :=
  if h : inst.check r = true then
    .ok ⟨⟨r⟩, (inst.check_iff r).mp h⟩
  else
    .error (.inadmissible k.id)

namespace CertifiedQuantity

variable {k : KindOfProperty} {R : Type} [inst : KindAdmissible k R]

/-- **The by-construction mint (tier (i)).** When a value is produced from already-kinded
inputs through an authored crossing, its admissibility is guaranteed by construction, not
re-checked; supply the guarantee once as a proof. The dual of `certify` for the strongest
evidence tier. -/
def byConstruction (q : Quantity k R) (h : inst.Holds q.magnitude) : CertifiedQuantity k R :=
  ⟨q, h⟩

/-- Drop the receipt: recover the plain quantity that flows downstream. -/
def toQuantity (c : CertifiedQuantity k R) : Quantity k R := c.q

/-- A certified value satisfies its kind's admissibility predicate — the receipt, as a fact. -/
theorem holds (c : CertifiedQuantity k R) : inst.Holds c.q.magnitude := c.cert

/-- A certified value's executable check is `true` — the receipt on the decidable face. -/
theorem check_true (c : CertifiedQuantity k R) : inst.check c.q.magnitude = true :=
  (inst.check_iff c.q.magnitude).mpr c.cert

end CertifiedQuantity

/-- **`certify` succeeds exactly on admissible values** — a value the gate accepts is one the
specification admits, and the recovered quantity carries the given magnitude. The soundness
of the checked tier, in one line. -/
theorem Quantity.certify_isOk_iff (k : KindOfProperty) (R : Type) [inst : KindAdmissible k R]
    (r : R) : (Quantity.certify k R r).toOption.isSome ↔ inst.Holds r := by
  rw [← inst.check_iff r]
  by_cases h : inst.check r = true <;>
    simp [Quantity.certify, h, Except.toOption]

/-! ## The batched tier — mask-mediated certification

Deployed pixel data contains NaNs and out-of-range values *by design* (fill pixels, water
bodies, retrieval failures), so a batched certificate cannot be `∀ pixel, Holds`. Instead
the gate emits, alongside the quantities, a `{0,1}` validity mask that the branch-free
kernels consume — exactly what `buildObsW`'s per-observation weight `w` and the QC layer
already do. `BatchAdmissible` is the batched face of `KindAdmissible`: a mask-producing
function in place of a `Bool`-valued check (a batched carrier has no decidable order, by
the branchless design law, so the scalar `check` is unavailable there). -/

/-- **The batched face of a kind claim.** In place of a scalar `check : R → Bool` (which a
branchless deployment carrier cannot provide), a mask producer: `mask r` is the `{0,1}`
validity indicator over the batch, `1` where the element is admissible for `k` and `0`
where it must be excluded. -/
class BatchAdmissible (k : KindOfProperty) (R : Type) where
  /-- The `{0,1}` per-element validity mask for `k`-admissibility over a batch. -/
  mask : R → R

/-- **A batched quantity paired with its validity mask** — the mask-mediated certificate.
The quantity flows into the branch-free kernels; the mask flows alongside (as `w`/QC does),
carrying the gate's evidence for the pixels that must be excluded. -/
structure MaskedCertificate (k : KindOfProperty) (R : Type) where
  /-- The batched quantity. -/
  q : Quantity k R
  /-- The `{0,1}` validity mask produced at the gate. -/
  valid : R

/-- **The batched mint.** Certify a batch by pairing it with the `{0,1}` validity mask its
kind's `BatchAdmissible` produces — the mask-mediated analogue of `Quantity.certify`, total
(no failure branch: invalid pixels are masked, not rejected). -/
def Quantity.certifyBatch (k : KindOfProperty) (R : Type) [BatchAdmissible k R] (r : R) :
    MaskedCertificate k R :=
  ⟨⟨r⟩, BatchAdmissible.mask (k := k) r⟩

/-! ## The adjudicated tier — the emittable `IngestContract` -/

/-- **One declared boundary slot.** The named external channel `name` carries a value of
kind `kindId` (a `KindOfProperty.id`), gated by `admissibility` (a note naming the
sanctioned admissibility predicate or the by-construction crossing) and documented by
`unitNote` (the unit/convention the producer must honour). The residual role assertion
"channel `name` *is* a `kindId`" lives here, on one line. -/
structure IngestSlot where
  /-- The external channel / slot name (the producer's key). -/
  name : String
  /-- The kind provenance claimed for the slot (a `KindOfProperty.id`). -/
  kindId : String
  /-- The evidence tier note: the sanctioned admissibility predicate, or the crossing that
  makes the value by-construction admissible. -/
  admissibility : String
  /-- The unit / convention the producer must honour (e.g. "mass fraction [0,1]"). -/
  unitNote : String := ""
deriving Repr, DecidableEq, BEq, Inhabited, ToJson, FromJson

/-- **The declared slot table for a named external interface** — the tier-(iii) adjudication
record. The npy/CLI marshalling is *generated from* this document (the deploy layer's
name-keyed slot marshalling, with the kind column and checks added), and the document is
*emittable* (JSON, `emitJson`) so the upstream producer signs the same table the code
enforces. -/
structure IngestContract where
  /-- The name of the external interface this contract governs. -/
  interface : String
  /-- The declared slots, in producer order. -/
  slots : List IngestSlot
deriving Repr, DecidableEq, BEq, Inhabited, ToJson, FromJson

namespace IngestContract

/-- **Build a slot from a kind**, so the `kindId` cannot drift from a real
`KindOfProperty` — a rename of the kind is a source edit here, not silent staleness. -/
def slot (k : KindOfProperty) (name admissibility : String) (unitNote : String := "") :
    IngestSlot :=
  { name := name, kindId := k.id, admissibility := admissibility, unitNote := unitNote }

/-- **Build a kindless slot** for a nominal channel (a flag word, an enumeration) whose
adjudication is that it carries *no* kind — a bitmask has no magnitude, and inventing a kind
for one is exactly what the role-named-kind invariant forbids — so the contract records the
absence explicitly instead of faking a kind id. -/
def nominalSlot (name admissibility : String) (unitNote : String := "") : IngestSlot :=
  { name := name, kindId := "(none: nominal channel)", admissibility := admissibility,
    unitNote := unitNote }

/-- The kinds claimed by the contract, in slot order (the provenance census a reviewer
reads against the producer's documentation). -/
def kindIds (c : IngestContract) : List String := c.slots.map (·.kindId)

/-- The slot names, in declared (producer) order — for a positionally packed interface this
*is* the channel order, so it is the census a positional reader pins its hardcoded channel
indices against. -/
def names (c : IngestContract) : List String := c.slots.map (·.name)

/-- The declared position of the named slot — its channel index, for a positionally packed
interface — if present. The consumer-side pin: `#guard c.idxOf? "clay" == some 6` ties a
hardcoded channel read to the declared table, so reordering either side fails the build. -/
def idxOf? (c : IngestContract) (name : String) : Option Nat :=
  c.slots.findIdx? (·.name == name)

/-- **Emit the contract as pretty-printed JSON** — the document the upstream data producer
signs. Both sides then target one artefact: the producer's output schema and the code's
ingest gate are the same table. -/
def emitJson (c : IngestContract) : String := (toJson c).pretty

end IngestContract

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
