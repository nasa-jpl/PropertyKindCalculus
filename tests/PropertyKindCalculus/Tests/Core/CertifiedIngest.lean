/-
# Validation probes — the certified ingest boundary (invariant 6)

`Quantity k R` records how kinds *leave* and *combine*; `CertifiedIngest` records how they
*enter* — with evidence, at three tiers. This probe exercises the checked tier
(`KindAdmissible` → `Quantity.certify` → `CertifiedQuantity`), the batched mask-mediated tier
(`BatchAdmissible` → `Quantity.certifyBatch`), and the adjudicated tier (`IngestContract` +
JSON emission), and pins the axiom profile of the soundness theorem.
-/

module

public import PropertyKindCalculus.CertifiedIngest
meta import PropertyKindCalculus.CertifiedIngest

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.CertifiedIngest

open PropertyKindCalculus

/-- A probe kind whose admissibility is a closed unit-interval range (the `massFraction`/
`reflectivity` shape). -/
def unitKind : KindOfProperty := { id := "certified-ingest probe unit-interval", scale := .ratio }

/-- The admissibility specification: a magnitude in `[0, 1]`. -/
def UnitHolds (x : Float) : Prop := 0.0 ≤ x ∧ x ≤ 1.0

/-- The checked-tier admissibility instance for `unitKind` at the `Float` carrier: the
executable `check` decides the `[0,1]` range. -/
instance instUnitKind : KindAdmissible unitKind Float where
  Holds := UnitHolds
  check x := decide (0.0 ≤ x) && decide (x ≤ 1.0)
  check_iff := by
    intro r; simp only [UnitHolds, Bool.and_eq_true, decide_eq_true_eq]

-- An admissible value certifies.
#guard (Quantity.certify unitKind Float 0.3).toOption.isSome
-- An out-of-range value is rejected.
#guard (Quantity.certify unitKind Float 1.5).toOption.isNone
-- The rejection carries a legible `CertError` naming the kind.
#guard (match Quantity.certify unitKind Float 1.5 with
        | .error e => e == .inadmissible unitKind.id | .ok _ => false)
-- The recovered quantity carries the certified magnitude.
#guard ((Quantity.certify unitKind Float 0.3).toOption.map (·.q.magnitude)) == some 0.3

/-- The by-construction mint (tier (i)): supply the guarantee (here obtained through the
executable face, since a raw `Float` inequality is not kernel-decidable). -/
def byCon : CertifiedQuantity unitKind Float :=
  CertifiedQuantity.byConstruction ⟨0.5⟩ ((instUnitKind.check_iff 0.5).mp (by native_decide))

#guard byCon.toQuantity.magnitude == 0.5

/-! ## Batched, mask-mediated (tier (ii) for pixel data) -/

/-- A toy batched carrier: a small array, with the `{0,1}` validity mask its `BatchAdmissible`
instance produces (here `1.0` where finite, `0.0` where not). -/
instance : BatchAdmissible unitKind (Array Float) where
  mask xs := xs.map (fun x => if x.isFinite then 1.0 else 0.0)

-- The batched mint pairs the batch with its validity mask.
#guard (Quantity.certifyBatch unitKind (Array Float) #[0.3, 0.0/0.0]).valid == #[1.0, 0.0]

/-! ## The adjudicated tier — the emittable contract -/

/-- A two-slot ingest contract: the clay channel (checked) and the incidence angle (by
construction). The residual role assertions live on these two lines. -/
def probeContract : IngestContract where
  interface := "probe-ancillary-npy"
  slots := [
    IngestContract.slot unitKind "MU_CLAY_FRC" "unit-interval range check" "mass fraction [0,1]",
    IngestContract.slot unitKind "INC_ANGLE" "by construction from the geometry" "degrees"]

-- The contract's provenance census, in slot order.
#guard probeContract.kindIds == [unitKind.id, unitKind.id]
-- The contract emits non-empty JSON — the document the producer signs.
#guard probeContract.emitJson.length > 0
-- The emitted JSON round-trips through the derived codec.
#guard (match (Lean.fromJson? (Lean.toJson probeContract) : Except String IngestContract) with
        | .ok c => c == probeContract | .error _ => false)

-- The JSON the producer signs.
#eval probeContract.emitJson

/-- info: 'PropertyKindCalculus.Quantity.certify_isOk_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Quantity.certify_isOk_iff

end PropertyKindCalculus.Tests.CertifiedIngest

end Blanket
