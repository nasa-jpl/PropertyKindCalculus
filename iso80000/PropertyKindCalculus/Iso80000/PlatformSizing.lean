/-
# The `Paradigm.Platform` sizing kinds, anchored in the ISO/IEC 80000 catalogue

The non-deployed annex to `PropertyKindCalculus.Paradigm.PlatformKinds`: the deployed
path carries the bare `KindOfProperty` vocabulary (Mathlib-free core); THIS module
attaches the `DimensionedKind` witnesses and the catalogue anchors, so no executable
gains a PhysLib/Mathlib dependency by sizing itself.

Anchors:

  * **Storage capacity — IEC 80000-13 item 13-9.** The identification is *definitional*
    (`platform_storage_is_13_9` is `rfl`): the Platform vocabulary's byte kind IS the
    catalogued kind, so everything Part 13 proves about it — dimension one, unit bit,
    incommensurable with the shannon of information content — transfers verbatim.
  * **The counts — ISO 80000-9 item 9-1 (number of entities).** The five count kinds are
    deliberately NOT 9-1 itself (they are role-named: elements, cores, workers, shards);
    each *specializes* 9-1 through an explicit direct-parent edge, so any two are
    `MutuallyComparable` as counts (Flater's lattice, NIST TN 1943 §6.2) while remaining
    pairwise distinct kinds. Comparable-but-not-interchangeable is the entire design:
    the cores→shards bound in `decideShards` is licensed by comparability and still has
    to pass through the authored `coresAsShardCap` crossing.

The capstone is the sizing instance of `dim_not_injective`: all seven kinds collapse to
dimension one under `toDimension` while staying pairwise distinct — a dimension-only
type system (PhysLib alone, QUDT, F# units, Boost.Units) checks NOTHING in a sizing
formula, which is why the solver module carries kinds in the first place.
-/

import PropertyKindCalculus.Iso80000.Part9
import PropertyKindCalculus.Iso80000.Part13
import PropertyKindCalculus.Paradigm.PlatformKinds

namespace PropertyKindCalculus.Iso80000.PlatformSizing

open PropertyKindCalculus
open PropertyKindCalculus.Paradigm

/-! ## The 13-9 identification (definitional) -/

/-- The Platform byte kind IS the catalogued *storage capacity* kind (13-9) — same
identity, same ratio scale, by construction. Part 13's incommensurability results
(storage capacity vs. the shannon) therefore hold of the deployed kind verbatim. -/
theorem platform_storage_is_13_9 :
    Platform.storageCapacity = Part13.storageCapacity.kind := rfl

/-! ## The dimensioned witnesses — all dimension one -/

/-- 13-9, as deployed (bytes are the 8-bit unit choice; the kind is the same). -/
def storageCapacityDK : DimensionedKind := { kind := Platform.storageCapacity, dim := Dim.one }
/-- The affine slope: storage per batch element — dimension one (bytes/element). -/
def storagePerElementDK : DimensionedKind := { kind := Platform.storagePerElement, dim := Dim.one }
/-- Batch element count — dimension one (a 9-1 specialization). -/
def elementCountDK : DimensionedKind := { kind := Platform.elementCount, dim := Dim.one }
/-- Schedulable core count — dimension one (a 9-1 specialization). -/
def coreCountDK : DimensionedKind := { kind := Platform.coreCount, dim := Dim.one }
/-- Concurrent worker count — dimension one (a 9-1 specialization). -/
def workerCountDK : DimensionedKind := { kind := Platform.workerCount, dim := Dim.one }
/-- Resident-split shard count — dimension one (a 9-1 specialization). -/
def shardCountDK : DimensionedKind := { kind := Platform.shardCount, dim := Dim.one }
/-- Per-shard slice element count — dimension one (a 9-1 specialization). The quotient of two
kinds that are both dimension one is dimension one too, which is exactly why the slice needs a
kind: nothing about its dimension distinguishes it from the total it was divided out of. -/
def sliceElementCountDK : DimensionedKind :=
  { kind := Platform.sliceElementCount, dim := Dim.one }

/-- Every count kind carries exactly 9-1's dimension (one) — the anchor agreement. -/
theorem counts_dim_matches_9_1 :
    elementCountDK.toDimension = Part9.numberOfEntities.toDimension ∧
    coreCountDK.toDimension = Part9.numberOfEntities.toDimension ∧
    workerCountDK.toDimension = Part9.numberOfEntities.toDimension ∧
    shardCountDK.toDimension = Part9.numberOfEntities.toDimension ∧
    sliceElementCountDK.toDimension = Part9.numberOfEntities.toDimension :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The 9-1 specialization lattice -/

/-- The direct-parent edge relation: each Platform count kind specializes *number of
entities* (9-1). This is the application-supplied `E` of `Specializes` — the hierarchy
is open, per Flater. -/
inductive CountEdge : KindOfProperty → KindOfProperty → Prop
  | element : CountEdge Platform.elementCount Part9.numberOfEntities.kind
  | core    : CountEdge Platform.coreCount    Part9.numberOfEntities.kind
  | worker  : CountEdge Platform.workerCount  Part9.numberOfEntities.kind
  | shard   : CountEdge Platform.shardCount   Part9.numberOfEntities.kind
  | slice   : CountEdge Platform.sliceElementCount Part9.numberOfEntities.kind

/-- Workers and shards are mutually comparable *as counts* (common super-kind 9-1) —
which is what licenses a cross-count bound like `min(cores, shards)` conceptually —
while `Platform.workerCount_ne_shardCount` keeps them distinct kinds, so the bound
still must pass through an authored crossing. Comparable, not interchangeable. -/
theorem workers_shards_comparable_as_counts :
    MutuallyComparable CountEdge Platform.workerCount Platform.shardCount :=
  ⟨Part9.numberOfEntities.kind, .of_edge .worker, .of_edge .shard⟩

/-- Likewise cores vs. shards — the pair `decideShards` actually bounds. -/
theorem cores_shards_comparable_as_counts :
    MutuallyComparable CountEdge Platform.coreCount Platform.shardCount :=
  ⟨Part9.numberOfEntities.kind, .of_edge .core, .of_edge .shard⟩

/-! ## The capstone — `dim_not_injective` at the sizing layer -/

/-- All seven sizing kinds are pairwise distinct … -/
theorem platform_kinds_pairwise_distinct :
    ([Platform.storageCapacity, Platform.storagePerElement, Platform.elementCount,
      Platform.coreCount, Platform.workerCount, Platform.shardCount,
      Platform.sliceElementCount]
      : List KindOfProperty).Pairwise (· ≠ ·) := by decide

/-- … and the dimension functor collapses every one of them to `1`: the sizing instance
of `dim_not_injective`. A dimension-only checker accepts every mis-wiring the kind layer
rejects — including the worker/shard confusion that authorizes ~N× the safe residency. -/
theorem platform_dims_conflated :
    [storageCapacityDK, storagePerElementDK, elementCountDK,
     coreCountDK, workerCountDK, shardCountDK, sliceElementCountDK].map
       DimensionedKind.toDimension
      = List.replicate 7 Dim.one := rfl

/-- The piecewise solver's pair, in the same form: a slice and the total it came from are the
same dimension and must not be the same kind, or a regime threshold would be tested against the
whole tile and every run would claim the cheaper side of the knee. -/
theorem total_slice_dimension_conflated :
    elementCountDK.toDimension = sliceElementCountDK.toDimension ∧
    elementCountDK.kind ≠ sliceElementCountDK.kind :=
  ⟨rfl, Platform.elementCount_ne_sliceElementCount⟩

/-- The emblematic pair, stated in the canonical conflation form: same dimension,
different kinds. -/
theorem workers_shards_dimension_conflated :
    workerCountDK.toDimension = shardCountDK.toDimension ∧
    workerCountDK.kind ≠ shardCountDK.kind :=
  ⟨rfl, Platform.workerCount_ne_shardCount⟩

end PropertyKindCalculus.Iso80000.PlatformSizing
