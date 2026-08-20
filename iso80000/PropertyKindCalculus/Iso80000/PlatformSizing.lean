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
  * **The time vocabulary — ISO 80000-3 item 3-9 (duration), plus two uncatalogued
    slopes.** `elapsedTime` specializes 3-9 (what a stopwatch reads around a deployment
    is a duration); the `w`/`a` slopes of the time model `t(N) = w·P/N + a·N` are
    modelling constructs with no catalogue item, dimension `T` because a count is
    dimension one. Time is the one dimension this vocabulary does *not* collapse —
    see the closing section.
  * **The counts — ISO 80000-9 item 9-1 (number of entities).** The five count kinds are
    deliberately NOT 9-1 itself (they are role-named: elements, cores, workers, shards);
    each *specializes* 9-1 through an explicit direct-parent edge, so any two are
    `MutuallyComparable` as counts (Flater's lattice, NIST TN 1943 §6.2) while remaining
    pairwise distinct kinds. Comparable-but-not-interchangeable is the entire design:
    the cores→shards bound in `decideShards` is licensed by comparability and still has
    to pass through the authored `coresAsShardCap` crossing.

The capstone is the sizing instance of `dim_not_injective`: all seven byte-and-count kinds
collapse to dimension one under `toDimension` while staying pairwise distinct — a
dimension-only type system (PhysLib alone, QUDT, F# units, Boost.Units) checks NOTHING in a
sizing formula, which is why the solver module carries kinds in the first place. The time
family is the counterpoint that sharpens the claim rather than weakening it: dimension does
separate seconds from bytes (the two currencies cannot be exchanged even dimensionally), and
that is *all* it separates — within the time family the functor conflates again, and the
swap that inverts the optimum (`w` for `a`) is invisible to it.
-/

import PropertyKindCalculus.Iso80000.Part3
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

/-! ## The time vocabulary — the one dimension the functor does not collapse

The time model `t(N) = w·P/N + a·N` brought three kinds, and they are the sizing
vocabulary's one family a dimension-only checker can tell apart from the seven above:
seconds against dimension one. That separation is real and worth stating — a byte slope
cannot be exchanged for a time slope even dimensionally. It is also *all* the separation
dimension offers here: within the family the functor conflates again, and the swap that
matters most — `w` for `a`, work-shared-out for overhead-multiplied-in — is exactly as
invisible to it as the worker/shard confusion is among the counts. -/

/-- Elapsed wall-clock time — dimension `T`, anchored at ISO 80000-3 item 3-9 (*duration*).
The platform kind is role-named (what a stopwatch reads around a deployment) and
*specializes* the catalogued kind rather than being it — the same relation the counts bear
to 9-1. -/
def elapsedTimeDK : DimensionedKind := { kind := Platform.elapsedTime, dim := Dim.time }

/-- The work rate `w` (seconds per batch element) — dimension `T`, a batch element being a
9-1 count of dimension one. A slope, not a duration of anything, so no catalogue item —
exactly as the byte slopes carry none. -/
def timePerElementDK : DimensionedKind := { kind := Platform.timePerElement, dim := Dim.time }

/-- The per-shard overhead `a` (seconds per shard) — dimension `T`, by the same argument. -/
def timePerShardDK : DimensionedKind := { kind := Platform.timePerShard, dim := Dim.time }

/-- The three time kinds carry exactly 3-9's dimension — the anchor agreement, as
`counts_dim_matches_9_1` is for 9-1. -/
theorem times_dim_matches_3_9 :
    elapsedTimeDK.toDimension = Part3.duration.toDimension ∧
    timePerElementDK.toDimension = Part3.duration.toDimension ∧
    timePerShardDK.toDimension = Part3.duration.toDimension :=
  ⟨rfl, rfl, rfl⟩

/-- The specialization edge: elapsed wall-clock time is a *duration* (3-9). The slopes are
deliberately not edged — a rate is not the duration of anything, and the catalogue has no
item for it. Open hierarchy, per Flater, like `CountEdge`. -/
inductive TimeEdge : KindOfProperty → KindOfProperty → Prop
  /-- What a stopwatch reads is a duration. -/
  | elapsed : TimeEdge Platform.elapsedTime Part3.duration.kind

/-- What the dimension functor DOES separate here — the two currencies. A time term and a
storage term cannot be exchanged even dimensionally, which is more than any pair of the
seven sizing kinds above can say. -/
theorem elapsed_storage_dimension_separated :
    elapsedTimeDK.toDimension ≠ storageCapacityDK.toDimension := by
  intro h
  have : (Dim.time).time = (Dim.one).time := congrArg Dimension.time h
  simp [Dim.time, Dim.one] at this

/-- And what it does not: within the time family the functor conflates again. `w` is
divided by the shard count and `a` multiplied by it, so the swap does not mis-scale the
optimum — it inverts which way the optimum moves — and both are dimension `T`. The kind
layer is still the only instrument, one dimension over. -/
theorem work_overhead_dimension_conflated :
    timePerElementDK.toDimension = timePerShardDK.toDimension ∧
    timePerElementDK.kind ≠ timePerShardDK.kind :=
  ⟨rfl, Platform.timePerElement_ne_timePerShard⟩

/-- A stopwatch reading is not a rate: same dimension, different kinds — the conflation
form, completing the family. -/
theorem elapsed_slope_dimension_conflated :
    elapsedTimeDK.toDimension = timePerElementDK.toDimension ∧
    elapsedTimeDK.kind ≠ timePerElementDK.kind :=
  ⟨rfl, Platform.elapsedTime_ne_timePerElement⟩

end PropertyKindCalculus.Iso80000.PlatformSizing
