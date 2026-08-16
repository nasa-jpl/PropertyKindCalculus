/-
`paradigm.platform_kinds` — **the kind vocabulary of the memory-bounded parallelism
solvers** (`Torch.Paradigm.Platform`): every quantity those solvers touch, as a
role-named `KindOfProperty`, plus the product/quotient laws that license the solver
arithmetic. Mathlib-free core (pure data): the deployed path carries these bare kinds;
the `DimensionedKind` witnesses and the ISO/IEC 80000 anchors (IEC 80000-13 item 13-9
*storage capacity*, ISO 80000-9 item 9-1 *number of entities*) are attached in the
non-deployed annex `PropertyKindCalculus.Iso80000.PlatformSizing`.

WHY KINDS HERE AT ALL. Every quantity in the sizing formulas is *dimension one* —
bytes, elements, cores, workers, shards, bytes-per-element — so a dimension-only type
system collapses all of them (`dim_not_injective`) and no check is available exactly
where a confusion is most expensive: a worker count read as a shard count authorizes
`workers × total` resident bytes where `1 × total` was safe. The kind layer is the
instrument that survives the collapse, so the solvers' own module must not be the one
place in the calculus written below its own discipline.

ONE STORAGE KIND, MANY INDIVIDUALS. The byte-valued quantities (a cgroup budget, a
per-worker fixed overhead, a caller's reserved holdings, a headroom) are deliberately
**one** kind: they are mutually comparable in Dybkær's sense — the solvers subtract and
compare them against each other, which is precisely what "quantities of the same kind"
licenses. Budget vs. overhead is a *role* distinction between individuals, carried by
field and parameter names (and, where it must be machine-checked, by `DedicatedKind`),
not a kind distinction. The counts, by contrast, are **four distinct kinds**: a core, a
worker, a shard, and a batch element are counted by incompatible residency/concurrency
semantics, no solver ever adds one to another, and swapping two of them is the silent
~N× residency error this module exists to make a type error.

THE SAME-SIGNATURE PAIR. `workersOfHeadroom` and `shardsOfHeadroom` have *identical*
quotient signatures — storage capacity over storage capacity — but deliberately
**distinct** result kinds: dividing a headroom by a per-worker footprint counts
*workers* (each worker adds its own resident block), dividing it by a per-shard fixed
overhead counts *shards* (the shards partition ONE resident total). Which count you
obtain is decided by which *law* you invoke, written in full at the call site — the
kind-calculus answer to "identical quotient signatures, deliberately distinct kinds",
usable as the template wherever two same-signature ratios must not interchange.
-/

import PropertyKindCalculus.Kind
import PropertyKindCalculus.Quantity
import PropertyKindCalculus.QuantityClassification
import PropertyKindCalculus.NominalValue

namespace PropertyKindCalculus.Paradigm.Platform

open PropertyKindCalculus

/-! ### The kinds -/

/-- Storage capacity, counted in bytes (anchor: IEC 80000-13 item 13-9, dimension one —
the annex attaches the witness). ONE kind for every byte-valued individual of the sizing
problem — budgets, fixed overheads, reserved holdings, headrooms, per-worker footprints —
because the solvers subtract and compare these against each other, the defining mark of
quantities of the same kind. -/
def storageCapacity : KindOfProperty :=
  { id := "storage capacity", scale := .ratio }

/-- The affine slope of an algorithm's memory model: marginal storage per batch element
(bytes/element). NOT a storage capacity — it never enters a budget comparison and is
consumed only through the product/quotient laws below. -/
def storagePerElement : KindOfProperty :=
  { id := "storage per batch element", scale := .ratio }

/-- Count of batch elements (the pixels of a tile, the rows of a block — whatever the
`BatchCarrier` batches over). Downstream applications refine this by `Specializes`
edges (a tile-pixel count *is an* element count); they do not re-use it raw. -/
def elementCount : KindOfProperty :=
  { id := "batch element count", scale := .ratio }

/-- Count of CPU cores the scheduler will actually grant (affinity ∧ quota). -/
def coreCount : KindOfProperty :=
  { id := "schedulable core count", scale := .ratio }

/-- Count of concurrently resident *workers*, each holding its OWN block of
`bytesFor(elemsPerWorker)` bytes (the `chunk_fit` driver shape): total residency scales
with this count. -/
def workerCount : KindOfProperty :=
  { id := "concurrent worker count", scale := .ratio }

/-- Count of *shards* partitioning ONE resident total (`runSharded`): the variable term
is invariant in this count and only the per-shard fixed overhead scales with it.
Deliberately distinct from `workerCount` — confusing the two silently authorizes
~count× the safe residency. -/
def shardCount : KindOfProperty :=
  { id := "resident-split shard count", scale := .ratio }

/-! ### The nominal text kinds — the parsers' input/output vocabulary

The capacity parsers all consume and produce `String`s, and two different texts in one
signature is the same argument-swap hole the quantity kinds close — a `/proc/meminfo`
dump and the field key to look up in it both type-check in either slot. So the TEXTS are
kinded too, as `NominalValue`s of nominal-scale kinds (§13.2.1: strings are properties
compared for equality, not quantities — `Quantity` would be the wrong wrapper, by
`nominal_not_quantity`). Each parser kind is one kernel-interface format, and the parser
for that format is the authority on it; the two label kinds at the end run the other
direction — designations the solvers *produce*, one per slot of the decision line they
emit. -/

/-- A kernel CPU-list (`"0-3,8,10-11"`) — the `Cpus_allowed_list` payload format. -/
def cpuListText : KindOfProperty := { id := "kernel CPU-list text", scale := .nominal }
/-- `/proc/self/status` content. -/
def procStatusText : KindOfProperty := { id := "/proc/self/status text", scale := .nominal }
/-- A cgroup memory-limit file's content (`memory.max` / `memory.limit_in_bytes`). -/
def memLimitText : KindOfProperty := { id := "cgroup memory-limit text", scale := .nominal }
/-- cgroup v2 `cpu.max` content (`"<quota> <period>"`). -/
def cpuMaxText : KindOfProperty := { id := "cgroup cpu.max text", scale := .nominal }
/-- `/proc/meminfo` content. -/
def meminfoText : KindOfProperty := { id := "/proc/meminfo text", scale := .nominal }
/-- A `/proc/meminfo` field key (`"MemAvailable"`) — NOT the dump it indexes into. -/
def meminfoFieldKey : KindOfProperty := { id := "/proc/meminfo field key", scale := .nominal }
/-- `/proc/self/cgroup` content. -/
def procCgroupText : KindOfProperty := { id := "/proc/self/cgroup text", scale := .nominal }
/-- A cgroup-v2 relative path (`"/kubepods/…"`) — the *extracted* half of
`parseCgroupV2Path`, a different kind of text than the dump it came from. -/
def cgroupPathText : KindOfProperty := { id := "cgroup-v2 relative path", scale := .nominal }
/-- A cgroup memory-*usage* file's content (`memory.current`, `memory.peak`,
`memory.max_usage_in_bytes`) — a bare byte count. A different kind from `memLimitText`
even though both are byte-valued text, because they do not admit the same values: a limit
may read `"max"` and a usage never does, so the limit parser's unlimited-sentinel handling
is wrong for a usage and would silently turn a real reading into `none`. -/
def memUsageText : KindOfProperty := { id := "cgroup memory-usage text", scale := .nominal }
/-- cgroup v2 `memory.events` content — `"low N\nhigh N\nmax N\noom N\noom_kill N"`. -/
def memEventsText : KindOfProperty := { id := "cgroup memory.events text", scale := .nominal }
/-- A `memory.events` field key (`"oom"`, `"oom_kill"`) — NOT the dump it indexes into,
the same distinction `meminfoFieldKey` draws against `meminfoText`. -/
def memEventsFieldKey : KindOfProperty :=
  { id := "cgroup memory.events field key", scale := .nominal }

/-- Count of memory-pressure events a cgroup level has recorded (`oom`, `oom_kill`). A
count, and deliberately NOT any of the four concurrency counts: nothing divides a headroom
by it and no solver adds it to a core, worker, shard or element. It is evidence *about* a
level rather than a term of the sizing arithmetic, which is exactly why it wants its own
kind — a level that has been killing things is a fact a reader must not be able to
arithmetic into a capacity. -/
def oomEventCount : KindOfProperty :=
  { id := "cgroup OOM event count", scale := .ratio }

/-- A capacity-source provenance label (`"cgroup-v2:<dir>"`, `"meminfo:MemAvailable"`,
`"cudaMemGetInfo:free"`) — what a `MemBudget` answers "believed from where" with. -/
def capacityProvenance : KindOfProperty :=
  { id := "capacity-source provenance label", scale := .nominal }

/-- The component a sizing decision is attributed to — the `[…]` prefix of the decision
line, and the twin of `capacityProvenance` on that same line: the provenance answers
"believed from where", the emitter "decided by whom". Deliberately GENERIC: an
application designates itself in its own vocabulary (an executable name, a stage id, a
DPS algorithm name — which are themselves distinct kinds, and confusable, in a
deployment that carries all three) and crosses into this kind through an authored
crossing at the call site, exactly as the count kinds do. Kinding it is what stops a log
line from being the one place in the decision where an unattributed `String` decides what
the reader believes about which program spoke. -/
def decisionEmitter : KindOfProperty :=
  { id := "sizing-decision emitter label", scale := .nominal }

/-- The swap that motivated the text kinds: the dump and the key that indexes it are
different kinds, so `parseMemInfoBytes key meminfo` is a compile error. -/
theorem meminfoText_ne_meminfoFieldKey : meminfoText ≠ meminfoFieldKey := by decide

/-- The same swap, one file down: `memory.events` and a key into it. -/
theorem memEventsText_ne_memEventsFieldKey : memEventsText ≠ memEventsFieldKey := by decide

/-- A cgroup limit and a cgroup usage are different kinds of text. This is the one that
would otherwise read plausibly: both files sit in the same directory and both hold bytes,
and feeding a `memory.current` to the limit parser costs nothing visible until a level
whose usage happens to exceed the v1 no-limit sentinel reports "no limit". -/
theorem memLimitText_ne_memUsageText : memLimitText ≠ memUsageText := by decide

/-- An OOM-event count is not a capacity: the census reports both per level, and the one
thing a reader must never do is arithmetic across them. -/
theorem oomEventCount_ne_storageCapacity : oomEventCount ≠ storageCapacity := by decide

/-- Input and output of `parseCgroupV2Path` are different kinds of text: feeding the
extracted path back to the extractor is a compile error. -/
theorem procCgroupText_ne_cgroupPathText : procCgroupText ≠ cgroupPathText := by decide

/-- The two labels of one decision line are different kinds — "decided by whom" is not
"believed from where" — so neither can be printed into the other's slot. -/
theorem decisionEmitter_ne_capacityProvenance : decisionEmitter ≠ capacityProvenance := by
  decide

/-! ### The display erasure of a storage capacity

Kinds erase at the log line (`Platform`'s module header names that as one of the two
sanctioned boundaries), but the *spelling* of the erasure should not be re-invented
per consumer: three repos printing `x / (1 <<< 20)` inline is three chances to divide by
the wrong power and no way to change the unit once. -/

/-- Render a storage capacity in **mebibytes** (IEC 80000-13 binary prefix `Mi` = 2²⁰),
the unit every budget line in and around these solvers reports.

Deliberately `String`-valued and one-way. Returning a rounded `Quantity` would put a
display figure back in reach of arithmetic that must run on the exact byte count — and a
budget comparison off by up to a mebibyte is precisely the class of error the solvers are
here to remove. -/
def showMiB (q : Quantity storageCapacity Nat) : String :=
  s!"{q.magnitude / (1 <<< 20)} MiB"

/-! ### The kind laws the solvers invoke -/

/-- `storagePerElement × elementCount = storageCapacity` — the variable term of the
affine memory model (`MemShape.bytesFor`). -/
theorem bytesOfElements : ProductKind storagePerElement elementCount storageCapacity :=
  ProductKind.ofRatio storagePerElement elementCount storageCapacity

/-- `storageCapacity / storagePerElement = elementCount` — the single-launch solver
(`MemShape.maxElems`): how many elements a budget sustains. -/
theorem elementsOfBudget : QuotientKind storageCapacity storagePerElement elementCount :=
  QuotientKind.ofRatio storageCapacity storagePerElement elementCount

/-- `storageCapacity / storageCapacity = workerCount` — the worker solver
(`maxConcurrentWorkers`): a headroom over a per-WORKER footprint counts workers, each
adding its own resident block. Same signature as `shardsOfHeadroom`, deliberately
different result kind — see the module header. -/
theorem workersOfHeadroom : QuotientKind storageCapacity storageCapacity workerCount :=
  QuotientKind.ofRatio storageCapacity storageCapacity workerCount

/-- `storageCapacity / storageCapacity = shardCount` — the split solver
(`maxShardsSplit`): a headroom (net of the ONE resident variable term) over a per-SHARD
fixed overhead counts shards. Same signature as `workersOfHeadroom`, deliberately
different result kind — see the module header. -/
theorem shardsOfHeadroom : QuotientKind storageCapacity storageCapacity shardCount :=
  QuotientKind.ofRatio storageCapacity storageCapacity shardCount

/-! ### The authored crossings

The one place counts of different kinds meet is the final `min` of `decideShards`:
a cores-implied cap and an elements-implied cap each bound the shard count. Those are
*claims* (one shard occupies one core; a shard needs at least one element), so each is
an authored, named crossing carrying its license in its docstring — the "by
construction" tier of `CertifiedIngest` — rather than an anonymous re-mint at the
call site. -/

/-- The cores-implied cap on concurrent shards. License: one shard runs on (at least)
one dedicated core, so no more shards than cores are usefully concurrent. -/
def coresAsShardCap (c : Quantity coreCount Nat) : Quantity shardCount Nat :=
  ⟨c.magnitude⟩

/-- The elements-implied cap on concurrent shards. License: a shard processes at least
one element, so no more shards than elements are useful. -/
def elementsAsShardCap (n : Quantity elementCount Nat) : Quantity shardCount Nat :=
  ⟨n.magnitude⟩

/-! ### Distinctness — the swap hazards, as theorems -/

/-- The load-bearing pair: a worker count is not a shard count (the ~N× residency
confusion, made unwritable). -/
theorem workerCount_ne_shardCount : workerCount ≠ shardCount := by decide

theorem coreCount_ne_shardCount : coreCount ≠ shardCount := by decide
theorem coreCount_ne_workerCount : coreCount ≠ workerCount := by decide
theorem elementCount_ne_shardCount : elementCount ≠ shardCount := by decide
theorem storageCapacity_ne_storagePerElement : storageCapacity ≠ storagePerElement := by
  decide

end PropertyKindCalculus.Paradigm.Platform
