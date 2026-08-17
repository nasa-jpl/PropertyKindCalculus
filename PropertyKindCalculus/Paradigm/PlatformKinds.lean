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

/-- The elements ONE shard of a split holds: `elementCount / shardCount`.

Distinct from `elementCount` for the reason `shardCount` is distinct from `workerCount` — the
two counts are the two sides of a division, and a total handed to a solver expecting a slice
authorizes `N×` the residency the slice implies. It exists because a memory shape's slope is
not always a constant of the algorithm: an allocator that maps a large block and unmaps it
again, rather than retaining it in an arena, has a **different marginal cost per element**, and
which regime a run lands in is decided by the size of ONE SHARD's block — not the tile's, and
not the shard count's. That threshold is a property of this quotient and of nothing else, which
is what makes it a kind rather than an arithmetic convenience. -/
def sliceElementCount : KindOfProperty :=
  { id := "per-shard slice element count", scale := .ratio }

/-! ### The time kinds — the term `decideShards` had no way to state

The three count caps answer "how many shards *fit*". None of them answers "how many shards are
worth having", and measured, the two questions have different answers: past an optimum the fixed
cost of spawning a task exceeds the work it takes away, so more parallelism is slower. The shape
is a fixed per-task cost amortized against shrinking per-task work, `t(N) = w·P/N + a·N`, which
is NOT a roofline — a roofline's corner sits at a fixed problem size, and this optimum moves as
`√P`.

Two kinds and not one composite. The closed-form optimum is `N* = √(w·P/a)`, and it is tempting
to record the single number `√(w/a)` that multiplies `√P` — but that quantity has dimension
`element^(−1/2)`, names nothing, and cannot be measured on its own: it is an artefact of solving,
not a property of the algorithm. `w` and `a` are separately measurable, separately meaningful,
and separately liable to change (a faster kernel moves `w`; a different task runtime moves `a`),
so they are the kinds, and the composite is what the solver computes. -/

/-- Elapsed wall-clock time, in **seconds** — the quantity a time model predicts and a stopwatch
reads. Ratio-scale: durations have a true zero and their ratios mean something ("twice as long"),
which is what licenses the whole model. -/
def elapsedTime : KindOfProperty :=
  { id := "elapsed wall-clock time", scale := .ratio }

/-- The marginal wall-clock cost per batch element (`w`, seconds/element) — the *work* rate. The
term that divides by the shard count, because it is work the shards share out. -/
def timePerElement : KindOfProperty :=
  { id := "time per batch element", scale := .ratio }

/-- The fixed wall-clock cost of one shard (`a`, seconds/shard) — spawn, schedule, join, and
whatever the runtime charges per task regardless of the work in it. The term that MULTIPLIES the
shard count, which is the whole reason an optimum exists.

Deliberately not the same kind as `timePerElement`, though both are seconds over a dimension-one
count: one is divided by `N` and the other multiplied by it, so a swap does not merely mis-scale
the answer — it inverts which way the optimum moves. -/
def timePerShard : KindOfProperty :=
  { id := "time per shard", scale := .ratio }

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

/-- `elementCount / shardCount = sliceElementCount` — what ONE shard of a split holds
(`maxShardsSplitPiecewise`): the quantity a regime threshold is a fact about. The quotient
of two counts is a count, and the result kind is the slice's rather than the total's, so the
two can never be compared against each other's thresholds. -/
theorem elementsOfSlice : QuotientKind elementCount shardCount sliceElementCount :=
  QuotientKind.ofRatio elementCount shardCount sliceElementCount

/-- `elementCount / sliceElementCount = shardCount` — the same division read for the other
factor: how many shards a total must be cut into for one slice to reach a stated size. This is
what locates a regime boundary on the shard axis (`maxShardsSplitPiecewise`), and it is a
separate law rather than an inversion of `elementsOfSlice` because the two answer different
questions and only one of them is a count of shards. -/
theorem shardsOfSlice : QuotientKind elementCount sliceElementCount shardCount :=
  QuotientKind.ofRatio elementCount sliceElementCount shardCount

/-- `timePerElement × elementCount = elapsedTime` — the *work* term `W = w·P` of the time
model, the exact analogue of `bytesOfElements` on the memory side. -/
theorem workOfElements : ProductKind timePerElement elementCount elapsedTime :=
  ProductKind.ofRatio timePerElement elementCount elapsedTime

/-- `timePerShard × shardCount = elapsedTime` — the *overhead* term `a·N`. The one term in
either model that grows with the count rather than shrinking with it. -/
theorem overheadOfShards : ProductKind timePerShard shardCount elapsedTime :=
  ProductKind.ofRatio timePerShard shardCount elapsedTime

/-- `elapsedTime / shardCount = elapsedTime` — the *shared* term `W/N`: total work handed to `N`
shards takes a duration, and dividing a duration by a dimension-one count leaves a duration. -/
theorem durationOfSharedWork : QuotientKind elapsedTime shardCount elapsedTime :=
  QuotientKind.ofRatio elapsedTime shardCount elapsedTime

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

/-- **The shard count that minimizes the modelled wall clock**: the stationary point
`N* = √(W/a)`, rounded to whichever of its integer neighbours is actually better.

**The model, because it is what this function is a solution *of*.** One term of work the shards
divide between them, one fixed cost every shard pays:

$$ t(N) \;=\; \underbrace{\frac{W}{N}}_{\text{shared work}} \;+\; \underbrace{a\,N}_{\text{per-shard cost}},
\qquad W = w\,P. $$

`t` is convex on `N > 0` (its second derivative is `2W/N³ > 0`), so the stationary point is the
minimum, and there is exactly one:

$$ \frac{dt}{dN} \;=\; -\frac{W}{N^{2}} + a \;=\; 0 \quad\Longrightarrow\quad N^{*} = \sqrt{W/a}. $$

A pleasant check, and a useful one for reading a measurement: at `N*` the two terms are *equal*,
each `√(Wa)`, so the minimum is

$$ t(N^{*}) \;=\; 2\sqrt{W a}. $$

That is the sanity test to apply to any candidate optimum — if the measured split between shared
work and per-shard overhead is far from even, either the count is not the optimum or the model is
not the right one.

**The four assumptions**, packed into those two terms, every one of which can be false while the
units stay perfectly consistent:

  * *the work divides evenly* — each shard takes exactly `W/N`. With `P` not divisible by `N` the
    wall clock is set by the largest shard, `⌈P/N⌉·w`, which is worse and not smooth;
  * *the shards are concurrent* — `W/N` is a duration only if all `N` run at once, so the model
    presumes at least `N` cores and no contention for them. Past the core count it is wrong in a
    way this term does not detect; the cores cap beside it is what covers that;
  * *the per-shard cost is serial* — `a·N` charges every shard's fixed cost to the critical path.
    **This is the assumption that creates the optimum.** If spawning and joining were themselves
    parallel the term would be `a·N/cores` or `a·log N`, `t` would fall monotonically, and there
    would be no interior minimum to find;
  * *`w` does not depend on `N`* — the marginal cost per element is the same at 1 shard and at 56.
    On the *memory* axis this deployment has already found that false (allocator arena retention
    and the mmap knee both move with `N`); on the time axis it is assumed and untested.

A named crossing rather than a law, for two reasons worth keeping apart. The *kind* reason: the
quotient `W/a` passes through a transient kind — seconds over seconds-per-shard is shards
**squared** — which nothing in this vocabulary names and which the square root immediately
removes, so the treatment is `Budget.combinedQ`'s (compute on the carrier, re-stamp the result)
rather than minting a `shardCount²`. The *metrological* reason, which matters more: this is not a
units cancellation at all, so a law would claim a check nobody performed. The four bullets above
are the content of that distinction.

`none` when there is no fixed per-shard cost: the modelled time is then monotonically decreasing
in `N`, so time does not constrain the count — the same `none` `maxShardsSplit` gives when memory
does not constrain it.

**The rounding is not to nearest, and the difference is real.** `t` is convex, so the integer
minimum is one of `N*`'s two neighbours; but `t(n) ≤ t(n+1)` exactly when `W/a ≤ n(n+1)`, i.e.
when `N*` is below the **geometric** mean `√(n(n+1))` — which is strictly less than the arithmetic
`n + ½`. Rounding to nearest therefore returns `n` throughout a band where `n+1` is genuinely
faster: the band is widest at small `n` (at `n = 1` it is `[1.414, 1.5)`) and it costs a real
1.7 % of wall clock there. -/
def optimalShardsOfWork (work : Quantity elapsedTime Float)
    (perShard : Quantity timePerShard Float) : Option (Quantity shardCount Nat) :=
  if perShard.magnitude ≤ 0.0 || work.magnitude ≤ 0.0 then none
  else
    -- `N*²`, in the transient shards-squared kind the square root removes.
    let ratio := work.magnitude / perShard.magnitude
    let n := Nat.max 1 (Float.sqrt ratio).floor.toUInt64.toNat
    some ⟨if ratio ≤ (n * (n + 1)).toFloat then n else n + 1⟩

/-! ### Distinctness — the swap hazards, as theorems -/

/-- The load-bearing pair: a worker count is not a shard count (the ~N× residency
confusion, made unwritable). -/
theorem workerCount_ne_shardCount : workerCount ≠ shardCount := by decide

/-- The time model's own load-bearing pair: `w` is divided by the shard count and `a` is
multiplied by it, so swapping them does not mis-scale the optimum — it inverts the direction the
optimum moves in. -/
theorem timePerElement_ne_timePerShard : timePerElement ≠ timePerShard := by decide

/-- A duration is not a rate. `w·P` and `a·N` are durations; `w` and `a` are not, and the model
adds the first pair while never adding the second. -/
theorem elapsedTime_ne_timePerElement : elapsedTime ≠ timePerElement := by decide

/-- The piecewise solver's own pair: a slice is not a total. Handing `maxShardsSplitPiecewise`
the tile's element count where its threshold expects one shard's would put every run on the
far side of the knee and size it by the cheaper regime — the unsafe direction. -/
theorem elementCount_ne_sliceElementCount : elementCount ≠ sliceElementCount := by decide

theorem coreCount_ne_shardCount : coreCount ≠ shardCount := by decide
theorem coreCount_ne_workerCount : coreCount ≠ workerCount := by decide
theorem elementCount_ne_shardCount : elementCount ≠ shardCount := by decide
theorem storageCapacity_ne_storagePerElement : storageCapacity ≠ storagePerElement := by
  decide

end PropertyKindCalculus.Paradigm.Platform
