/-
`paradigm.platform` — **host capacity introspection + the memory-bounded parallelism
solvers**: what the machine (or the cgroup it is caged in) will actually sustain, as queried
facts with provenance, and the two solver shapes that turn an algorithm's affine memory
model `bytes(P) = fixed + perElement·P` into a maximum sustainable parallelism level.

WHY. A batched deployment has two independent parallelism knobs — how many `runSharded`
task-shards a CPU run forks, and how many pixels a device batch carries — and both are
memory-bounded long before they are compute-bounded. Sizing them takes two inputs: the
algorithm's own memory shape (`MemShape`; static prior from the recorded tape —
`TapeCodegen.AiReport.maxLive` / `fusedPeakBytes` / `eagerHostBytesPerElem` — calibrated by
measurement), and the capacity of the platform the run actually landed on. This module is
the HOST half of the second input; the device twin (`cudaMemGetInfo`) is already exposed
through the allocator stats and surfaced as `BatchCarrier.deviceMemBudget`.

KINDED THROUGHOUT. Every quantity here is dimension one (bytes, elements, cores, workers,
shards, bytes-per-element), which is exactly the `dim_not_injective` regime — so every
scalar rides `Quantity k` with the role-named kinds of `Paradigm.PlatformKinds`, and the
solver arithmetic goes through the named product/quotient laws declared there. The two
count-producing quotients (`workersOfHeadroom`, `shardsOfHeadroom`) have identical
signatures and deliberately distinct result kinds: which count a division yields is
decided by which law is invoked, in writing, at the call site. The TEXTS are kinded too:
each parser input/output rides `NominalValue` at a per-format nominal kind (a
`/proc/meminfo` dump, the field key indexing it, a cgroup path, a provenance label are
four different kinds of `String`), so an argument swap is a compile error rather than a
silent parse failure. The remaining naked values are the non-properties: decision flags
(`Bool` facts about the derivation) and `System.FilePath`s (already nominally typed by
Lean). Kinds attach at the audited ingest boundaries — file reads minting their
per-format text kind (the path is the license) and pure parsers minting quantities from
text (the certified-ingest tier "adjudicated by the kernel interface contract") — and
erase at one: the `describe` log line and the `.magnitude`/`.value` reads of a caller
crossing back into naked code.

CGROUPS FIRST, `/proc/meminfo` SECOND. A containerized or slice-confined process is killed
at its cgroup `memory.max`, not at the host's `MemAvailable`, and the two disagree by
integer factors in practice (a ~28 GiB cap on a 62 GiB host is the observed norm on shared
worker queues). So the budget asks cgroup v2 (the process's own cgroup, minimum over
ancestors — a limit binds from any level), then cgroup v1, then `/proc/meminfo
MemAvailable`, and every answer carries its provenance so a sizing decision is auditable
from the log line alone. The same discipline for cores: the scheduler affinity mask
(`Cpus_allowed_list`) min'd with the cgroup CPU quota — never the raw host core count.

Everything is plain file reads (`IO.FS`) over pure, unit-testable parsers — no FFI, no
subprocess, and nothing queried here decides anything by itself. On a system without these
files (non-Linux), the queries answer `none`/1 and the solvers degrade to serial.
-/

import PropertyKindCalculus.Paradigm.PlatformKinds
import PropertyKindCalculus.QuantityFunction

namespace PropertyKindCalculus.Paradigm.Platform

open PropertyKindCalculus

/-! ### Pure parsers (the IO layer below only reads files and calls these)

The parsers are the INGEST boundary, kinded on BOTH sides: the input texts are
`NominalValue`s of per-format nominal kinds (`PlatformKinds` — a `/proc/meminfo` dump
and the field key that indexes it are different kinds of `String`, so swapping them is a
compile error), and each output mint `⟨…⟩` is licensed by the file's documented
semantics (`memory.max` IS a storage capacity; `Cpus_allowed_list` IS a core count) —
the adjudicated tier of `CertifiedIngest`, with the kernel ABI as the external
provenance. Inside a parser, `.value` drops to lexical processing; the quantity (or the
extracted text) is born at the return. -/

/-- A kernel CPU-list (`"0-3,8,10-11"`) → CPU count (`6`). Malformed parts count 0. -/
def parseCpuList (s : NominalValue cpuListText String) : Quantity coreCount Nat := Id.run do
  let s := s.value.trimAscii.toString
  if s.isEmpty then return ⟨0⟩
  let mut n := 0
  for part in s.splitOn "," do
    match part.splitOn "-" with
    | [a] => if a.toNat?.isSome then n := n + 1
    | [a, b] =>
      match a.toNat?, b.toNat? with
      | some x, some y => if y ≥ x then n := n + (y - x + 1)
      | _, _ => pure ()
    | _ => pure ()
  return ⟨n⟩

/-- The `Cpus_allowed_list` row of `/proc/self/status` content → CPU count. This is the
affinity mask the scheduler actually honours (what `sched_getaffinity` reports), which a
cpuset or a pinned container narrows below the host core count. (The row's payload is
re-minted as a `cpuListText` — licensed by the `/proc/self/status` format.) -/
def parseCpusAllowed (status : NominalValue procStatusText String) :
    Option (Quantity coreCount Nat) := Id.run do
  for line in status.value.splitOn "\n" do
    if line.startsWith "Cpus_allowed_list:" then
      return some (parseCpuList ⟨(line.drop "Cpus_allowed_list:".length).toString⟩)
  return none

/-- A cgroup memory-limit file's content → a storage capacity. `"max"` (v2 unlimited) and
the v1 no-limit sentinel (≈ `2^63`, what `memory.limit_in_bytes` reports when unset) parse
as `none` = no limit. -/
def parseLimitBytes (s : NominalValue memLimitText String) :
    Option (Quantity storageCapacity Nat) :=
  let s := s.value.trimAscii.toString
  if s == "max" then none
  else match s.toNat? with
    | some n => if n ≥ (1 <<< 60) then none else some ⟨n⟩
    | none => none

/-- cgroup v2 `cpu.max` content (`"<quota> <period>"`, µs) → whole cores `⌈quota/period⌉`;
`"max <period>"` = no quota. (The µs/µs quotient is dimension-erasing by the kernel's own
contract; the parser mints the resulting core count at the boundary.) -/
def parseCpuMaxCores (s : NominalValue cpuMaxText String) :
    Option (Quantity coreCount Nat) :=
  match (((s.value.split Char.isWhitespace).map toString).filter (!·.isEmpty)).toList with
  | [q, p] =>
    if q == "max" then none
    else match q.toNat?, p.toNat? with
      | some qn, some pn => if pn == 0 || qn == 0 then none else some ⟨(qn + pn - 1) / pn⟩
      | _, _ => none
  | _ => none

/-- A cgroup memory-*usage* file's content → a storage capacity. Deliberately not
`parseLimitBytes`: a usage admits no `"max"` and has no unlimited sentinel, so the limit
parser's `n ≥ 2^60 → none` rule would turn a real reading into "no limit" on any level whose
usage is large. The kinds keep the two apart (`memLimitText_ne_memUsageText`). -/
def parseUsageBytes (s : NominalValue memUsageText String) :
    Option (Quantity storageCapacity Nat) :=
  (s.value.trimAscii.toString).toNat?.map (⟨·⟩)

/-- A `memory.events` counter (`"oom 0\noom_kill 0"`) → an event count. Same dump-vs-key
kinding as `parseMemInfoBytes`, for the same reason. -/
def parseMemEventCount (events : NominalValue memEventsText String)
    (key : NominalValue memEventsFieldKey String) : Option (Quantity oomEventCount Nat) :=
  Id.run do
    for line in events.value.splitOn "\n" do
      if line.startsWith (key.value ++ " ") then
        return ((line.drop (key.value.length + 1)).toString.trimAscii.toString).toNat?.map (⟨·⟩)
    return none

/-- A `/proc/meminfo` field (`"MemAvailable:   40316 kB"`) → a storage capacity. The dump
and the key are DIFFERENT nominal kinds: the swapped call is a type error, not a silent
`none`. -/
def parseMemInfoBytes (meminfo : NominalValue meminfoText String)
    (key : NominalValue meminfoFieldKey String) : Option (Quantity storageCapacity Nat) :=
  Id.run do
    for line in meminfo.value.splitOn "\n" do
      if line.startsWith (key.value ++ ":") then
        let rest := (line.drop (key.value.length + 1)).toString.trimAscii.toString
        let toks := (((rest.split Char.isWhitespace).map toString).filter (!·.isEmpty)).toList
        match (toks.headD "").toNat? with
        | some kb => return some ⟨kb * 1024⟩
        | none => return none
    return none

/-- The process's cgroup v2 path from `/proc/self/cgroup` content (the `0::<path>` row;
v1-only systems have no such row). Input and output are different kinds of text — the
dump cannot be fed its own extract. -/
def parseCgroupV2Path (selfCgroup : NominalValue procCgroupText String) :
    Option (NominalValue cgroupPathText String) := Id.run do
  for line in selfCgroup.value.splitOn "\n" do
    if line.startsWith "0::" then
      let p := (line.drop 3).toString.trimAscii.toString
      return some ⟨if p.isEmpty then "/" else p⟩
  return none

/-! ### The capacity queries -/

/-- Read a file, `none` if absent or unreadable — every capacity file is optional by
nature (other cgroup version, other OS, tighter sandbox). -/
def readFile? (p : System.FilePath) : IO (Option String) := do
  try pure (some (← IO.FS.readFile p)) catch _ => pure none

/-- A queried budget: the quantity AND where it came from, because the first question after
an OOM-kill (or an inexplicably idle machine) is which limit the sizing believed. The
`source` is not a quantity but it IS kinded — a `capacityProvenance` nominal label, so a
provenance string cannot drift into (say) a path slot. -/
structure MemBudget where
  bytes : Quantity storageCapacity Nat
  /-- `cgroup-v2:<dir>` | `cgroup-v1` | `meminfo:MemAvailable` (| `cudaMemGetInfo:free`
  from the device twin). -/
  source : NominalValue capacityProvenance String
deriving Repr

/-- The cgroup-v2 directories whose limits bind this process: its own cgroup (relative
path `rel` under the mount root) and every ancestor up to the root — the effective limit
is the minimum over them. -/
def cgroupV2Dirs (rel : NominalValue cgroupPathText String) : List System.FilePath :=
  Id.run do
    let root : System.FilePath := "/sys/fs/cgroup"
    let mut dirs : List System.FilePath := []
    let mut cur : System.FilePath :=
      if rel.value == "/" then root else ⟨root.toString ++ rel.value⟩
    for _ in [0:32] do
      dirs := dirs ++ [cur]
      if cur.toString == root.toString then return dirs
      match cur.parent with
      | some p => cur := p
      | none => return dirs
    return dirs

/-- The effective cgroup-v2 memory limit: own cgroup and ancestors, minimum wins, the
binding directory named in the provenance. `none` when there is no v2 cgroup or no level
sets a limit. (Each file read mints its per-format text kind — the path IS the license.) -/
def cgroupV2MemLimit : IO (Option MemBudget) := do
  let some cg ← readFile? "/proc/self/cgroup" | return none
  let some rel := parseCgroupV2Path ⟨cg⟩ | return none
  let mut best : Option MemBudget := none
  for dir in cgroupV2Dirs rel do
    if let some txt ← readFile? (dir / "memory.max") then
      if let some b := parseLimitBytes ⟨txt⟩ then
        if best.all (fun m => b < m.bytes) then
          best := some { bytes := b, source := ⟨s!"cgroup-v2:{dir}"⟩ }
  return best

/-- **The host memory budget**, in the order the limits actually bind: cgroup v2, cgroup
v1, then the host's own `MemAvailable`. `none` = nothing readable (treat as
unconstrained-but-unknown, and say so). LIMIT semantics: the quantity is a cap on the
process's TOTAL use, so a consumer subtracts what it already holds (input columns, outputs
to be stitched) rather than treating it as free headroom. -/
def hostMemLimit : IO (Option MemBudget) := do
  if let some m ← cgroupV2MemLimit then return some m
  if let some txt ← readFile? "/sys/fs/cgroup/memory/memory.limit_in_bytes" then
    if let some b := parseLimitBytes ⟨txt⟩ then
      return some { bytes := b, source := ⟨"cgroup-v1"⟩ }
  if let some mi ← readFile? "/proc/meminfo" then
    if let some b := parseMemInfoBytes ⟨mi⟩ ⟨"MemAvailable"⟩ then
      return some { bytes := b, source := ⟨"meminfo:MemAvailable"⟩ }
  return none

/-- The concurrency the scheduler will actually grant. -/
structure CoreBudget where
  /-- The effective count: `min(affinity, quota)` over what was readable, floor 1. -/
  cores : Quantity coreCount Nat
  /-- `|Cpus_allowed_list|`, when readable. -/
  affinity : Option (Quantity coreCount Nat) := none
  /-- The cgroup CPU quota in whole cores (`⌈quota/period⌉`), when one is set. -/
  quota : Option (Quantity coreCount Nat) := none
deriving Repr

/-- The effective cgroup-v2 CPU quota (own cgroup and ancestors, minimum wins). -/
def cgroupV2CpuQuota : IO (Option (Quantity coreCount Nat)) := do
  let some cg ← readFile? "/proc/self/cgroup" | return none
  let some rel := parseCgroupV2Path ⟨cg⟩ | return none
  let mut best : Option (Quantity coreCount Nat) := none
  for dir in cgroupV2Dirs rel do
    if let some txt ← readFile? (dir / "cpu.max") then
      if let some q := parseCpuMaxCores ⟨txt⟩ then
        if best.all (fun b => q < b) then best := some q
  return best

/-- The cgroup-v1 CPU quota (`cfs_quota_us` = `-1` when unset, which `toNat?` rejects). -/
def cgroupV1CpuQuota : IO (Option (Quantity coreCount Nat)) := do
  let some qs ← readFile? "/sys/fs/cgroup/cpu/cpu.cfs_quota_us" | return none
  let some ps ← readFile? "/sys/fs/cgroup/cpu/cpu.cfs_period_us" | return none
  match (qs.trimAscii.toString).toNat?, (ps.trimAscii.toString).toNat? with
  | some q, some p => if q == 0 || p == 0 then return none else return some ⟨(q + p - 1) / p⟩
  | _, _ => return none

/-- **The cores this process can actually use**: affinity mask ∧ cgroup quota, floor 1 —
`1` when nothing is readable (non-Linux), degrading to serial rather than oversubscribing. -/
def availableCores : IO CoreBudget := do
  let affinity := parseCpusAllowed ⟨(← readFile? "/proc/self/status").getD ""⟩
  let quota ← do
    match ← cgroupV2CpuQuota with
    | some q => pure (some q)
    | none => cgroupV1CpuQuota
  let cores := match affinity, quota with
    | some a, some q => Quantity.max ⟨1⟩ (Quantity.min a q)
    | some a, none   => Quantity.max ⟨1⟩ a
    | none,   some q => Quantity.max ⟨1⟩ q
    | none,   none   => ⟨1⟩
  return { cores, affinity, quota }

/-! ### The container census — evidence about the environment, not about the algorithm

`hostMemLimit` answers *what may I use*, which is the one number a solver needs. It answers
it by taking a minimum and discarding everything else it read. The census keeps the rest,
because a different question is asked after the fact and cannot be answered from a minimum:
**where** does the binding limit sit, what sits above it, and who else is holding memory.

Per-level attribution rather than a total is the whole point. "The host is busy" is not
reportable to anyone; "the sibling of my container is holding 34 GiB" is. The difference is
`parent.memory.current − own.memory.current`, which needs the chain and not its minimum.

The known limitation belongs here rather than in a footnote: under a **private cgroup
namespace** (the Docker default on current engines) a container sees its own cgroup as the
root and the ancestors are simply not there. The census then reports one level and no parent,
which is itself the finding — not a failure to read — and `/proc/meminfo`, usually not
namespaced without `lxcfs`, is what remains. -/

/-- One cgroup level's readable facts. Every field is optional because every one of them is
absent on some real configuration (v1, a namespaced view, a kernel below 5.19 for
`memory.peak`, a tighter sandbox), and an absent reading is evidence too. -/
structure CgroupLevel where
  /-- The level's directory under the cgroup mount — `/sys/fs/cgroup` is the root. -/
  dir : String
  /-- `memory.max` at this level: the limit this level imposes, if it imposes one. -/
  memMax : Option (Quantity storageCapacity Nat) := none
  /-- `memory.current`: usage of this level's ENTIRE subtree, which is what makes the
  sibling subtraction possible. -/
  memCurrent : Option (Quantity storageCapacity Nat) := none
  /-- `memory.peak` (v2, kernel ≥ 5.19) or v1's `memory.max_usage_in_bytes` — the same
  attribution at the worst moment rather than at sampling time. -/
  memPeak : Option (Quantity storageCapacity Nat) := none
  /-- `memory.events oom` — times this level hit its limit. -/
  oom : Option (Quantity oomEventCount Nat) := none
  /-- `memory.events oom_kill` — times this level actually killed something. -/
  oomKill : Option (Quantity oomEventCount Nat) := none
deriving Repr, Inhabited

/-- What one job can establish about the machine it woke up inside. -/
structure Census where
  /-- The `0::` path from `/proc/self/cgroup`. Its *shape* names the orchestrator —
  `/docker/…`, `/ecs/…`, `/kubepods/…` are different answers — and its depth says whether
  there is a slot layer at all. -/
  cgroupPath : Option (NominalValue cgroupPathText String) := none
  /-- Own cgroup first, then each ancestor up to the root. A single entry means no parent
  was visible, which under a private namespace is the expected reading. -/
  levels : List CgroupLevel := []
  /-- `/proc/meminfo MemTotal` — the machine, which this job does not own. -/
  memTotal : Option (Quantity storageCapacity Nat) := none
  /-- `/proc/meminfo MemAvailable` — already nets out reclaimable cache, so
  `MemTotal − MemAvailable` less this job's own usage is everything else on the box. -/
  memAvailable : Option (Quantity storageCapacity Nat) := none
  /-- What the solver will actually use: affinity ∧ quota. -/
  cores : CoreBudget := { cores := ⟨1⟩ }
  /-- The host's online CPU count — the third leg of the core-axis disagreement, and the
  one a naive `nproc` would have taken. -/
  hostCores : Option (Quantity coreCount Nat) := none
deriving Repr, Inhabited

/-- Read one cgroup level. -/
def readCgroupLevel (dir : System.FilePath) : IO CgroupLevel := do
  let read? (name : String) : IO (Option String) := readFile? (dir / name)
  let events := (← read? "memory.events").getD ""
  return {
    dir := dir.toString
    memMax := (← read? "memory.max").bind (fun t => parseLimitBytes ⟨t⟩)
    memCurrent := (← read? "memory.current").bind (fun t => parseUsageBytes ⟨t⟩)
    -- v2 ≥ 5.19 first, then v1's spelling of the same quantity.
    memPeak := (← read? "memory.peak").bind (fun t => parseUsageBytes ⟨t⟩) <|>
               (← read? "memory.max_usage_in_bytes").bind (fun t => parseUsageBytes ⟨t⟩)
    oom := parseMemEventCount ⟨events⟩ ⟨"oom"⟩
    oomKill := parseMemEventCount ⟨events⟩ ⟨"oom_kill"⟩ }

/-- **The census.** Reads what an unprivileged process inside a container can establish about
the limits it is running under and who it is sharing with. Never fails: every field is
optional and an absent one is a reading. -/
def containerCensus : IO Census := do
  let cgPath := (← readFile? "/proc/self/cgroup").bind (fun t => parseCgroupV2Path ⟨t⟩)
  let levels ← match cgPath with
    | some rel => (cgroupV2Dirs rel).mapM readCgroupLevel
    | none => pure []
  let meminfo := (← readFile? "/proc/meminfo").getD ""
  -- `/sys/devices/system/cpu/online` is a kernel CPU-list, the same format the affinity
  -- mask uses — so the host figure and the affinity figure are parsed by one authority
  -- rather than by two spellings that could disagree about what a range means.
  let hostCores := (← readFile? "/sys/devices/system/cpu/online").map
    (fun t => parseCpuList ⟨t.trimAscii.toString⟩)
  return {
    cgroupPath := cgPath
    levels
    memTotal := parseMemInfoBytes ⟨meminfo⟩ ⟨"MemTotal"⟩
    memAvailable := parseMemInfoBytes ⟨meminfo⟩ ⟨"MemAvailable"⟩
    cores := ← availableCores
    hostCores }

/-- Which level's `memory.max` actually binds, and what it is — the question `hostMemLimit`
answers with a bare minimum. `none` = no level states a limit. -/
def Census.bindingLevel (c : Census) : Option CgroupLevel :=
  c.levels.foldl (init := none) fun best l =>
    match l.memMax with
    | none => best
    | some b => if best.all (fun (m : CgroupLevel) => m.memMax.all (b < ·)) then some l else best

/-- **What the siblings hold**: the parent's whole-subtree usage less this job's own. The
number an "excessive neighbour" claim needs, and the reason the census keeps the chain
instead of a minimum.

`none` when there is no visible parent (a private cgroup namespace — the expected reading
under Docker's default, and a finding rather than an error) or when either level's
`memory.current` is unreadable. Saturating subtraction: the two files are sampled a moment
apart, so a parent that reads *below* its own child is a race and not a negative quantity. -/
def Census.siblingBytes (c : Census) : Option (Quantity storageCapacity Nat) :=
  match c.levels with
  | own :: parent :: _ => do
    let o ← own.memCurrent
    let p ← parent.memCurrent
    pure ⟨p.magnitude - o.magnitude⟩
  | _ => none

/-! ### The solvers -/

/-- An algorithm's affine memory model, per shard/worker/batch:
`bytes(elems) = fixedBytes + bytesPerElem·elems`. The static prior comes from the recorded
tape (`TapeCodegen.AiReport`); a measured probe refines it, and the measurement is the
authority — a guessed factor once authorized ~2× the safe worker count where the measured
one did not. `bytesPerElem` is `Float`-carried so a calibrated factor needs no rounding;
its KIND (`storagePerElement`) is not a storage capacity, so a slope can never slip into a
budget slot or vice versa. -/
structure MemShape where
  /-- Per-worker/shard fixed overhead (runtime context, process image, marshaling slack). -/
  fixedBytes : Quantity storageCapacity Nat := ⟨0⟩
  /-- Marginal storage per element (pixel) of one shard/batch. -/
  bytesPerElem : Quantity storagePerElement Float := ⟨0⟩
deriving Repr

/-- `bytes(elems)` of one shard/worker under this shape: the `bytesOfElements` product law
(variable term rounded up), then a same-kind add of the fixed overhead. -/
def MemShape.bytesFor (shape : MemShape) (elems : Quantity elementCount Nat) :
    Quantity storageCapacity Nat :=
  shape.fixedBytes +
    (Quantity.mul bytesOfElements shape.bytesPerElem elems.asFloat).ceilToNat

/-- SOLVER, single-launch shape (a megakernel driver: ONE resident batch, choose its element
count): the largest `elems` with `bytesFor elems ≤ budget`, i.e. the `elementsOfBudget`
quotient `⌊(budget − fixed) / bytesPerElem⌋`. `none` = no per-element term, memory does not
constrain the batch; `some 0` = the fixed term alone exceeds the budget. Floor-safe against
`bytesFor`'s ceiling: the quotient `q` has `bytesPerElem·q ≤ budget − fixed` with an integer
right side, so `⌈bytesPerElem·q⌉` still fits. -/
def MemShape.maxElems (shape : MemShape) (budget : Quantity storageCapacity Nat) :
    Option (Quantity elementCount Nat) :=
  if shape.bytesPerElem ≤ ⟨0⟩ then none
  else if shape.fixedBytes > budget then some ⟨0⟩
  else some (Quantity.div elementsOfBudget
    (budget - shape.fixedBytes).asFloat shape.bytesPerElem).floorToNat

/-- SOLVER, worker shape (a `chunk_fit`-style driver: fixed `elemsPerWorker` per worker,
choose how many run concurrently): the `workersOfHeadroom` quotient
`⌊headroom / bytesFor(elemsPerWorker)⌋`. `headroom` is the budget minus everything already
resident. `none` = the shape is degenerate (zero cost) and memory does not constrain;
`some 0` = not even one worker fits — shrink the block, not the count. -/
def maxConcurrentWorkers (shape : MemShape) (elemsPerWorker : Quantity elementCount Nat)
    (headroom : Quantity storageCapacity Nat) : Option (Quantity workerCount Nat) :=
  let per := shape.bytesFor elemsPerWorker
  if per == ⟨0⟩ then none else some (Quantity.div workersOfHeadroom headroom per)

/-- SOLVER, split shape (`runSharded`: N shards partition ONE resident total, all
concurrent — the variable term `bytesPerElem·total` is invariant in N and only the
per-shard `fixedBytes` scales): the `shardsOfHeadroom` quotient
`⌊(headroom − bytesPerElem·total) / fixedBytes⌋`. `none` = memory does not constrain N (no
fixed term); `some 0` = the variable term alone overflows the headroom, so NO shard count
fits — the tile must shrink (row-chunk externally), not the count. Same quotient signature
as `maxConcurrentWorkers`, different law, different count — see `PlatformKinds`. -/
def maxShardsSplit (shape : MemShape) (totalElems : Quantity elementCount Nat)
    (headroom : Quantity storageCapacity Nat) : Option (Quantity shardCount Nat) :=
  let varBytes :=
    (Quantity.mul bytesOfElements shape.bytesPerElem totalElems.asFloat).ceilToNat
  if varBytes > headroom then some ⟨0⟩
  else if shape.fixedBytes == ⟨0⟩ then none
  else some (Quantity.div shardsOfHeadroom (headroom - varBytes) shape.fixedBytes)

/-- SOLVER, split shape whose SLOPE CHANGES at a slice threshold: the largest shard count that
fits when `bytesPerElem` is not one constant but two, selected by how big ONE shard's slice is.

**Why a solver needs this at all.** `maxShardsSplit`'s model has the variable term invariant in
`N` — the shards partition one resident total, so only the per-shard fixed overhead scales. That
is exact while the marginal cost per element is a constant of the algorithm, and it is measurably
false across an allocator regime change: a slice large enough to be mapped and unmapped directly
costs *fewer* bytes per element than one served out of retained arenas, so the same tile cut into
fewer, larger pieces can hold less than it does cut into many. Which regime a run lands in is a
fact about `total / N` — the slice, `sliceElementCount` — and about neither factor alone.

**Selected, never combined.** `above` is in force strictly past `threshold`, `base` at and below
it. An envelope over the two pieces (a `max`) would be the wrong answer and not merely a loose
one: an envelope of affine pieces is convex and can only ever ascend, while the regime change
this exists for is a *descent*, so the envelope would charge the retained-arena slope in the very
configuration that does not pay it.

**How it is solved: two clamped solves, not an iteration.** Each piece is `maxShardsSplit`'s own
model within the regime it governs, and the regimes are an interval each — `above` for
`N < total/threshold`, `base` for the rest — so the answer is the larger of (that piece's cap,
clamped to its own regime) over the two, with no fixed point to chase. A search that fed one
piece's answer back through the selector could oscillate across the boundary; this cannot,
because neither solve is ever asked about a count its own regime does not contain.

`none` = memory does not constrain `N` (the base regime carries no per-shard fixed term, so
counts above the boundary are unbounded). `some 0` = neither regime fits at any count — the
variable term alone overflows both ways, and the fix is a smaller total, not a smaller count. -/
def maxShardsSplitPiecewise (base above : MemShape)
    (threshold : Quantity sliceElementCount Float)
    (totalElems : Quantity elementCount Nat)
    (headroom : Quantity storageCapacity Nat) : Option (Quantity shardCount Nat) :=
  if threshold ≤ ⟨0⟩ then
    -- Every slice of a non-empty total is bigger than a non-positive threshold, so one regime
    -- governs the whole axis and the piecewise question does not arise.
    maxShardsSplit above totalElems headroom
  else
    -- The boundary on the SHARD axis: the count at which one slice is exactly the threshold.
    -- `above` governs strictly below it, so its last count is the largest integer under the
    -- boundary — `⌈boundary⌉ − 1`, which is `boundary − 1` when the division comes out whole.
    let boundary : Quantity shardCount Nat :=
      (Quantity.div shardsOfSlice totalElems.asFloat threshold).ceilToNat
    let lastAbove : Quantity shardCount Nat := ⟨boundary.magnitude - 1⟩
    let firstBase : Quantity shardCount Nat := ⟨lastAbove.magnitude + 1⟩
    -- Each piece, capped by its own regime. A cap of `0` is `maxShardsSplit`'s "not at any
    -- count", which contributes nothing rather than a candidate of zero shards.
    let fromAbove : Option (Quantity shardCount Nat) :=
      if lastAbove.magnitude == 0 then none
      else match maxShardsSplit above totalElems headroom with
        | none => some lastAbove
        | some c => if c.magnitude == 0 then none else some (Quantity.min c lastAbove)
    match maxShardsSplit base totalElems headroom with
    -- The base regime is unbounded above the boundary: memory does not constrain the count.
    | none => none
    | some c =>
      let fromBase : Option (Quantity shardCount Nat) :=
        if c.magnitude ≥ firstBase.magnitude then some c else none
      match fromAbove, fromBase with
      | none, none => some ⟨0⟩
      | some a, none => some a
      | none, some b => some b
      | some a, some b => some (Quantity.max a b)

/-- **What a split is solved against**: one affine shape, or two selected by the slice.

A sum and not a `MemShape` with optional extra fields, because the two are different claims and
the difference must be visible at the call site. `simple` says the marginal cost per element is
a constant of the algorithm — the case where the piecewise question does not arise, not a
degenerate instance of it. `piecewise` says a threshold on ONE SHARD's slice selects between two
costs, and carries the threshold with the pieces it separates, so no caller can pair one
regime's slope with another's boundary. -/
inductive SplitShape where
  /-- One affine model, `bytes(N) = fixed·N + perElem·total`, at every count. -/
  | simple (shape : MemShape)
  /-- Two, with `above` in force strictly past the slice threshold and `base` at and below it. -/
  | piecewise (base above : MemShape) (threshold : Quantity sliceElementCount Float)

/-- The memory-implied cap on the shard count, by whichever solver the shape calls for.
Same reading either way: `none` = memory does not constrain, `some 0` = no count fits. -/
def SplitShape.memCap : SplitShape → Quantity elementCount Nat →
    Quantity storageCapacity Nat → Option (Quantity shardCount Nat)
  | .simple s, total, headroom => maxShardsSplit s total headroom
  | .piecewise b a t, total, headroom => maxShardsSplitPiecewise b a t total headroom

/-- **Is the far piece in force at this count?** Splitting a total `n` ways makes slices of
`total/n`, and `above` governs strictly past the threshold.

The regime rule lives here and nowhere else: a decision needs the SHAPE it ran under and its
account needs the NAME of that shape, and two functions deciding the same boundary
independently is how a log line comes to disagree with the arithmetic it describes.

`n = 0` cannot arise from a decision (the count is floored at 1) and answers `false`, the
conservative reading of a question that was not asked. A simple shape is never "above": it has
no far piece to be in. -/
def SplitShape.aboveAt : SplitShape → Quantity elementCount Nat → Quantity shardCount Nat → Bool
  | .simple _, _, _ => false
  | .piecewise _ _ t, total, n =>
    if n.magnitude == 0 then false
    else
      let slice : Quantity sliceElementCount Float :=
        Quantity.div elementsOfSlice total.asFloat ⟨n.magnitude.toFloat⟩
      slice.magnitude > t.magnitude

/-- **Which piece is in force at a given count** — the shape a decision actually ran under,
for the solver's own re-reading and for a caller reporting what it charged. -/
def SplitShape.pieceAt (s : SplitShape) (total : Quantity elementCount Nat)
    (n : Quantity shardCount Nat) : MemShape :=
  match s with
  | .simple sh => sh
  | .piecewise b a _ => if s.aboveAt total n then a else b

/-! ### The time shape — the fourth cap

`decideShards` used to answer only "how many shards *fit*". Measured, that is not the same
question as "how many shards are worth having": past an optimum the fixed cost of spawning a task
exceeds the work it takes away. On one measured algorithm, picking 56 shards costs **3.93×** the
wall clock of picking 8 at 25 600 elements and **2.20×** at 102 400 — the range production blocks
land in — so the cap is not a refinement, it is the difference between a rule that is right and
one that is right about memory and wrong about time.

Optional, and that is a finding rather than an escape hatch: on the same host three other
algorithms need no such cap at all, because their per-task overhead is negligible against their
work. The term binds for one algorithm and not the others, which is exactly why it belongs in a
keyed measurement a caller supplies and not in this solver's constants. -/

/-- The time model of a sharded run: `t(N) = perElement·total/N + perShard·N`. A *fixed* cost per
spawned shard, amortized against work that shrinks as it is divided — the shape §2.3 of the
deployment's own analysis settles, and deliberately not a roofline (a roofline's corner sits at a
fixed problem size; this optimum moves as `√total`).

Zero `perShard` is the honest default: with no measured per-task cost the model says more shards
are always faster, and the solver correctly declines to cap. -/
structure TimeShape where
  /-- `w` — marginal seconds per batch element. Divided by the shard count: shards share it. -/
  perElement : Quantity timePerElement Float := ⟨0⟩
  /-- `a` — fixed seconds per shard. Multiplied by the shard count: every shard pays it. -/
  perShard : Quantity timePerShard Float := ⟨0⟩
deriving Repr

/-- The total work `W = w·total` this shape predicts, through the `workOfElements` product law —
the numerator of the time model, before any shard count is chosen. -/
def TimeShape.work (shape : TimeShape) (totalElems : Quantity elementCount Nat) :
    Quantity elapsedTime Float :=
  Quantity.mul workOfElements shape.perElement totalElems.asFloat

/-- The modelled wall clock at a given shard count: `W/N + a·N`, each term through its own law
(`durationOfSharedWork` and `overheadOfShards`) and summed as the same-kind duration both are.
Exposed because a cap a caller cannot check is a cap a caller has to trust: this is the function
`optimalShards` claims to minimize, and comparing the two is one line. -/
def TimeShape.wallClock (shape : TimeShape) (totalElems : Quantity elementCount Nat)
    (n : Quantity shardCount Nat) : Quantity elapsedTime Float :=
  let shared := Quantity.div durationOfSharedWork (shape.work totalElems) n.asFloat
  let overhead := Quantity.mul overheadOfShards shape.perShard n.asFloat
  ⟨shared.magnitude + overhead.magnitude⟩

/-- SOLVER, time shape: the shard count minimizing the modelled wall clock, `N* = √(W/a)`
through the `optimalShardsOfWork` crossing. `none` = time does not constrain the count (no
measured per-shard cost, or no work), the same reading `maxShardsSplit` gives for memory. -/
def TimeShape.optimalShards (shape : TimeShape) (totalElems : Quantity elementCount Nat) :
    Option (Quantity shardCount Nat) :=
  optimalShardsOfWork (shape.work totalElems) shape.perShard

/-- The audited outcome of `decideShards`: the count, plus every term that produced it.
The two `Bool`s are decision *flags* (facts about the derivation), not quantities. -/
structure ShardDecision where
  /-- The shard count to run (≥ 1). -/
  nShards : Quantity shardCount Nat
  cores : CoreBudget
  budget : Option MemBudget
  /-- The memory-implied cap (`maxShardsSplit`); `none` = memory did not constrain. -/
  memCap : Option (Quantity shardCount Nat)
  /-- The time-implied cap (`TimeShape.optimalShards`); `none` = no time model was supplied, or
  the one supplied has no per-shard cost, so time did not constrain. The three caps beside it
  answer "how many shards fit"; this one answers "how many are worth having". -/
  timeCap : Option (Quantity shardCount Nat)
  /-- The resident variable term alone exceeds the budget: even `nShards = 1` risks the
  cap. The fix is a smaller total (external row-chunking), not a smaller count. -/
  overflow : Bool
  /-- An explicit override short-circuited the solver (the caps are still reported). -/
  overridden : Bool
deriving Repr

/-- One log line with every term and its provenance — the `chunked.py` budget-table UX:
what was decided, from which numbers, believed from which source, **and by whom**. The
`emitter` is the line's own attribution: a decision is only actionable if the reader knows
which program made it, and on a host running six deployment executables that is not
inferable from the numbers. Applications pass their own designation across an authored
crossing into `decisionEmitter` rather than a bare `String` — the emitter and the budget's
`source` are the two labels of this line, and `decisionEmitter_ne_capacityProvenance`
keeps them out of each other's slot. (The `.magnitude`/`.value` reads and `showMiB` here
are the sanctioned display erasure: the log line is where kinds leave the calculus.) -/
def ShardDecision.describe (d : ShardDecision)
    (emitter : NominalValue decisionEmitter String) : String :=
  let mem := match d.budget with
    | some b => s!"budget {showMiB b.bytes} [{b.source.value}]"
    | none => "budget unknown"
  let cap := match d.memCap with
    | some m => s!"mem-cap {m.magnitude}"
    | none => "mem-cap none"
  let tcap := match d.timeCap with
    | some t => s!", time-cap {t.magnitude}"
    | none => ""
  let how := if d.overridden then "override" else "auto"
  let over := if d.overflow then
      "  ⚠ resident set alone exceeds the budget — shrink the tile/block, not the count"
    else ""
  s!"[{emitter.value}] shards={d.nShards.magnitude} ({how}; \
cores={d.cores.cores.magnitude}, {cap}{tcap}, {mem}){over}"

/-- **Decide a `runSharded` shard count**: `min(cores-implied cap, memory cap, hardCap)`,
floor 1 — or the explicit `override` when the caller has one (a `TILE_SHARDS`-style env
contract), which wins verbatim while the bypassed caps are still reported. `reservedBytes`
is everything the caller already holds or will hold regardless of N (input columns,
stitched outputs) — subtracted here because the budget has LIMIT semantics
(`hostMemLimit`), so holdings must be charged exactly once. `hardCap` bounds by useful
parallelism; a caller capping by element count states the license through
`elementsAsShardCap`. The cores bound enters through the authored `coresAsShardCap`
crossing — the one place two count kinds meet, each conversion named and licensed.

`time` is the fourth cap and the only one that answers a different *question*: the other three
bound what fits, and this one bounds what is worth running. It is an `Option` because whether a
per-task cost is worth charging is a measured fact about one algorithm — on the host this was
established, one of four algorithms needs it — so an absent time model means "not measured here",
which is exactly the reading `none` should have. -/
def decideShardsOf (shape : SplitShape) (totalElems : Quantity elementCount Nat)
    (reservedBytes : Quantity storageCapacity Nat := ⟨0⟩)
    (override : Option (Quantity shardCount Nat) := none)
    (hardCap : Option (Quantity shardCount Nat) := none)
    (time : Option TimeShape := none) : IO ShardDecision := do
  let cores ← availableCores
  let budget ← hostMemLimit
  let memCap := match budget with
    | some b => shape.memCap totalElems (b.bytes - reservedBytes)
    | none => none
  let overflow := memCap == some ⟨0⟩
  let timeCap := time.bind (·.optimalShards totalElems)
  let auto :=
    let c := match memCap with
      | some m => Quantity.min (coresAsShardCap cores.cores) m
      | none => coresAsShardCap cores.cores
    let c := match hardCap with
      | some h => Quantity.min c h
      | none => c
    match timeCap with
    | some t => Quantity.min c t
    | none => c
  let n := match override with
    | some o => Quantity.max ⟨1⟩ o
    | none => Quantity.max ⟨1⟩ auto
  return { nShards := n, cores, budget, memCap, timeCap, overflow,
           overridden := override.isSome }

/-- **Decide a `runSharded` shard count** against ONE affine shape — `decideShardsOf` at the
shape every caller had before a slope could change under a threshold. Kept as the name the
callers use, and as a definition rather than a default argument, because the simple shape is
not a degenerate piecewise one: it is the case where the question does not arise. -/
def decideShards (shape : MemShape) (totalElems : Quantity elementCount Nat)
    (reservedBytes : Quantity storageCapacity Nat := ⟨0⟩)
    (override : Option (Quantity shardCount Nat) := none)
    (hardCap : Option (Quantity shardCount Nat) := none)
    (time : Option TimeShape := none) : IO ShardDecision :=
  decideShardsOf (.simple shape) totalElems reservedBytes override hardCap time

end PropertyKindCalculus.Paradigm.Platform
