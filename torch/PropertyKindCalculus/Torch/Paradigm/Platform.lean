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
    (Quantity.mul bytesOfElements shape.bytesPerElem
        (elems.castCarrier Nat.toFloat)).castCarrier (fun x => x.ceil.toUInt64.toNat)

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
  else some ((Quantity.div elementsOfBudget
    ((budget - shape.fixedBytes).castCarrier Nat.toFloat)
    shape.bytesPerElem).castCarrier (fun x => x.floor.toUInt64.toNat))

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
  let varBytes := (Quantity.mul bytesOfElements shape.bytesPerElem
    (totalElems.castCarrier Nat.toFloat)).castCarrier (fun x => x.ceil.toUInt64.toNat)
  if varBytes > headroom then some ⟨0⟩
  else if shape.fixedBytes == ⟨0⟩ then none
  else some (Quantity.div shardsOfHeadroom (headroom - varBytes) shape.fixedBytes)

/-- The audited outcome of `decideShards`: the count, plus every term that produced it.
The two `Bool`s are decision *flags* (facts about the derivation), not quantities. -/
structure ShardDecision where
  /-- The shard count to run (≥ 1). -/
  nShards : Quantity shardCount Nat
  cores : CoreBudget
  budget : Option MemBudget
  /-- The memory-implied cap (`maxShardsSplit`); `none` = memory did not constrain. -/
  memCap : Option (Quantity shardCount Nat)
  /-- The resident variable term alone exceeds the budget: even `nShards = 1` risks the
  cap. The fix is a smaller total (external row-chunking), not a smaller count. -/
  overflow : Bool
  /-- An explicit override short-circuited the solver (the caps are still reported). -/
  overridden : Bool
deriving Repr

/-- One log line with every term and its provenance — the `chunked.py` budget-table UX:
what was decided, from which numbers, believed from which source. (The `.magnitude` reads
here are the sanctioned display erasure: the log line is where kinds leave the calculus.) -/
def ShardDecision.describe (d : ShardDecision) : String :=
  let mem := match d.budget with
    | some b => s!"budget {b.bytes.magnitude / (1 <<< 20)} MiB [{b.source.value}]"
    | none => "budget unknown"
  let cap := match d.memCap with
    | some m => s!"mem-cap {m.magnitude}"
    | none => "mem-cap none"
  let how := if d.overridden then "override" else "auto"
  let over := if d.overflow then
      "  ⚠ resident set alone exceeds the budget — shrink the tile/block, not the count"
    else ""
  s!"shards={d.nShards.magnitude} ({how}; cores={d.cores.cores.magnitude}, {cap}, {mem}){over}"

/-- **Decide a `runSharded` shard count**: `min(cores-implied cap, memory cap, hardCap)`,
floor 1 — or the explicit `override` when the caller has one (a `TILE_SHARDS`-style env
contract), which wins verbatim while the bypassed caps are still reported. `reservedBytes`
is everything the caller already holds or will hold regardless of N (input columns,
stitched outputs) — subtracted here because the budget has LIMIT semantics
(`hostMemLimit`), so holdings must be charged exactly once. `hardCap` bounds by useful
parallelism; a caller capping by element count states the license through
`elementsAsShardCap`. The cores bound enters through the authored `coresAsShardCap`
crossing — the one place two count kinds meet, each conversion named and licensed. -/
def decideShards (shape : MemShape) (totalElems : Quantity elementCount Nat)
    (reservedBytes : Quantity storageCapacity Nat := ⟨0⟩)
    (override : Option (Quantity shardCount Nat) := none)
    (hardCap : Option (Quantity shardCount Nat) := none) : IO ShardDecision := do
  let cores ← availableCores
  let budget ← hostMemLimit
  let memCap := match budget with
    | some b => maxShardsSplit shape totalElems (b.bytes - reservedBytes)
    | none => none
  let overflow := memCap == some ⟨0⟩
  let auto :=
    let c := match memCap with
      | some m => Quantity.min (coresAsShardCap cores.cores) m
      | none => coresAsShardCap cores.cores
    match hardCap with
    | some h => Quantity.min c h
    | none => c
  let n := match override with
    | some o => Quantity.max ⟨1⟩ o
    | none => Quantity.max ⟨1⟩ auto
  return { nShards := n, cores, budget, memCap, overflow, overridden := override.isSome }

end PropertyKindCalculus.Paradigm.Platform
