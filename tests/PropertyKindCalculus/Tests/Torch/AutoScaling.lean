/-
# Validation probes — peak-residency accounting + the platform capacity parsers/solvers

Inhabitation and value probes for the auto-scaling substrate:

  * `paradigm.tape_codegen.maxLiveNodes` — the eager carrier's peak live-buffer count,
    pinned on tapes with hand-computed live-set structure (chain, diamond, fan-in, a
    const leaf) recorded at the tape carrier and CSE'd, exactly as the deployments record
    them; plus the `AiReport.maxLive` threading and the peak-bytes shapes.
  * `paradigm.platform` — the pure parsers pinned on captured `/proc` / cgroup content
    (including the v2 `"max"` and v1 no-limit sentinel cases, which MUST parse as "no
    limit", not as a colossal budget), and the two solver shapes pinned on hand-solved
    budgets — including the `some 0` overflow answers, whose meaning ("shrink the block /
    tile, not the count") a driver acts on.

Everything here is pure (`#guard`-evaluable): the tapes carry host `Tensor Float` scalars,
and the platform layer's IO is never entered — its parsers take file *content* as strings,
which is precisely what makes them probeable.
-/

import PropertyKindCalculus.Torch.Paradigm.TapeCodegen
import PropertyKindCalculus.Torch.Paradigm.Platform

namespace PropertyKindCalculus.Tests.AutoScaling

open Spec
open Runtime.Autograd (Tape TapeM)
open PropertyKindCalculus (MathCarrier)
open PropertyKindCalculus.Paradigm (TapeBuilder)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)
open PropertyKindCalculus.Paradigm.TapeCodegen
open PropertyKindCalculus.Paradigm.Platform

/-! ## Recording scaffolding (the demo's pattern: leaves in, CSE'd tape out) -/

abbrev TB := TapeBuilder Shape.scalar

/-- A named input leaf (placeholder value `0`). -/
def inLeaf (nm : String) : TB := ⟨TapeM.leaf (fill (0.0 : Float) Shape.scalar) (name := some nm)⟩

/-- Record one output and hash-cons, exactly as the deployment recorders do. -/
def record1 (b : TB) : Except String (Tape Float) := do
  let (_, t) ← TapeM.run Tape.empty b.run
  pure (cseCompact t).1

/-- `maxLiveNodes` through the `Except`, with a poison value on a failed record. -/
def mlOf (r : Except String (Tape Float)) : Nat :=
  match r with
  | .ok t => maxLiveNodes t
  | .error _ => 1000000

/-! ## `maxLiveNodes` on hand-computed live-set structures

Walk convention: named inputs live from launch; a node allocates at its id; operands whose
last consumer is node `j` free after `j` executes; terminal nodes stay live to the end. -/

/-- Chain `exp (exp (exp x))`: at every step one operand + one result → peak 2. -/
def chain : Except String (Tape Float) :=
  record1 (MathCarrier.exp (MathCarrier.exp (MathCarrier.exp (inLeaf "x"))))

#guard mlOf chain == 2

/-- Diamond `(exp x) * (x + x)`: after CSE `x` feeds both arms, so the peak is
`{x, exp x, x+x}` while the second arm computes → 3. -/
def diamond : Except String (Tape Float) :=
  let x := inLeaf "x"
  record1 (MathCarrier.exp x * (x + x))

#guard mlOf diamond == 3

/-- Fan-in `(exp x + exp y) + (exp z + exp w)`: 4 inputs live from launch; the peak is
during the first arm — `{x..w}` + `exp x` (x not yet dead) → 5, and the tail never
exceeds it (the finished arm's sum keeps earlier buffers' places). -/
def fanIn : Except String (Tape Float) :=
  record1 ((MathCarrier.exp (inLeaf "x") + MathCarrier.exp (inLeaf "y"))
         + (MathCarrier.exp (inLeaf "z") + MathCarrier.exp (inLeaf "w")))

#guard mlOf fanIn == 5

/-- A const leaf allocates like any buffer (`BatchCarrier.const` materializes full-size):
`x * 2` peaks at `{x, const, mul}` → 3. -/
def withConst : Except String (Tape Float) :=
  record1 (inLeaf "x" * (TapeBuilder.const 2.0 : TB))

#guard mlOf withConst == 3

-- The empty tape has nothing live.
#guard maxLiveNodes (Tape.empty (α := Float)) == 0

/-! ## `AiReport` threading and the peak-bytes shapes -/

/-- The diamond's report at one output: `maxLive` rides along `aiReport`, and the three
shapes are the documented formulas — fused `(nIns+nOut)·P·4`, eager `maxLive·P·4`, host
`8·(nIns+nOut) + 4·maxLive` per pixel. -/
def diamondRep : AiReport :=
  match diamond with
  | .ok t => aiReport t 1
  | .error _ => aiReport (Tape.empty (α := Float)) 1

#guard diamondRep.maxLive == 3
#guard diamondRep.nInputs == 1
#guard diamondRep.fusedBytesPerElem == (1 + 1) * 4
#guard diamondRep.fusedPeakBytes 10 == (1 + 1) * 10 * 4
#guard diamondRep.eagerPeakBytes 10 == 3 * 10 * 4
#guard diamondRep.eagerHostBytesPerElem == 8 * (1 + 1) + 4 * 3

/-! ## Platform parsers on captured content -/

-- The parsers are kinded on BOTH sides (the ingest boundary): inputs are `NominalValue`
-- texts of per-format kinds, outputs kinded indications. The `⟨…⟩` literals below are
-- typed by each guard's left-hand side.
#guard parseCpuList ⟨"0-3,8,10-11"⟩ == ⟨7⟩
#guard parseCpuList ⟨"0-11"⟩ == ⟨12⟩
#guard parseCpuList ⟨"7"⟩ == ⟨1⟩
#guard parseCpuList ⟨""⟩ == ⟨0⟩

#guard parseCpusAllowed ⟨"Name:\tfit\nCpus_allowed:\t10f\nCpus_allowed_list:\t0-3,8\n"⟩
    == some ⟨5⟩
#guard parseCpusAllowed ⟨"Name:\tfit\n"⟩ == none

-- v2 unlimited and the v1 no-limit sentinel are "no limit", never a colossal budget
#guard parseLimitBytes ⟨"max\n"⟩ == none
#guard parseLimitBytes ⟨"30064771072\n"⟩ == some ⟨30064771072⟩
#guard parseLimitBytes ⟨"9223372036854771712\n"⟩ == none

#guard parseCpuMaxCores ⟨"150000 100000\n"⟩ == some ⟨2⟩   -- 1.5 cores rounds UP: it can burst
#guard parseCpuMaxCores ⟨"100000 100000\n"⟩ == some ⟨1⟩
#guard parseCpuMaxCores ⟨"max 100000\n"⟩ == none

-- The dump and the key are different NOMINAL kinds — `parseMemInfoBytes key dump`
-- (the classic swap) no longer type-checks.
#guard parseMemInfoBytes
  ⟨"MemTotal:       65486356 kB\nMemFree:         4200000 kB\nMemAvailable:   40316000 kB\n"⟩
  ⟨"MemAvailable"⟩ == some ⟨40316000 * 1024⟩
#guard parseMemInfoBytes ⟨"MemTotal: 1 kB\n"⟩ ⟨"MemAvailable"⟩ == none

-- Input dump and extracted path are different kinds of text; the expected answers are
-- `cgroupPathText` designations.
#guard parseCgroupV2Path ⟨"0::/kubepods/burstable/pod12\n"⟩ == some ⟨"/kubepods/burstable/pod12"⟩
#guard parseCgroupV2Path ⟨"12:memory:/docker/abc\n0::/\n"⟩ == some ⟨"/"⟩
#guard parseCgroupV2Path ⟨"12:memory:/docker/abc\n"⟩ == none

/-! ## The two solver shapes on hand-solved budgets -/

-- Worker shape: bytes(50) = 100 + 2·50 = 200; ⌊1000/200⌋ = 5 WORKERS (the
-- `workersOfHeadroom` law — each worker adds its own resident block).
#guard maxConcurrentWorkers { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ } ⟨50⟩ ⟨1000⟩
    == some ⟨5⟩
-- Not even one worker fits — the caller must shrink the block, not the count.
#guard maxConcurrentWorkers { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ } ⟨1000⟩ ⟨150⟩
    == some ⟨0⟩
-- A zero-cost shape cannot constrain.
#guard maxConcurrentWorkers { fixedBytes := ⟨0⟩, bytesPerElem := ⟨0.0⟩ } ⟨50⟩ ⟨1000⟩ == none

-- Single-launch shape: ⌊(1000 − 100)/2⌋ = 450 elements fit one resident batch.
#guard MemShape.maxElems { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ } ⟨1000⟩ == some ⟨450⟩
-- The fixed term (bound tables) alone exceeds the budget.
#guard MemShape.maxElems { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ } ⟨50⟩ == some ⟨0⟩
-- No per-element term: memory does not constrain the batch size.
#guard MemShape.maxElems { fixedBytes := ⟨100⟩, bytesPerElem := ⟨0.0⟩ } ⟨1000⟩ == none
-- Fractional per-element (a calibrated factor): ⌊900/2.5⌋ = 360, and bytesFor 360 = 1000 exactly.
#guard MemShape.maxElems { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.5⟩ } ⟨1000⟩ == some ⟨360⟩

-- Split shape: the variable term 2·400 = 800 is invariant in N; ⌊(1000−800)/100⌋ = 2
-- SHARDS (the `shardsOfHeadroom` law — the shards partition ONE resident total).
#guard maxShardsSplit { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ } ⟨400⟩ ⟨1000⟩ == some ⟨2⟩
-- The resident total alone overflows: NO count fits — row-chunk externally instead.
#guard maxShardsSplit { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ } ⟨600⟩ ⟨1000⟩ == some ⟨0⟩
-- No per-shard fixed term: memory does not constrain the count at all.
#guard maxShardsSplit { fixedBytes := ⟨0⟩, bytesPerElem := ⟨2.0⟩ } ⟨400⟩ ⟨1000⟩ == none

-- The same numbers through the two same-signature laws: equal magnitudes, DIFFERENT
-- kinds — `workerCount` vs `shardCount`. Comparing the two results directly would not
-- even type-check; that unwritable comparison is the point of the split vocabulary.
#guard (Quantity.div workersOfHeadroom (⟨1000⟩ : Quantity storageCapacity Nat) ⟨200⟩
    : Quantity workerCount Nat).magnitude
    == (Quantity.div shardsOfHeadroom (⟨1000⟩ : Quantity storageCapacity Nat) ⟨200⟩
    : Quantity shardCount Nat).magnitude

end PropertyKindCalculus.Tests.AutoScaling
