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

module

public import PropertyKindCalculus.Torch.Paradigm.TapeCodegen
meta import PropertyKindCalculus.Torch.Paradigm.TapeCodegen
public import PropertyKindCalculus.Torch.Paradigm.Platform
meta import PropertyKindCalculus.Torch.Paradigm.Platform

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.AutoScaling

open Spec TorchLean
open Runtime.Autograd (Tape TapeM)
open PropertyKindCalculus (MathCarrier)
open PropertyKindCalculus.Paradigm (TapeBuilder)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)
open PropertyKindCalculus.Paradigm.TapeCodegen
open PropertyKindCalculus.Paradigm.Platform

/-! ## Recording scaffolding (the demo's pattern: leaves in, CSE'd tape out) -/

abbrev TB := TapeBuilder Shape.scalar

/-- A named input leaf (placeholder value `0`). -/
def inLeaf (nm : String) : TB := ⟨TapeM.leaf (Tensor.full Shape.scalar (0.0 : Float)) (name := some nm)⟩

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

/-! ### The split shape whose slope changes at a slice threshold

`maxShardsSplitPiecewise`. The shapes below are the measured knee in caricature: past the
threshold ONE SHARD's slice is mapped directly and costs less per element; at and below it the
slice is served from retained arenas and costs more. Every cell is hand-solved, and the pair
that matters is the first two — the same threshold and the same pieces answer with the *cheap*
regime in one and the *expensive* one in the other, because which regime can be reached at all
depends on the per-shard fixed term. -/

-- The cheap regime wins. total = 400, threshold = 100 ⇒ the boundary is N = 4, so `above`
-- governs N ≤ 3 and `base` governs N ≥ 4. Above: ⌊(1000 − 1·400)/100⌋ = 6, clamped to its
-- regime = 3. Base: ⌊(1000 − 2·400)/100⌋ = 2, which is not in `N ≥ 4` and so is no answer at
-- all. Three shards — where the conservative single-piece solve would have said two.
#guard maxShardsSplitPiecewise { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ }
    { fixedBytes := ⟨100⟩, bytesPerElem := ⟨1.0⟩ } ⟨100.0⟩ ⟨400⟩ ⟨1000⟩ == some ⟨3⟩
#guard maxShardsSplit { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ } ⟨400⟩ ⟨1000⟩ == some ⟨2⟩

-- The expensive regime wins, with the SAME slopes and threshold: a per-shard overhead of 10
-- instead of 100 puts ⌊(1000 − 800)/10⌋ = 20 shards inside `N ≥ 4`, and 20 beats the 3 the
-- cheap regime is boxed into by its own boundary. The two answers are not a ranking of the
-- pieces — each piece is solved only where it is in force, and the better feasible count wins.
#guard maxShardsSplitPiecewise { fixedBytes := ⟨10⟩, bytesPerElem := ⟨2.0⟩ }
    { fixedBytes := ⟨10⟩, bytesPerElem := ⟨1.0⟩ } ⟨100.0⟩ ⟨400⟩ ⟨1000⟩ == some ⟨20⟩

-- **The base piece owns the boundary.** At N = 4 the slice is exactly 100 = the threshold, and
-- `above` is in force *strictly* past it — so however much room the cheap piece has (here
-- ⌊(1000 − 400)/1⌋ = 600), it is never credited with the boundary count itself.
#guard maxShardsSplitPiecewise { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ }
    { fixedBytes := ⟨1⟩, bytesPerElem := ⟨1.0⟩ } ⟨100.0⟩ ⟨400⟩ ⟨1000⟩ == some ⟨3⟩

-- Neither regime fits: both variable terms alone overflow the headroom (1.8·600 = 1080 and
-- 2·600 = 1200 against 1000). `some 0` — the same reading the single-piece solver gives, and
-- the same remedy: a smaller total, not a smaller count.
#guard maxShardsSplitPiecewise { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ }
    { fixedBytes := ⟨100⟩, bytesPerElem := ⟨1.8⟩ } ⟨100.0⟩ ⟨600⟩ ⟨1000⟩ == some ⟨0⟩

-- No per-shard fixed term in the regime that governs the large counts: the count is
-- unconstrained by memory, which is `none` and not a very large number.
#guard maxShardsSplitPiecewise { fixedBytes := ⟨0⟩, bytesPerElem := ⟨2.0⟩ }
    { fixedBytes := ⟨100⟩, bytesPerElem := ⟨1.0⟩ } ⟨100.0⟩ ⟨400⟩ ⟨1000⟩ == none

-- A threshold no slice can fail to exceed is not a piecewise question: one regime governs the
-- whole axis, and the answer is that piece's own single-piece solve.
#guard maxShardsSplitPiecewise { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ }
    { fixedBytes := ⟨100⟩, bytesPerElem := ⟨1.0⟩ } ⟨0.0⟩ ⟨400⟩ ⟨1000⟩
    == maxShardsSplit { fixedBytes := ⟨100⟩, bytesPerElem := ⟨1.0⟩ } ⟨400⟩ ⟨1000⟩

-- The sum a decision is solved against dispatches to the two solvers and answers the same
-- readings, so a caller that switches shapes does not have to re-learn what `none` means.
#guard (SplitShape.simple { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ }).memCap ⟨400⟩ ⟨1000⟩
    == some ⟨2⟩
#guard (SplitShape.piecewise { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ }
    { fixedBytes := ⟨100⟩, bytesPerElem := ⟨1.0⟩ } ⟨100.0⟩).memCap ⟨400⟩ ⟨1000⟩ == some ⟨3⟩

-- Which piece a decision RAN under, which is what its log line and its artifact have to say:
-- at 3 shards the slice is 133 and the cheap piece is in force; at 4 it is exactly the
-- threshold and the base piece owns it; a simple shape answers itself at every count.
#guard ((SplitShape.piecewise { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ }
    { fixedBytes := ⟨100⟩, bytesPerElem := ⟨1.0⟩ } ⟨100.0⟩).pieceAt ⟨400⟩ ⟨3⟩).bytesPerElem
    == ⟨1.0⟩
#guard ((SplitShape.piecewise { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ }
    { fixedBytes := ⟨100⟩, bytesPerElem := ⟨1.0⟩ } ⟨100.0⟩).pieceAt ⟨400⟩ ⟨4⟩).bytesPerElem
    == ⟨2.0⟩
#guard ((SplitShape.simple { fixedBytes := ⟨7⟩, bytesPerElem := ⟨2.0⟩ }).pieceAt
    ⟨400⟩ ⟨9⟩).fixedBytes == ⟨7⟩
-- The same boundary, as the name an account of the run carries: one rule, asked two ways.
#guard (SplitShape.piecewise { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ }
    { fixedBytes := ⟨100⟩, bytesPerElem := ⟨1.0⟩ } ⟨100.0⟩).aboveAt ⟨400⟩ ⟨3⟩ == true
#guard (SplitShape.piecewise { fixedBytes := ⟨100⟩, bytesPerElem := ⟨2.0⟩ }
    { fixedBytes := ⟨100⟩, bytesPerElem := ⟨1.0⟩ } ⟨100.0⟩).aboveAt ⟨400⟩ ⟨4⟩ == false
#guard (SplitShape.simple { fixedBytes := ⟨7⟩, bytesPerElem := ⟨2.0⟩ }).aboveAt ⟨400⟩ ⟨1⟩ == false

-- The slice is a quotient of two counts, and the two ways of reading that division answer
-- different questions at the same magnitudes: 400 elements over 4 shards is a slice of 100,
-- and 400 elements at a slice of 100 is 4 shards. Neither result can be handed to the other's
-- slot — `sliceElementCount` and `shardCount` are distinct kinds.
#guard (Quantity.div elementsOfSlice (⟨400⟩ : Quantity elementCount Nat) ⟨4⟩
    : Quantity sliceElementCount Nat) == ⟨100⟩
#guard (Quantity.div shardsOfSlice (⟨400⟩ : Quantity elementCount Nat) ⟨100⟩
    : Quantity shardCount Nat) == ⟨4⟩

-- The same numbers through the two same-signature laws: equal magnitudes, DIFFERENT
-- kinds — `workerCount` vs `shardCount`. Comparing the two results directly would not
-- even type-check; that unwritable comparison is the point of the split vocabulary.
#guard (Quantity.div workersOfHeadroom (⟨1000⟩ : Quantity storageCapacity Nat) ⟨200⟩
    : Quantity workerCount Nat).magnitude
    == (Quantity.div shardsOfHeadroom (⟨1000⟩ : Quantity storageCapacity Nat) ⟨200⟩
    : Quantity shardCount Nat).magnitude

/-! ## The integer ↔ real round-trip: the rounding DIRECTION is the claim -/

-- A demand rounds up, an allowance rounds down. Same magnitude in, different answers —
-- which is why each direction is a named definition rather than a lambda per call site.
#guard (⟨2.5⟩ : Quantity storageCapacity Float).ceilToNat == ⟨3⟩
#guard (⟨2.5⟩ : Quantity elementCount Float).floorToNat == ⟨2⟩
#guard (⟨7⟩ : Quantity storageCapacity Nat).asFloat == ⟨7.0⟩
-- Exact values are fixed points of both — the directions differ only where it matters.
#guard (⟨4.0⟩ : Quantity shardCount Float).ceilToNat == (⟨4.0⟩ : Quantity shardCount Float).floorToNat

/-! ## The decision line — both labels, one erasure -/

-- MiB display truncates and is `String`-valued: a rounded figure must not be able to
-- re-enter the arithmetic that decides whether a batch fits.
#guard showMiB ⟨30064771072⟩ == "28672 MiB"        -- the 28 GiB cgroup cap of the motivating case
#guard showMiB ⟨(1 <<< 20) - 1⟩ == "0 MiB"
#guard showMiB ⟨0⟩ == "0 MiB"

-- The whole line, both labels in their own slots: the emitter says who decided, the
-- budget's `source` says which limit was believed. Swapping them is a type error, not a
-- confusing log entry.
#guard ShardDecision.describe
    { nShards := ⟨4⟩, cores := { cores := ⟨16⟩ },
      budget := some { bytes := ⟨30064771072⟩, source := ⟨"cgroup-v2:/kubepods/burstable"⟩ },
      memCap := some ⟨4⟩, timeCap := none, overflow := false, overridden := false }
    ⟨"tile_retrieve"⟩
  == "[tile_retrieve] shards=4 (auto; cores=16, mem-cap 4, " ++
     "budget 28672 MiB [cgroup-v2:/kubepods/burstable])"

-- A supplied time model prints beside the memory cap rather than replacing it: the reader has
-- to be able to see WHICH cap bound, because "fits" and "worth having" have different repairs.
#guard ShardDecision.describe
    { nShards := ⟨8⟩, cores := { cores := ⟨56⟩ },
      budget := some { bytes := ⟨30064771072⟩, source := ⟨"cgroup-v2:/kubepods/burstable"⟩ },
      memCap := some ⟨2704⟩, timeCap := some ⟨8⟩, overflow := false, overridden := false }
    ⟨"avs_fit_linearized"⟩
  == "[avs_fit_linearized] shards=8 (auto; cores=56, mem-cap 2704, time-cap 8, " ++
     "budget 28672 MiB [cgroup-v2:/kubepods/burstable])"

/-! ## The time cap — `t(N) = W/N + a·N`, and the closed form that minimizes it

The strongest available check on a closed-form optimum is not a pinned number: it is that the
`N` it returns really does minimize the very function the module says it minimizes. So the probe
brute-forces `wallClock` over the whole shard ladder and compares. The closed form rounds to an
integer, so the test is that no integer `N` in range beats it — not that it equals the argmin of
a continuous relaxation, which is a different and weaker claim. -/

/-- The measured shape of the one algorithm on this host that needs the cap: `w ≈ 45 µs` per
element, `a ≈ 19 ms` per task. Seconds, which is the kind's stated unit. -/
def fitShape : TimeShape := { perElement := ⟨45.0e-6⟩, perShard := ⟨19.0e-3⟩ }

/-- Brute force: is there any shard count in `1..limit` with a strictly smaller modelled time? -/
def beatenBy (shape : TimeShape) (total : Quantity elementCount Nat)
    (n : Quantity shardCount Nat) (limit : Nat) : Bool :=
  (List.range limit).any fun i =>
    let m : Quantity shardCount Nat := ⟨i + 1⟩
    (shape.wallClock total m).magnitude < (shape.wallClock total n).magnitude

-- Across the block sizes production lands in, the closed form is never beaten on the ladder.
#guard [1600, 6400, 25600, 102400, 409600, 1638400].all fun p =>
  match fitShape.optimalShards ⟨p⟩ with
  | some n => !beatenBy fitShape ⟨p⟩ n 56
  | none => false

-- **The dense sweep, which is the probe that matters.** Six hand-picked sizes are exactly the
-- test that let a rounding error through: `t` is convex so the integer optimum is one of `N*`'s
-- neighbours, but the changeover is at the GEOMETRIC mean `√(n(n+1))`, not the arithmetic
-- `n + ½`, and a round-to-nearest implementation is wrong throughout the band between them —
-- about 0.9 % of the `N*` line, concentrated at small `n` where the band is widest. Sweeping
-- `W/a` continuously is what catches it, and a handful of sizes is what does not.
#guard
  let shape (i : Nat) : TimeShape :=
    -- `a = 1 s`, so `W` in seconds IS `N*²`: walks `N*` from ~1 to ~24 in 600 steps.
    { perElement := ⟨(1.0 + i.toFloat * 0.04) * (1.0 + i.toFloat * 0.04)⟩, perShard := ⟨1.0⟩ }
  (List.range 600).all fun i =>
    match (shape i).optimalShards ⟨1⟩ with
    | some n => !beatenBy (shape i) ⟨1⟩ n 40
    | none => false

-- **The equal-terms identity**, which is the derivation's own sanity check made executable: at
-- `N* = √(W/a)` the shared-work and per-shard terms are *equal*, each `√(Wa)`, so the minimum is
-- `t(N*) = 2√(Wa)`. Pinned at a shape where `W/a` is a perfect square, so `N*` is an exact integer
-- and rounding cannot blur the equality: `a = 1 s`, `W = 16 s` ⇒ `N* = 4`, both terms `4 s`,
-- `t = 8 s`. A measured optimum whose two terms are far from even is either not the optimum or
-- not this model.
#guard
  let s : TimeShape := { perElement := ⟨16.0⟩, perShard := ⟨1.0⟩ }
  let n := s.optimalShards ⟨1⟩
  n == some ⟨4⟩ && (s.wallClock ⟨1⟩ ⟨4⟩).magnitude == 8.0

-- The specific case round-to-nearest gets wrong, pinned so the repair cannot silently regress:
-- `N* = 1.45` rounds to 1, but two shards are genuinely faster (3.051 s against 3.103 s).
#guard
  let s : TimeShape := { perElement := ⟨1.45 * 1.45⟩, perShard := ⟨1.0⟩ }
  s.optimalShards ⟨1⟩ == some ⟨2⟩
  && (s.wallClock ⟨1⟩ ⟨2⟩).magnitude < (s.wallClock ⟨1⟩ ⟨1⟩).magnitude

-- The optimum moves as `√P` — it is not a roofline, whose corner would sit at a fixed size.
-- Sixteen times the elements, four times the shards, at a pair where the rounding is clean.
#guard match fitShape.optimalShards ⟨6400⟩, fitShape.optimalShards ⟨102400⟩ with
  | some a, some b => b.magnitude == 4 * a.magnitude
  | _, _ => false

-- The cost of ignoring it, at the block sizes production lands in: taking every core is a real
-- multiple of the optimum's wall clock, not a rounding. These are the *model's* ratios at the
-- shape recorded above (3.66× and 1.94×); the measurement that motivated the cap read 3.93× and
-- 2.20× on the algorithm itself, which is the same conclusion from the readings rather than from
-- the fit — and the reason this probe bounds rather than pins.
#guard
  let ratio (p : Nat) : Float :=
    match fitShape.optimalShards ⟨p⟩ with
    | some n => (fitShape.wallClock ⟨p⟩ ⟨56⟩).magnitude / (fitShape.wallClock ⟨p⟩ n).magnitude
    | none => 0.0
  ratio 25600 > 3.0 && ratio 102400 > 1.9

-- No measured per-shard cost ⇒ the model says more shards are always faster, so time does not
-- constrain the count. `none`, the same reading `maxShardsSplit` gives for memory.
#guard (({ perElement := ⟨45.0e-6⟩ } : TimeShape).optimalShards ⟨102400⟩).isNone
-- No work either way: nothing to optimize.
#guard (fitShape.optimalShards ⟨0⟩).isNone

-- The three algorithms whose per-task overhead is negligible against their work are not capped
-- into uselessness by a shared rule: with `a` a thousand times smaller, the optimum is past the
-- core count and the cores cap binds, exactly as it did before this term existed.
#guard match ({ perElement := ⟨45.0e-6⟩, perShard := ⟨19.0e-6⟩ } : TimeShape).optimalShards
    ⟨102400⟩ with
  | some n => n.magnitude > 56
  | none => false

end PropertyKindCalculus.Tests.AutoScaling

end Blanket
