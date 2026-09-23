import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References
-- This is a *methodology* chapter: it cross-references the proved spine nodes with `{uses …}`
-- (the labels resolve at blueprint-generation time, not Lean elaboration), and illustrates each
-- step with the public `PropertyKindCalculus.Examples.MiniWriteOnce` worked example by name only.
-- It re-declares nothing, so — unlike the node-bearing chapters — it does not import
-- `PropertyKindCalculus` or the examples; the worked example is checked in the `Examples` library.

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Write Once, Correctly" =>
%%%
tag := "write-once"
%%%

The chapters so far catalogue what PropertyKindCalculus _provides_. This one is about _method_:
the order in which an application author reaches for those pieces when specifying a real model,
and why the order is forced rather than a matter of taste. The running example is
`PropertyKindCalculus.Examples.MiniWriteOnce` — a small, self-contained soil-moisture retrieval in
the project's own `Examples` library — read here only to _infer the recipe_. It is a deliberately
simplified subset, keeping just the salient structure each step needs (a few kinds, a typed
constant table, a dedicated kind, one row of a Cholesky factor) and omitting the full retrieval.
Every line of it is a _checked fact_, built in the `Examples` library under CI, so the
illustrations below are machine-verified; PropertyKindCalculus supplies the four primitives named
below and the example composes them in this order.

The discipline has a slogan: _write once correctly, go fast
automatically_. A quantity is authored once, carrying its kind, over an abstract numeric carrier;
the kind layer is checked by the elaborator and then _erases_ — projected away by `.magnitude` —
to a bare floating-point kernel, bit for bit. Correctness lives in the types and is paid for at
compile time, while the number that runs is the same one a hand-written kernel would compute.
Getting the _authoring order_ right is what makes that erasure sound: each layer must be in place
before the one above it can type-check.

This carrier-parametric discipline is inherited from TorchLean
{Manual.citep george_torchlean_formalizing_neural_networks}[], where a tensor is generic over its
scalar carrier so that one network runs at `ℝ` for proof and at `Float` for execution — and the
executable carrier here is, in fact, a TorchLean tensor. PropertyKindCalculus lifts the discipline
up the metrology tower: the same numeric carrier is varied over a kind-typed scalar quantity, a
tensor-valued quantity, and — across the lawful-to-executable refinement — a numerically adequate
one; the same parametric-indexing idea then carries onto an additive uncertainty descriptor,
yielding an _uncertain_ quantity, and onto the measured object as a further type index, yielding an
object-indexed _individual_ quantity. What TorchLean provides for one carrier of one tensor,
PropertyKindCalculus provides for the whole tower of quantity notions.

# The four steps

:::group "write-once"
These four steps are the order in which a PropertyKindCalculus model is authored. Each rests on
the layer beneath it; each is shown with where the `MiniWriteOnce` worked example realizes it.
:::

## Step 1 — Start from the measurement principle: declare the kinds

:::definition "wo-kinds" (parent := "write-once")
Before any number, name _what each quantity is_ by the examination that produces it. A
{uses "def_kindOfProperty"}[kind-of-property] is the common defining aspect of mutually comparable
properties (Dybkær §6.19); two otherwise-comparable kinds are individuated by their
{uses "def_examination"}[examination principle] — the defining aspect of the procedure that
measures them, so that {uses "thm_examPrinciple_defining"}[a different principle forces a different
kind]. This is the layer a description logic partly has: it can record a class, but not the
operator algebra or the laws the later steps add.

In the example this is the catalogue of bare kinds — the radar `backscatter` $`\sigma^0`, the
optical `ndvi`, the surface `reflectivity`, and the Mironov dielectric fit-constant kinds — each
declared as a `def` of `KindOfProperty`, named by the instrument or principle that examines it.
That a different examination principle forces a different kind is itself checked there: monostatic
and bistatic `reflectivity` share name, scale, and dimension yet are distinct kinds. A kind is
_general_ (a type); _this pixel's_ backscatter is _individual_ (a term, `Quantity backscatter α`).
Fix the kinds first: everything above is indexed by them.
:::

## Step 2 — Pair each kind with its dimension

:::definition "wo-dimension" (parent := "write-once")
Give each kind its dimension, and let dimension do only what it can. The {uses "def_dim"}[dimension
map] is a forgetful functor — it keeps a kind's SI base-quantity exponents and discards the rest —
so it answers only the coarse question, _are these even commensurable?_ It
{uses "thm_dim_homomorphism"}[respects products], which is ordinary dimensional bookkeeping proved
as a law, but it _does not decide_ identity. This step matters precisely because the quantities
that carry the retrieval are almost all dimension one — a volume fraction, a reflectivity, an
index. Dimension equates them all; the kind layer keeps them apart. Pairing a kind with its
dimension here is what lets a later product be checked for dimensional consistency _and_ kind
consistency at once.

In the example, volumetric and gravimetric water content (`vwc`, `gwc`) are both dimension one yet
distinct kinds — a units library alone would silently accept one for the other, which is exactly
the failure this layer removes. (The literal `dim`-functor collapse is the Mathlib-backed dimension
layer, shown in the _Units_ and _Dimension_ chapters; here the point is made one level up, at the
kind.)
:::

## Step 3 — Build kind-differentiated quantities; gate the arithmetic

:::definition "wo-quantities" (parent := "write-once")
Now write the model's data and forward maps as records of typed quantities, and let the
{uses "def_kMul"}[interaction algebra] gate the arithmetic: a product is formed only where the
kinds sanction it (`KMul` for products, {uses "def_kDiv"}[`KDiv` for quotients]), so a wrong
pairing is a compile error, not a wrong number. Same-kind addition is the gate on `+`; products and
quotients change kind by the algebra. Authored over an abstract carrier `α`, the whole record
re-represents at the proof carrier (`ℝ`), the rounding spec (binary32), and the executable (`Float`)
by one map, preserving every kind.

The example's `MiniMironovCoeffs α` is the pattern: each Mironov-2009 fit constant is a field of its
own kind — a dry refractive index `ndA0 : Quantity refractiveIndexKind α`, a relaxation time
`taub0 : Quantity relaxTimeKind α`, a conductivity `sigbF0 : Quantity conductivityKind α` — so the
elaborator refuses to pass a relaxation time where a conductivity is expected, even though all three
erase to the same carrier. Its `MiniMironovCoeffs.map` re-represents the whole table at any carrier
(the constants moved from `Int` to executable `Float` by one map), each constant keeping its kind.
:::

## Step 4 — Differentiate shared kinds: dedicate, or index by field

:::definition "wo-dedication" (parent := "write-once")
Finally, decide what to do about quantities that share a kind. There are two cases, and they go on
_different axes_.

When two quantities _should_ be different kinds because their measurement target differs — same
quantity, different system or component — make them distinct with a {uses "def_dedicatedKind"}[
dedicated kind]: holding the {uses "def_component"}[component] (or system) apart
{uses "thm_dedicated_distinct_component"}[is enough to force distinct kinds], without inventing
identity strings. In the example the bound-water and free-water static permittivities
(`boundStaticPerm`, `freeStaticPerm`) are one relative-permittivity kind dedicated to two
components, hence provably distinct.

When the algebra _forces_ a genuinely shared kind, the leftover distinction is _positional_, not
metrological, and belongs on a second axis carried by _named record fields_ — not arrays. One row
of the Cholesky factor — the example's `CholRowQ α` — is row-homogeneous: three fields
`l20 l21 l22`, all `Quantity reflectivity α`, because $`A = L L^{\mathsf T}` makes every
$`L_{ik} L_{jk}` land at the same kind regardless of the column — a kind that separated them would
make the factorization's own row sums ill-typed. The remaining "which slot" distinction is held by
the distinct field names and checked off the kind axis by an erasure `rfl`: the theorem
`cholRowQ_magnitudes` proves the kinded row's `.magnitudes` are _definitionally_ the bare-`Float`
kernel's outputs, so a same-kind slot swap still type-checks but breaks parity. A `Fin 3`-indexed
array would push that positional bookkeeping onto the type and discard the named slots; the record
keeps both axes separable — kind by the elaborator, position by parity-to-reference.
:::

# The payoff

Authored in this order, the model is _one source_. The kinds make every operation in the forward
physics and the normal-equations solve a checked equation; the dimension layer certifies
commensurability without conflating dimension-one quantities; the interaction algebra gates the
arithmetic; and dedication plus named fields carry the distinctions the kind axis cannot. Then
`.magnitude` erases the whole overlay and the compiled kernel is the bare `Float` program — proved,
by a definitional `rfl` for every input, to be the same numbers. _Write once correctly, go fast
automatically._

The worked example is `PropertyKindCalculus.Examples.MiniWriteOnce`, build-gated by the project's
own CI, so every illustration above is a checked fact rather than a claim. The recipe scales to a
full retrieval: the same four steps, composed in the same order, carry a complete SMAP–NISAR
soil-moisture model — and because each step's facts are real declarations, a downstream
_verifiable ATBD_ can cite them by name with their proved-or-`sorry` status, keeping the document
and the code in lockstep. PropertyKindCalculus supplies the four primitives this chapter names; a
model composes them in this order.

# Go fast, automatically — the deployment spectrum

The four steps above are the _write once, correctly_ half of the slogan; this section is the _go
fast, automatically_ half. Once a model is authored once over an abstract carrier `[NumCarrier α]`,
the kind overlay erases to a bare arithmetic kernel that is the _same_ for every carrier — and the
_carrier the model is instantiated at_ then selects, on its own, an execution strategy. There is a
spectrum of them, from a portable single core to a compiled GPU megakernel, and moving along it is
_choosing a carrier, not rewriting the model_. That is the precise content of "automatically": the
performance engineering is a consequence of the instantiation, paid for once in the carrier
libraries rather than per model.

The spectrum has an honest dividing line. The first two strategies ask _nothing_ of the model's
structure — they run an arbitrary science model, including one whose control flow braids input/output
and computation in ways that defeat vectorization. The last two exploit a structural property the
`NumCarrier` capability _enforces_: because `NumCarrier` carries no ordering-to-`Bool`, a kernel over
it cannot take a data-dependent branch on its inputs — every conditional is re-expressed with the
branchless selectors `min`/`max`. "Typechecks against `NumCarrier`" therefore _means_ "one fused,
control-flow-free elementwise kernel", which is exactly the precondition that makes automatic
parallelization and fusion sound. Good throughput on the last two strategies additionally needs the
model to have favourable _arithmetic intensity_ — enough arithmetic per byte of input/output moved —
which is a property of the science, not of the calculus.

## CPU, single-threaded — the universal baseline and the oracle

Instantiate the model at the scalar executable carrier (`α := Float`). The kind overlay erases by
`.magnitude` to the bare floating-point program of Step 4's payoff; every intermediate lives in a
register, so the arithmetic intensity per work-item is maximal and the kernel is compute-bound on one
core. This strategy is unconditional: it runs _any_ science model, including those whose interleaving
of I/O and computation, data-dependent iteration, or irregular memory access makes efficient
parallelism genuinely hard — the cases where the later strategies do not apply. It is also the
_oracle_: because it is the same erased kernel, its per-pixel result is the reference the parallel and
GPU strategies are checked against, bit for bit. The cost is that it uses a single core.

## CPU, multi-threaded — coarse-grained task parallelism

Keep the scalar carrier and split the _row-independent_ (pixel) axis into contiguous slices, running
the whole kernel on each slice on its own dedicated Lean `Task`. The parallelism is Lean's own task
construct — no external threading library, no OpenMP shim — and it is _coarse-grained_: one task per
slice runs the entire op-chain, so the compute-per-fork is maximal and per-operation fork/join
overhead is nil. This is exact whenever the work-items are independent (which the per-pixel retrieval
is), and it scales toward the core count _when the model has good arithmetic intensity_ — enough
compute per work-item that the cores are kept busy rather than starved on memory bandwidth or throttled
by task overhead. A model with poor intensity, or one whose items are not independent, sees little
benefit here and is better served by the single-threaded baseline. This strategy is the deployment
layer's `runSharded`.

## GPU, eager — one pre-compiled kernel per operation

Instantiate the model at TorchLean's batched device carrier (`α := CudaT`). Each `NumCarrier`
operation on this carrier is a single pre-compiled CUDA kernel, launched by a foreign-function call,
that reads its operand buffers from device memory and writes one output buffer back. Running the
write-once source at this carrier therefore issues a _sequence_ of device kernel launches, one per
arithmetic operation of the model, and the GPU parallelizes _within_ each launch — one thread per
pixel per operation.

It is worth being exact about what is _not_ happening here, because it is a common confusion: this is
_not_ an intermediate representation being _interpreted on the GPU_, and no IR is involved at all.
The Lean-level operation sequence directly drives a sequence of hand-written device kernels through
the foreign-function boundary — eager, operation-at-a-time dispatch, the device analogue of running
the scalar kernel one statement at a time. There is no on-device program, no fused kernel, and nothing
that walks a graph at run time.

This strategy is _automatic_ in the strongest sense — the very same write-once source runs on the GPU
with no GPU code written — and it wins substantially when the pixel batch is large, because each launch
amortizes over the whole batch. Its ceiling is set by _memory bandwidth_: every intermediate of the
model is materialized as a full device buffer and round-tripped through DRAM, so the workload is
_memory-bound_ and its arithmetic intensity — arithmetic performed per byte moved — sits far below the
device's roofline (for the SMAP–NISAR AVS fit, an intensity of roughly 0.17 against an ideal near
13.75, an ~80× gap). The device spends its time moving buffers, not computing. This is the current
production GPU path.

## Fused forms — a targeted middle ground

Between dispatching every operation eagerly and compiling the whole model there is a targeted lever: a
_fused form_. On the eager carrier a single composed sub-expression of the model — say a two-way
attenuation `exp(c · x · y)` — is several kernel launches and as many DRAM round-trips, one per
operation. A fused form replaces that one recurring shape with a single kernel the carrier provides
directly, computing the composition in one pass with its intermediates in registers. Crucially the
fused form is a _refinement_ of the composition, not an approximation of it: it is required to be
bit-identical to the `NumCarrier` expression it stands in for — same operations, same association — so
substituting it changes only _how fast_ the shape is computed, never _what_ it computes. Where a carrier
offers no fused form for a shape, the model simply falls back to the plain composition; the write-once
source is unchanged either way.

This lever is _domain-neutral_ and _extensible_. The forms are named by their mathematical shape, not by
any application: the first is the scaled product exponential `exp(c · x · y)`, of which a soil-moisture
vegetation attenuation `exp(−2 · b · ndvi)` and a Beer–Lambert two-way extinction `exp(−2 · κ · ℓ)` are
instances — the domain reading lives downstream, in the science model that supplies the coefficient.
Further forms — an affine exponent `exp(a + c · x)` (Arrhenius, log-linear models), a Gaussian
`exp(−γ · x²)` (radial-basis kernels), a numerically-stable `logSumExp`, a reciprocal square root — drop
in the same way, each earned by a specific hot path rather than added speculatively.

A fused form is the _special case_ of the general fusion the next strategy performs. The megakernel
compiles the _whole_ model into one kernel; a fused form hand-collapses _one named shape_ within an
otherwise eager execution. It is the right tool when a single sub-expression dominates and the rest of
the model is content to run eagerly, or as the concrete kernel a compiled path targets for that shape.
The same discipline governs both: a fused form is trusted because it is a refinement of its composed
spec, exactly as the megakernel is trusted because it is proved faithful to the recorded model.

## Vocabulary extensions — tabulated data as a declared capability

A fused form refines a shape the base vocabulary can already _compose_. Some operations are not like
that: a look-up into tabulated data is a data-dependent gather, and the branchless carrier vocabulary
deliberately has no indexing to compose it from — the exclusion that makes every model above lower to
one straight-line kernel. When a model genuinely needs a table (a tabulated transfer function, a
calibration curve), the honest move is not to smuggle the gather in but to _declare_ it: a
vocabulary-_extension_ class whose single operation is piecewise-linear interpolation into a named,
layered, uniform-abscissa table. Unlike a fused form it has _no_ composed fallback — a model that uses
it says so in its type, so the dependence on tabulated data is visible exactly where the write-once
discipline wants it: in the instance context.

The extension keeps every leg of the discipline. Its reference semantics is one small function —
clamp, floor, linear interpolation, the uniform-grid analogue of the operational interpolator — which
is simultaneously the scalar oracle, the value a recording stores (recorder-faithful by construction),
and the meaning the interpreter assigns a recorded fetch. On the device it is realised by _texture
hardware_: the table lives in a layered texture bound once, fetched through the GPU's dedicated
texture cache — a table of tens of kilobytes is simply _resident_ there, so per-fetch traffic
effectively vanishes. One boundary must be stated rather than wished away: the texture unit's
hardware interpolation uses a low-precision fixed-point blend weight, so the _hardware-filtered_ mode
is a tolerance-bounded accelerator, never bit-reproducible; the _point-fetch_ mode — two exact texel
reads and an explicit, contraction-blocked lerp — is the bit-reproducible twin of the reference, and
it is the mode every bit-exact claim quantifies over. The split is fixed at generation time, not
discovered in production. Two further consequences come for free: the table's _name_ rides in the
recorded node, so common-subexpression elimination distinguishes fetches into different tables with no
change to its key; and because texture hardware interpolates only _uniform_ coordinates, an inverse
table over a non-uniform abscissa must first be inverted and resampled host-side — a one-time,
measured, controllable approximation that belongs to the model's accuracy budget, stated next to the
table's own discretization bias.

## GPU, megakernel-compiled — Lean → recorded IR → CUDA source

The remaining headroom is recovered by _compiling_ the model rather than dispatching it
operation-by-operation. Because the write-once kernel is branchless — the `NumCarrier` guarantee — the
same source, instantiated at a _recording_ carrier, does not compute a number: it _records_ its own
elementwise operation graph. That graph is common-subexpression-eliminated to its DAG of distinct
sub-expressions and emitted as a single fused CUDA `__global__` kernel: one thread per pixel, the
_whole_ model held in registers, with device memory touched only for the model's actual inputs and
outputs. This is a genuine _ahead-of-time compilation_ — from the Lean source, through a recorded
intermediate representation, to CUDA C source text — and, again, _not_ an interpreter: the generated
kernel is ordinary compiled CUDA, with no graph walked at run time.

The trade the previous strategy could not make is now available: with every intermediate kept in a
register instead of round-tripped to DRAM, the workload moves from memory-bound to _compute-bound_,
and its arithmetic intensity rises above the roofline knee — as close to the device's peak as the
science allows. The cost is a precondition: the model must have favourable AI properties — branchless
(guaranteed) and _register-fittable_, since the register pressure of the fused kernel bounds how much
of the model can be held live at once (a very large model is fused per-step and looped on the device,
rather than fused whole). This is why the strategy is _not_ universal in the way the single-threaded
baseline is: it buys the roofline in exchange for a structural demand on the model.

Two properties make this more than a code generator. First, it is _verified_: the recorded graph is
proved — sorry-free, over all inputs, by the tape's forward-value faithfulness — to compute exactly
the source kernel, so the generated kernel is faithful to the model _by a theorem_, not by a tested
diff. Second, it is _bit-controllable_: compiled with fused-multiply-add contraction disabled and no
re-association, the megakernel is bit-identical to the eager device path, because fusion changes only
_where an intermediate lives_ (a register versus DRAM), never the arithmetic performed — the speedup is
pure memory-traffic elimination, orthogonal to the numerics. (Enabling contraction trades that exact
identity for additional speed and a more-accurate-but-different result, a separate, quantified step.)

## Recording carriers are deferred — share loop-carried state or the graph explodes

The megakernel strategy carries one authoring hazard worth stating on its own, because it is a
property of the _recording carrier_ rather than of any model. That carrier is _deferred_: a recorded
value is a thunk that re-emits its sub-graph on every reference, not a memoized handle to an
already-emitted node. Reusing an intermediate therefore records it _again_ — and an iterated
computation reuses its loop-carried state on every step. A fixed-point sweep whose accumulator appears
$`k` times in the body, composed to depth $`d`, records on the order of $`k^{d}` copies of the first
step _before_ common-subexpression elimination can collapse them. CSE dedups the _result_, but the
recorder must first _build_ that intermediate, so a deep, reuse-heavy fold can exhaust memory at
elaboration time even though the final DAG — and every carrier's actual arithmetic — is small.

The discipline is the recording-time analogue of the megakernel's own _fuse one step, loop the device_
shape: record _one_ step and _materialize_ the loop-carried state to a single node between steps, so the
next step references it as one shared leaf instead of re-recording the entire prior step. Materialization
is semantics-preserving — the shared node computes the same value — so the recording stays bit-for-bit the
same kernel; only its _cost of being recorded_ changes, from exponential to linear in the step count. This
is invisible at the scalar, threaded, and eager-GPU carriers, where a value is just a number or a buffer
and reuse is free; it surfaces only when the same write-once source is run at the deferred recording
carrier, and it is a general hazard for _any_ science model with an unrolled iteration recorded that way —
not a quirk of one retrieval. It was found and fixed in exactly that setting: an eight-sweep loss-coupling
fixed point in the SMAP–NISAR closed-form Stage-3 retrieval, its accumulator reused several times per
sweep, unrolled past a hundred gigabytes at elaboration until the fold was threaded to share its
accumulator per sweep — after which the same recording completed in seconds, the generated kernel
unchanged.

## Right-sizing the deployment — the memory shape is computed, the platform is asked

Choosing a strategy is only half of a deployment decision; the other half is a _number_ — how many
task-shards the multi-threaded strategy forks, or how many pixels a device batch carries. Both are
bounded by memory before they are bounded by compute: the eager device carrier materializes a full
buffer per live intermediate, and the sharded CPU path holds every concurrent slice at once. And the
bound is a property of _this model on this machine_, so a hand-set constant is wrong somewhere —
cores idle on the large host, or an out-of-memory kill on the confined worker. The calculus
therefore treats sizing the way it treats everything else in this chapter: the model's memory shape
is _computed_, from the same recording that already proves faithfulness and computes arithmetic
intensity; the platform is _asked_ what it will actually grant; and a small solver combines the two —
with an explicit operator override that wins verbatim when someone knows better.

The model half is computed, not cited — the same standard the intensity accounting set. Memory use
is affine in the pixel count for every strategy, `bytes(P) = fixed + perElement · P`, and the
per-element term falls out of the recorded DAG per strategy. For the fused megakernel it is exact:
inputs plus outputs, four bytes each — every intermediate is a register — with a bound table charged
once per launch. For the eager carrier it is the _peak count of simultaneously-live buffers_ when
the DAG is evaluated in tape order, each buffer freed after its last consumer: one pass recovers
every node's last use, one walk takes the running peak (`maxLiveNodes`, reported beside the
intensity numbers by the same `aiReport`), and the sharded CPU path adds its host marshaling columns
on top. One honesty clause belongs here: the eager number is a _lower bound_, because "freed
promptly after its last consumer" is what a garbage-collected finalizer approaches rather than
guarantees, and a driver that loops a recorded step holds its carry across iterations. So the static
shape is the _prior_ — what makes a freshly authored model safely sizable before it has ever run —
and a measured probe of a real block (allocator peak on the device, child peak memory on the host)
is the _authority_ that calibrates it.

The platform half is asked with its provenance kept, because the budget that matters is the one
enforcement reads. A confined process is killed at its cgroup limit, not at the host's advertised
available memory — a container capped at 28 GiB on a host reporting 62 GiB is the observed norm on
shared worker queues — so the budget query asks cgroup v2 first (the process's own cgroup, minimum
over its ancestors), falls back to cgroup v1, and only then to the host's own figure, every answer
labeled with its source so the log records _which limit the sizing believed_. Core counts get the
same discipline: the scheduler's affinity mask intersected with the cgroup CPU quota, never the raw
host core count. On the device the query is the CUDA free-memory figure, taken _after_ the carrier's
warm-up — the context's fixed tax is then already netted out of it, which is one fixed overhead
nobody has to specify.

Two solver shapes close the loop, because the two knobs constrain differently. Task-sharding
partitions _one resident tile_ among concurrent shards, so the variable term is invariant in the
shard count and only a per-shard fixed cost scales with it — and when the resident term _alone_
exceeds the budget, no shard count fits, and the solver says exactly that (shrink the tile, not the
count) instead of clamping to a plausible-looking answer. Block-concurrency — a fixed block size,
choosing how many run at once — divides the remaining headroom by the per-worker cost. Either way
the decision is announced on one line with every term and its source, so an out-of-memory kill or an
inexplicably idle machine is diagnosable from the log alone; and the validation suite pins the
peak-residency walk on hand-computed live-set structures and the capacity parsers on captured
platform records, so the shapes are checked facts under the same CI as the parity theorems.

## The through-line

The four strategies are one source. The single-threaded baseline runs anything and is the oracle; the
multi-threaded and both GPU strategies trade a structural demand on the model — independence and good
arithmetic intensity, and for the megakernel, register-fittability — for progressively more of the
hardware's peak. What licenses the automatic parallelization and fusion of the latter three is not a
heroic compiler analysis but the `NumCarrier` discipline itself: a model that typechecks against it is
_already_ branchless and fusible, so "go fast, automatically" is earned at authoring time by the same
type that made "write once, correctly" true. The performance is a corollary of the specification, not
a second, hand-written artifact that must be kept in step with it. And the deployment's _size_ is
earned the same way: the recording that licenses fusion also yields the model's memory shape, so how
much of the spectrum a given machine can sustain is computed from the same single source — asked of
the platform at run time, never tuned into the model.
