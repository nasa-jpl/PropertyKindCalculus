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

## The through-line

The four strategies are one source. The single-threaded baseline runs anything and is the oracle; the
multi-threaded and both GPU strategies trade a structural demand on the model — independence and good
arithmetic intensity, and for the megakernel, register-fittability — for progressively more of the
hardware's peak. What licenses the automatic parallelization and fusion of the latter three is not a
heroic compiler analysis but the `NumCarrier` discipline itself: a model that typechecks against it is
_already_ branchless and fusible, so "go fast, automatically" is earned at authoring time by the same
type that made "write once, correctly" true. The performance is a corollary of the specification, not
a second, hand-written artifact that must be kept in step with it.
