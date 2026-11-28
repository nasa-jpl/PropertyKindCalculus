import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References
-- The layer-by-layer figure: the `svg_figure` directive and the figure it inlines.
import PropertyKindCalculusBlueprint.Figures
-- The four nodes below link declarations in the executable-binary32 rung, the tape library, the
-- composed pipeline theorem (which lives in the `Examples` library), and TorchLean's own kernel
-- compiler, so this chapter imports each of them.
import PropertyKindCalculus.Torch.Fp32
import PropertyKindCalculus.Torch.Paradigm.TapeHom
import PropertyKindCalculus.Examples.TapeEndToEndChain
import PropertyKindCalculus.Examples.TapeSharedCse
import TorchLean.CUDA.Kernel.Emit.Source

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PropertyKindCalculusBlueprint

#doc (Manual) "Metrology on a Verified Numerical Framework" =>
%%%
tag := "verified-framework"
%%%

PropertyKindCalculus does no arithmetic of its own. A kinded quantity erases to a magnitude, and
the magnitude is computed by a numerical framework: TorchLean
{Manual.citep george_torchlean_formalizing_neural_networks}[], whose tensors are generic over
their scalar, whose floating-point formats are specified in Lean (in its FloatLib dependency), and whose CUDA kernels are
generated from Lean source. {ref "write-once"}[Write Once, Correctly] states the discipline a
model is written in, and {ref "capstones"}[the capstone chapter] proves what that discipline
buys. This chapter states what the discipline _demands_ of the framework underneath it, and what
the calculus gives back, in two directions:

- *to metrology*, a computation that can be accelerated without losing its metrological meaning:
  the kinds, the declared sources and the listed constants of a model are theorems about the
  program that runs, at every carrier, not only about the source it was written in;
- *to verified numerical frameworks*, a consumer whose correctness criterion is bit-for-bit
  agreement across devices, and a set of results that belong to any framework of that kind.

In plain engineering terms: a unit-and-kind checker usually stops at the source code, and the
fast version of a model is a second artifact that has to be trusted to match it. Here the fast
version is derived from the source, and the derivation carries a proof.

# Six demands on the framework

Each demand follows from the write-once discipline. None of them is particular to one model.

:::table +header
*
  * Demand
  * Why the calculus needs it
  * What carries it
*
  * One source, many carriers
  * A model is authored once over `[NumCarrier α]` and instantiated along the {tech}[carrier ladder]: `ℝ` for proof, binary32 as the rounding specification, the executable binary32, `Float`, an eager device carrier, and the {tech}[recording carrier]. Each rung asks the framework for a different thing: proved derivatives at `ℝ`, executable floating-point facts at binary32, the whole operation set on device buffers, and a recorder.
  * TorchLean's scalar-generic `Context` and `MathFunctions`, which PropertyKindCalculus's `MathCarrier` mirrors field for field; the forwarding instances in `PropertyKindCalculus.Torch.Paradigm.NumCarrierContext`
*
  * A bit-exact oracle on every machine
  * The single-threaded `Float` run is the reference every other carrier is checked against. The acceptance rule is stated per check: bit for bit where both sides are IEEE-exact at one precision (the table fetch, where a NaN matches any NaN; an emitted kernel's outputs whose cone reaches no `exp` or `log`); within an ulp bound where a library `exp` or `log` is reached (four ulps by default in `julia_parity`); within a relative tolerance on every output for the KernelAbstractions twin of an emitted kernel (`1e-9` by default); and within a stated tolerance (`1e-3`) where a binary32 batched run is compared with the binary64 reference. That check has to run where there is no GPU (continuous integration, a CPU-only deployment), and a disagreement between devices is a defect to find, not noise to tolerate.
  * The LibTorch bridge running on the host through ATen's CPU kernels; the parity executables `ssprc_batched_parity`, `mcm_batched_parity` and `lut_cudat_parity`
*
  * Proofs whose cost does not grow with the model
  * A science model has hundreds of operations. A parity proof written per operation per model would not be written at all.
  * The {tech}[denotation bridge], preserved by each carrier operation once, bundled as a homomorphism and closed per model by the `tape_hom` tactic, whose residual is the list of the model's own definitions to unfold; the {tech}[kind-transporting weak bisimulation], whose acceptance is decided, not proved, per model
*
  * A recording that costs what the model costs
  * The megakernel path records the _whole_ model, so a recorder whose cost grows faster than the number of operations makes the path unusable on exactly the models that need it.
  * TorchLean's `Tape.record`, which pushes each node in place; the {tech}[compacted tape], which merges identical sub-expressions without moving a value; the sharing recorder `SharedTapeBuilder`, which records the compacted tape directly and never holds the expression tree, with `shares_record` proving it is the compaction of the unshared recording
*
  * Arithmetic intensity
  * Eager device execution round-trips every intermediate through device memory, so it is memory-bound. Fusion into one kernel keeps intermediates in registers. Tabulated data enters as a declared vocabulary extension whose device form is one kernel too.
  * The straight-line program read off a tape and printed as CUDA, C or Julia; TorchLean's certified kernel compiler for the table fetch
*
  * Metrological meaning survives the acceleration
  * A fused kernel carries no kinds. If its inputs, constants and kind changes cannot be tied back to the source's, the speed is bought with the provenance.
  * The {tech}[kind-transporting weak bisimulation] between the {tech}[metrological provenance hypergraph] and the {tech}[computational tape graph], and the {tech}[seal of the computation] over it
:::

The last demand is the one a metrologist asks about first, and the one no other demand settles.
The relation it rests on is a weak bisimulation, which is stronger than a refinement: a
refinement would say that every computation step corresponds to a step the source allows, and
the bisimulation says that, in both directions. Every occurrence the hypergraph states is
realized on the tape, and every tape path projects to a hypergraph path. It is _weak_ because
it says nothing about the inside of one operation's expansion on the carrier, which is where
the kinds are erased anyway.

# The trust chain, link by link

From a kinded source to bits on a device, each link is either a theorem or a named trusted base.
Every theorem cited here depends on `propext`, `Classical.choice` and `Quot.sound` only;
`Match.isBisimulation_contracted` depends on `propext` and `Quot.sound`.

:::table +header
*
  * Link
  * Carried by
  * Trusted
*
  * Kinded source to the erased kernel
  * `@[simp]` erasure lemmas proved by `rfl` (`Quantity.add_magnitude`, …): the naked kernel _is_ the kinded one with `.magnitude` applied
  * nothing
*
  * Erased kernel to the binary32 rungs
  * `Quantity.add_refines` at the rounding specification, unconditionally; `Quantity.add_refines_exec` at the executable binary32, under the explicit hypothesis that the sum is finite
  * nothing; overflow is a hypothesis, not an assumption
*
  * Kernel to its tape
  * the {tech}[denotation bridge] (`TapeParity.Evaluates`) and its homomorphism `Evaluates.isNumCarrierHom`, from TorchLean's per-operator `Tape.apply` correctness
  * nothing
*
  * Tape to compacted tape to printed program
  * `pipeline_denotes`: at every environment, the program printed from the compacted tape holds at the remapped slot of every original node the value the original tape computes there; `SL.genSL_denotes` for the program alone, table fetches included
  * nothing, up to the program; the printer's dozen forms meaning in the host language what they mean in Lean's `Float`
*
  * Tape graph to provenance hypergraph
  * `Match.isWeakBisimulation_weak`, and `Match.isBisimulation_contracted` on the {tech}[contracted tape graph]; the {tech}[seal of the computation] (`TapeSeal.semantic_seal`), carried to the printed program by `semantic_seal_program`
  * the harvest's reading of the source, which the bisimulation cross-checks rather than trusts
*
  * Printed program to device
  * for a table fetch, TorchLean's `CUDA.denotes_emit`: the generated CUDA source denotes the kernel expression `Program.of` certified against its Lean source
  * the host compiler with contraction and reassociation disabled; the host's IEEE conformance; `exp` and `log` from glibc, libdevice or Julia's `Base.Math`, checked by the parity executables to an ulp bound
:::

:::group "verified_framework"
The links of the trust chain that the capstone chapter does not already carry as nodes.
:::

:::theorem "vf_thm_exec_refinement" (parent := "verified_framework") (lean := "PropertyKindCalculus.Quantity.add_refines_exec") (tags := "proved") (effort := "small")
*The executable binary32 rung, with overflow stated.* For kind-`k` quantities carried at
the executable binary32 (FloatLib's `ExecFloat.Binary 8 23`, on which TorchLean builds), if the executable sum is finite, forgetting it to `ℝ` gives the
binary32 rounding of the real sum. Where the hypothesis fails (an overflow to infinity, a NaN
operand) the theorem claims nothing: it proves the equality on the finite path, not its failure off
it, and the hypothesis marks that boundary.
:::

:::proof "vf_thm_exec_refinement"
FloatLib's `ExecFloat.Binary.toReal_add_eq_roundAt`, transported along the kind index: the kinded sum is the
naked sum under `Quantity.mk`.
:::

:::theorem "vf_thm_hom" (parent := "verified_framework") (lean := "PropertyKindCalculus.Paradigm.TapeParity.Evaluates.isNumCarrierHom") (tags := "proved") (effort := "small")
*The denotation bridge is a homomorphism.* The bridge relates both leaf formers and each of `+`,
`−`, `×`, `÷`, `min`, `max`, `sqrt` and `exp` on the recording carrier to the matching
elementwise operation on tensors, bundled as one record. The `tape_hom` tactic closes a model's
parity by unfolding the model's own definitions and walking the exposed operation tree with
these cases.
:::

:::proof "vf_thm_hom"
Each field is one of the per-operation preservation lemmas of the denotation bridge, which are
proved from the tape's forward-value faithfulness lemmas through a run bridge.
:::

:::theorem "vf_thm_pipeline" (parent := "verified_framework") (lean := "PropertyKindCalculus.Examples.TapeEndToEndChain.pipeline_denotes") (tags := "proved") (effort := "medium")
*Tape, compacted tape and program agree.* For every well-formed tape without table fetches, if
the straight-line program is produced from its compacted form, then at every environment the
program holds, at the remapped slot of every original node, exactly the value the original tape
computes there. Constant leaves merged by compaction are covered, through the injectivity of
`Float.toBits`.
:::

:::proof "vf_thm_pipeline"
The compaction's denotation theorem, `cseCompact_denotation_unconditional`, composed with the
program's denotation theorem for table-free tapes; the program's existence supplies the
compacted tape's evaluation.
:::

:::theorem "vf_thm_shared_record" (parent := "verified_framework") (lean := "PropertyKindCalculus.Examples.TapeSharedCse.shares_record") (tags := "proved") (effort := "medium")
*The sharing recorder records the compacted tape.* A carrier-generic model names a shared
sub-expression once per use, so the recording carrier emits the expression tree and compaction
shares it afterwards; the tree can be orders of magnitude larger than the model. The sharing
recorder looks each node up by `cseCompact`'s key before appending it. For outputs related
operation by operation at the two carriers and recorded from the empty tape at one tensor shape,
both recordings fail, or the sharing tape has the name, the operands and the stored value of
every node of the compacted unshared tape, in the same order, and its output ids are the
remapped ids. Such a tape holds each key once (`keys_distinct_of_fwd`). That is the statement
for the unguarded entry `recordRaw`. The entry models use, `record`, also rejects a recording in
which one input name holds two different tensors, which the unshared recorder accepts; for it
the statement is one-sided (`shares_record_guarded`): when `record` succeeds, the unshared
recording succeeds and the same agreement holds.
:::

:::proof "vf_thm_shared_record"
A simulation between the sharing state and `cseCompact`'s fold over the unshared tape, one node
at a time (`Rel.step`), and a lemma that each elementwise recorder reads only its operands'
values (`raw_natural`), which makes the lookup before running sound. The relation `Shares` is
preserved by leaves, constants, `+ - * /`, `min`, `max`, `fmin`, `fmax`, `exp`, `log`, `abs`,
`sqrt` and the table fetch; the tactic `tape_shares` closes it for a concrete model.
:::

:::theorem "vf_thm_kernel_denotes" (parent := "verified_framework") (lean := "TorchLean.CUDA.denotes_emit") (tags := "proved") (effort := "medium")
*The framework's own link.* TorchLean's CUDA emitter: if emission of a kernel expression
succeeds, the generated source denotes the expression for any arithmetic and for buffer
contents read through bounds-checked loads. `Program.of` pairs each expression with a proof that
it agrees with the Lean function it was recognized from. Compilation, memory and execution
are outside the statement.
:::

:::proof "vf_thm_kernel_denotes"
A theorem of TorchLean, linked here because the table fetch's device kernel rests on it.
:::

# What the framework gained

The demands above were met partly by TorchLean as it stands and partly by changes contributed to
it. The ledger has one row per topic and lists every pull request this work opened on
`lean-dojo/TorchLean` for that topic, each with its state on 2026-11-27. _Merged_ means merged
into TorchLean's `main`. _Open_ means under review upstream: the calculus reaches an open
contribution through the `combined` branch of this work's fork, which is TorchLean's `main` with
the open branches merged on top, and which the calculus pins. _Closed_ means closed without a
merge, and the row says why and which pull request, if any, took the topic up again.

:::table +header
*
  * Topic
  * Pull requests and their state
  * Demand it serves
*
  * Exact matrix factorizations (Cholesky and QR)
  * [#1](https://github.com/lean-dojo/TorchLean/pull/1) closed by its author, who split it; [#2](https://github.com/lean-dojo/TorchLean/pull/2), its domain-independent exact part, merged
  * One source, many carriers
*
  * Differentiable `exp`, `log` and scalar-affine maps
  * [#5](https://github.com/lean-dojo/TorchLean/pull/5) merged
  * One source, many carriers
*
  * Elementwise division on the tape
  * [#7](https://github.com/lean-dojo/TorchLean/pull/7), the CPU node, merged; [#26](https://github.com/lean-dojo/TorchLean/pull/26), the proof-side node with its Fréchet derivative, merged
  * One source, many carriers
*
  * An asserted leak bound for long eager loops
  * [#8](https://github.com/lean-dojo/TorchLean/pull/8) closed; [#15](https://github.com/lean-dojo/TorchLean/pull/15), which proposed it again, closed: the maintainers' stress suite covers the need
  * A recording that costs what the model costs; met by the maintainers' own work
*
  * Release of device temporaries
  * [#9](https://github.com/lean-dojo/TorchLean/pull/9) closed: the trainer came to release tape temporaries itself; [#22](https://github.com/lean-dojo/TorchLean/pull/22), the scoped arena proposed again, closed when TorchLean moved to LibTorch and removed the backend it changed
  * A recording that costs what the model costs; met by the maintainers' own work
*
  * A bounded device block cache
  * [#10](https://github.com/lean-dojo/TorchLean/pull/10) merged
  * A recording that costs what the model costs
*
  * Sterbenz's lemma for formats with an underflow floor
  * [#16](https://github.com/lean-dojo/TorchLean/pull/16) closed; the maintainers reported taking its content into `main` in an upgrade, and the theory has since moved to FloatLib
  * Numerical adequacy; FloatLib now proves it
*
  * An executable unit in the last place and an absorption test
  * [#17](https://github.com/lean-dojo/TorchLean/pull/17) closed; the maintainers reported taking its content into `main` in an upgrade, and the theory has since moved to FloatLib
  * Numerical adequacy; TorchLean carries the absorption test and the calculus defines the executable ULP
*
  * A glibc link failure in CUDA builds
  * [#18](https://github.com/lean-dojo/TorchLean/pull/18) closed: the maintainers removed the call that caused it
  * Met by the maintainers' own work
*
  * The fused scaled product exponential `exp((c·x)·y)`, bit-identical to its four-operation form
  * [#23](https://github.com/lean-dojo/TorchLean/pull/23) merged
  * Arithmetic intensity
*
  * A piecewise-linear table lookup on the device
  * [#24](https://github.com/lean-dojo/TorchLean/pull/24), on CUDA textures, closed when TorchLean moved to LibTorch; [#34](https://github.com/lean-dojo/TorchLean/pull/34), the same function composed from LibTorch primitives as a tape node, closed when `main` replaced the interfaces it targeted; [#53](https://github.com/lean-dojo/TorchLean/pull/53), the lookup and its pullback on device buffers with its positions held on the device, open
  * One source, many carriers
*
  * The runtime link connected to the Fréchet-derivative model
  * [#25](https://github.com/lean-dojo/TorchLean/pull/25) merged
  * One source, many carriers
*
  * The choice of CUDA target architecture
  * [#27](https://github.com/lean-dojo/TorchLean/pull/27) closed: the maintainers added their own selection
  * Met by the maintainers' own work
*
  * Unboxed, concurrent `.npy` decoding
  * [#29](https://github.com/lean-dojo/TorchLean/pull/29) merged
  * A recording that costs what the model costs
*
  * The identity of a CUDA device
  * [#30](https://github.com/lean-dojo/TorchLean/pull/30), on the custom CUDA backend, closed when TorchLean moved to LibTorch; [#35](https://github.com/lean-dojo/TorchLean/pull/35), its LibTorch follow-up, closed when `main` replaced the interfaces it targeted; [#45](https://github.com/lean-dojo/TorchLean/pull/45), which reimplements it, open
  * A bit-exact oracle on every machine
*
  * The `TapeM` surface reduced to one lemma
  * [#31](https://github.com/lean-dojo/TorchLean/pull/31) merged
  * One source, many carriers
*
  * The LibTorch bridge on the host
  * [#36](https://github.com/lean-dojo/TorchLean/pull/36) closed when `main` replaced the interfaces it targeted; [#43](https://github.com/lean-dojo/TorchLean/pull/43), which reimplements it, open
  * A bit-exact oracle on every machine
*
  * Conversions between scalars and indices in a certified kernel
  * [#44](https://github.com/lean-dojo/TorchLean/pull/44) open, answering [issue #42](https://github.com/lean-dojo/TorchLean/issues/42)
  * Arithmetic intensity
*
  * A conditional directly in an `else` branch certified
  * [#46](https://github.com/lean-dojo/TorchLean/pull/46) open
  * Arithmetic intensity
*
  * Binary64 arithmetic on binary32 buffers
  * [#47](https://github.com/lean-dojo/TorchLean/pull/47) open
  * Arithmetic intensity
*
  * NaN-ignoring `fmin` and `fmax` on device buffers, with the same bits on both devices
  * [#50](https://github.com/lean-dojo/TorchLean/pull/50) open
  * A bit-exact oracle on every machine
*
  * A tape node recorded in linear time
  * [#51](https://github.com/lean-dojo/TorchLean/pull/51) open
  * A recording that costs what the model costs
*
  * Power, the ordered comparisons and selection on device buffers
  * [#52](https://github.com/lean-dojo/TorchLean/pull/52) open
  * One source, many carriers
*
  * The power `x ^ y` with the exponent a value: a recorded tape node with both operands as parents, so the exponent receives a gradient
  * [#54](https://github.com/lean-dojo/TorchLean/pull/54) open
  * One source, many carriers; available at the pinned revision
:::

The ledger holds 33 pull requests under 24 topics: nine merged, ten open, and fourteen closed.

Two contributions on the floating-point side stand closed unmerged, the theory they extended
having moved to FloatLib: Sterbenz's lemma for formats with an underflow floor
([#16](https://github.com/lean-dojo/TorchLean/pull/16)), which FloatLib now proves, and an
executable unit in the last place with an absorption test
([#17](https://github.com/lean-dojo/TorchLean/pull/17)), whose absorption test TorchLean carries
and whose executable ULP the calculus defines itself, in its numerical-adequacy layer.

Four further needs were met by TorchLean's maintainers in their own way, and the corresponding
contributions stand closed in favor of that work: an asserted leak bound for long eager loops
([#8](https://github.com/lean-dojo/TorchLean/pull/8),
[#15](https://github.com/lean-dojo/TorchLean/pull/15)), release of tape temporaries
([#9](https://github.com/lean-dojo/TorchLean/pull/9)), a glibc link failure in CUDA builds
([#18](https://github.com/lean-dojo/TorchLean/pull/18)), and the choice of CUDA target
architecture ([#27](https://github.com/lean-dojo/TorchLean/pull/27)). That independent
convergence is the plainest evidence that these needs are the framework's, not one model's.

Three of the contributions follow from the table fetch alone, and they show how a metrological
choice becomes a framework capability. A lookup is a data-dependent read, so the kernel language
needs an index computed from a coordinate (`⌊u⌋`) and the weight computed back from the index
(`u − ⌊u⌋`): #44. Linear interpolation in binary32 has no formula free of all three of overflow,
an inexact flat segment and cancellation, so the kernel computes in binary64 on binary32 buffers
and rounds once: #47. The device program then mirrors the host reference's chain of
conditionals instead of nesting every conditional in a `then` branch: #46.

Requiring the CPU and device runs to agree bit for bit makes them a differential test of the
framework and of the libraries under it, and the test found three defects there. ATen's CPU
`log1p` returns `0` at the least subnormal of binary32 and of binary64. ATen's CPU `fmax`
returns the first of a pair of zeros where CUDA orders them. `__float2ull_rz` of a NaN is not
`0` on an SM 8.6 device. The first is repaired in #43, the second avoided in #50, and the third
guarded in #44's emitted code.

# What the calculus built on the framework

The library `PropertyKindCalculus.Torch` is where the calculus meets TorchLean. Part of it is
metrology, and part of it is framework machinery that any consumer of a TorchLean tape could
use.

{figref "torchlean-extension"}[] sets the two side by side, layer by layer. The layers fall into
two classes.

Two layers have no counterpart in TorchLean. _Meaning_: a TorchLean tensor holds numbers, and
the kinds, the provenance hypergraph and the seal are the calculus's own. _Performance_: the
arithmetic intensity of a recorded model, the peak residency of its live intermediates under
each strategy, and the parallelism a confined platform can sustain are computed by the calculus
from the same recording that carries the faithfulness proofs. A search of TorchLean's source on
the pinned revision for intensity, roofline, residency, liveness and platform-capacity terms
finds nothing; that is a measurement of the source text, and it is stated as one.

The performance layer reaches the CPU as well as the GPU. Because a model is branch-free and
its pixels independent, the whole model runs on contiguous slices of a tile in parallel. The
number of slices is the largest that pays off: no more than the cores can run or free memory can
hold, and, where a program's per-task cost has been measured, no more than the count that
minimizes its modeled run time, past which each extra slice costs more to start than it saves. On a workstation with a 28-core
Intel Xeon w7-3465X, the soil-moisture deployment's four tile programs (the parameter fit and
three retrievals) run 12.6 to 24.0 times faster than on one core: the median of three runs of
compute time, each against the same program's own one-slice run, over tiles of 0.41 to 6.55
million pixels (`BENCHMARKS-A4500-56cores.md`, section 4, in the soil-moisture-workflows
repository). Those figures are measurements. What is proved about that path is the kinds of the
sizing arithmetic, which keep a count of slices from being confused with a count of bytes; that
the slices together compute what one run over the whole tile computes rests on the independence
of the pixels, and is not proved: no theorem states it, and no checked-in test compares the two
runs bit for bit.

At the other five layers the calculus builds on what TorchLean provides. _Uncertainty_:
TorchLean bounds round-off; the calculus states measurement uncertainty along the GUM, Willink
and SSPRC methods, with coverage intervals and conformity assessment, and charges round-off to
that budget as numerical adequacy, written in TorchLean's binary32 rounding vocabulary
({ref "uncertainty"}[the uncertainty chapter]). _Code generation_: TorchLean compiles one scalar
function to one kernel; the calculus compiles a whole model to one, and prints the same program
as C and Julia, where TorchLean reaches Julia only as an external process. _Kernel alphabet_:
the addition is the operations remote-sensing forward models are built from: attenuation and
extinction are exponentials, dielectric mixing takes square roots and logarithms, branch-free
selection takes `min` and `max`, and calibration curves are tables. _Recording_ and _Numbers_:
the recording carrier and the carrier ladder are built on TorchLean's tape and floating-point
formats. TorchLean's tape records each operation it is given; the sharing recorder adds a tape
that is proved to be the compaction of that recording, at the memory of the model's graph
instead of its expression tree.

:::svg_figure "torchlean-extension" PropertyKindCalculusBlueprint.Figures.torchleanExtension
What PropertyKindCalculus adds beyond TorchLean, layer by layer.

The left column is TorchLean; a `#n` marks a change contributed to it by this work, and a dashed
box a layer where TorchLean's source has no counterpart. The right column is what the calculus
adds at that layer. In the kernel alphabet, the filled chips are
the operations TorchLean's kernel compiler `Program.of` refuses in binary32 and binary64, on the
revision the calculus pins; TorchLean's eager device and tape operations include `exp`, `log` and
`sqrt`, so the extension is to one certified fused kernel holding a model's whole arithmetic.
The table fetch is shared: its device kernel is a TorchLean `Program.of` kernel, and its
semantics is the calculus's vocabulary extension.
The last two rows of chips on the left are eager device-buffer operations contributed by this
work (#52, #53): LibTorch calls on buffers, not operations of a certified `Program.of` kernel.
In the recording layer, #54 is the power whose exponent is a recorded value: a tape operation of
TorchLean, present at the pinned revision.
:::

:::table +header
*
  * Modules
  * What they provide
  * Reading
*
  * `TapeM`, `TapeFaithful`
  * the elementwise recorders over TorchLean's single entry `Tape.apply`, and their forward-value lemmas for symbolic inputs
  * framework machinery: depends on TorchLean alone
*
  * `TapeCse`, with its denotation theorems
  * value-preserving common-subexpression elimination over a recorded tape, keyed on operation, remapped parents and value bits
  * framework machinery
*
  * `TapeSharedCarrier`, with `shares_record`
  * a recording carrier that shares sub-expressions while it records, proved to emit the compaction of the unshared recording
  * framework machinery, keyed on the calculus's `NumCarrier`
*
  * `TapeEval`, `TapeStraightLine`, `TapeCodegen`, `TapeCodegenJulia`
  * the tape's forward denotation; one straight-line program per tape with one denotation theorem; CUDA, C and Julia printers of it; arithmetic-intensity and peak-residency accounting
  * framework machinery, over an alphabet that includes `exp`, `log`, `sqrt`, `min`, `max` and the table fetch
*
  * `CudaCarrier`, `BatchCarrier`
  * the branchless carrier on device buffers; the backend boundary as a class, and task-sharded CPU execution
  * framework machinery, keyed on the calculus's `NumCarrier`
*
  * `Fp32Spec`, `Fp32`, `Fp32Math`
  * the binary32 rungs of the carrier ladder, with the executable rung's side condition, and the record that the executable carrier has a smaller function vocabulary than `ℝ` and none of its function laws
  * metrology
*
  * `TapeCarrier`, `TapeParity`, `TapeHom`, `TapeSeal`
  * the recording carrier, the denotation bridge, the homomorphism and its tactic, and the seal of the computation
  * metrology: the provenance hypergraph meets the tape here
*
  * `FusedKinds`, `LutCarrier`, `Platform`
  * the kinded fused form; the table fetch as a declared vocabulary extension; host capacity and memory-bounded sizing, every count and byte figure a kinded quantity
  * metrology applied to the computation itself
:::

The code generator and TorchLean's certified kernel compiler are complementary, not redundant.
`Program.of` proves a Lean scalar function equal to a kernel expression and the emitted CUDA
equal to the expression, and its expressions have no transcendental primitives: on the pinned
revision it refuses `Float.exp`, `Float.sqrt` and `min` alike. The calculus's code generator
covers that alphabet and the table fetch, proves the printed program equal to the tape, and
leaves each printer's dozen forms and the host's `exp` and `log` to trust. A framework that
offered both would let a branchless model be compiled end to end by one certified path. Which
side should absorb the other is a design question for the framework's maintainers.

# Open edges

What the chain above does not yet cover, each one checked rather than recalled:

- The homomorphism stops at `exp` and `sqrt`. The recorders and their forward-value lemmas cover
  `abs` and `log`, but neither the bundled homomorphism nor `tape_hom` has a case for them: on
  `x + log y` the tactic leaves `Evaluates (log y) (log vy)` open, where on `x + exp y` it closes.
- The composed pipeline theorem is stated for tapes without table fetches. With them, the
  recorded fixture is faithful for all inputs (`lut_kernel_faithful`) and the program denotes as
  the table-extended interpreter, but no one theorem composes the two through compaction.
- The compaction's denotation theorems and the composed pipeline theorem live in the `Examples`
  library, beside the fixtures that exercise them, so a consumer that imports
  `PropertyKindCalculus.Torch` alone does not receive them.
- The device tape has no `fmin` or `fmax` operator: that needs a vector-Jacobian product, and
  only buffer-level forward values exist.
- The recording-time measurement is a synthetic chain of additions (128 000 additions in
  0.159 s); no science model has been timed through both recorders.
- `shares_record` is proved per model: `tape_shares` unfolds the model, and its goal grows with
  the expression tree, so it closes the probe kernel (`kernel_shares_record`) and not a model
  whose tree is too large to unfold, which is where sharing matters most. The theorem compares
  forward content, not the `backward` closures, and assumes one tensor shape.
- The sharing recorder inherits `cseCompact`'s key: two input leaves with one name and one
  recorded value, or two tables with one name fetched at the same operands with the same
  result, are one node. `record` rejects an input name that holds two different tensors, and
  code generation rejects two supplied tables with one name; two inputs with one name and one
  recorded value cannot be told from one input used twice, so distinct names remain a
  precondition there.

# How far it reaches

For metrology, nothing above depends on the quantities being soil moisture, radiances or
anything else. The pattern applies to any kind system written over a scalar-generic numerical
framework: the kinds erase by `rfl`, so they cost nothing at run time; the floating-point
rungs state their side conditions instead of assuming them; and the provenance a metrologist
needs for an uncertainty budget — which inputs and which constants an output depends on — is a
theorem about the executed program. There is therefore no trade between metrological rigor and
throughput to negotiate per model.

For verified numerical frameworks, the calculus is a demanding consumer: one whose acceptance
test is bit parity across devices, which turns every run into a differential test, and whose
models are long enough to expose costs that grow faster than the program. The framework
machinery in the table above (recorders with forward-value lemmas, value-preserving compaction
with a proof, and one program with one denotation theorem for every printer) carries no
metrology, and it belongs to any framework that records tapes and generates kernels.
