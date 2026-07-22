# PropertyKindCalculus

A Lean 4 formalization of **Dybkær's *[An Ontology on Property for Physical,
Chemical, and Biological Systems](References/ontology-on-property.pdf)*** (2009),
extended with **Flater's full tracking of kinds of quantities**
([NIST Technical Note 1943](References/NIST.TN.1943.pdf), Appendix C).

It continues a line of machine-checkable metrology modeling 
from the Object Management Group (OMG) Systems Modeling Language (SysML)
 Conceptual model of Quantities, Units, Dimensions and Values (QUDV),
then an OML/OWL2 metrology vocabulary grounded in Dybkær — and is the first in
which the *quantity calculus itself*, not just the taxonomy around it, is a
checked artifact. OWL2 captures the taxonomy (specialization, instantiation,
dimensional factoring) but is structurally unable to express the calculus: the
partial kind-interaction algebra, scale-type operator gating, extensivity, unit
conversion, or any algebraic *law* as a provable theorem. Lean has all of it
natively.

The full rationale — the QUDV → OML lineage and how each construct maps into
Lean's type system — is in the [design blueprint](blueprint/) ("Why a calculus,
not a taxonomy").

- **License:** Apache-2.0 — see [LICENSE](LICENSE)
- **Toolchain:** `leanprover/lean4` (see [lean-toolchain](lean-toolchain))

## On the name

The calculus is over **kinds of *property*** — Dybkær's root notion (§6.19),
which spans nominal, ordinal, and quantitative kinds alike. A **kind of
quantity** is the special case whose scale carries magnitude (§13.3.1, in Lean
`IsQuantity k := k.scale.HasMagnitude`); the `QuantityKind` of QUDT and SysML v2
is therefore *subsumed here* — as a scale-gated leaf of the property-kind spine,
not as its root. The name keeps "Property" in front to make that genus visible
(and to avoid reading the bare word "kind" in its type-theoretic sense). So the
project is broader than a quantity calculus by construction, with quantity kinds
as its motivating special case.

## Representational conventions

* **Meta-concepts** ("what it is to be a kind-of-quantity") → Lean
  `structure`/`class`.
* **Specific kinds** (length, mass, vwc) → **values** of those structures, so
  applications extend the ontology by writing `def`s (open-world), mirroring how
  OML *declares* concepts. A fixed `inductive` would not be extensible.
* **Individual quantities** ("the width of this pencil") → **terms** of the
  quantity type. An individual *instantiates* its kind; it is **not** a subtype.
* **OML relations** map directly: `GeneralUnitaryQuantity`→`KindOfProperty`,
  `Specializes`→`Specializes`, `IndividualUnitaryQuantity`→`IndividualProperty`,
  `HasUnit`/`Instantiates`→ the `u`/`kind` indices.
* **Traceability**: every definition cites Dybkær by section (`§x.y`) or Flater
  by section, so the formalization can be audited against the source.

## Libraries and how to consume them

The package ships six libraries so the core is exportable on its own:

| Library | Source tree | Contents | `lake build` |
|---|---|---|---|
| `PropertyKindCalculus` (default target) | `PropertyKindCalculus/` | the exportable, Mathlib-free ontological spine | `lake build` |
| `Examples` | `examples/` | worked examples for the spine (`PropertyKindCalculus.Examples.*`), Mathlib-free | `lake build Examples` |
| `Dimension` | `dimension/` | the PhysLib-backed coherence layer (library modules only, no examples) — `dim` as the forgetful functor into PhysLib's `Dimension` (`PropertyKindCalculus.Dimension`), the scale-spanning unit classification (R13, `PropertyKindCalculus.ScaleSpanning`), Flater's interaction algebra `KMul`/`KDiv` (`PropertyKindCalculus.Interaction`), and the `ℝ` quantity carrier (`PropertyKindCalculus.QuantityReal`); pulls in PhysLib + Mathlib | `lake build Dimension` |
| `DimensionExamples` | `examples/` | worked examples for the Mathlib-backed `Dimension` layer (dimension functor, interaction algebra, `ℝ` quantity carrier, the ISO 80000 catalogue, and the ISO 80000-2 §18 vector quantity) — kept under `examples/` so no library module carries example code; PhysLib + Mathlib-backed (transitively) | `lake build DimensionExamples` |
| `Iso80000` | `iso80000/` | the standards-grounded layer: a references catalogue citing the ISO/IEC 80000 parts by name + version only (no normative content), plus the full catalogues of **eleven** of the thirteen parts — ISO 80000-3 *Space and time* (42 items), ISO 80000-4 *Mechanics* (54 items), ISO 80000-5 *Thermodynamics* (54 items), IEC 80000-6 *Electromagnetism* (85 items), ISO 80000-7 *Light and radiation* (66 items), ISO 80000-8 *Acoustics* (18), ISO 80000-9 *Physical chemistry and molecular physics* (62), ISO 80000-10 *Atomic and nuclear physics* (125), ISO 80000-11 *Characteristic numbers* (115, all dimension one), ISO 80000-12 *Condensed matter physics* (60), and IEC 80000-13 *Information science and technology* (42) — quantity-kinds, units, the length/force/energy/power/radiation specialization lattices, the sub-suffixed characteristic-number homonyms, the gray/sievert and mole-reduction collisions, the dimension-collision, scale-type, and scale-spanning (R13) capstones, and the formalized *Remarks* (several crossing between parts); PhysLib-backed | `lake build Iso80000` |
| `Torch` | `torch/` | the TorchLean-backed instance of the R10 exec/spec refinement bridge — the binary32 `FP32` (rounding spec) and `IEEE32Exec` (executable) carriers realizing `CarrierRefinement`; depends on TorchLean | `lake build Torch` |

The core spine and its `import PropertyKindCalculus` stay Mathlib-free. Note that
`require`-ing the package now also *resolves* the TorchLean dependency (it backs only
the `Torch` library), so a consumer's lock file lists it even when only the core is
imported and `Torch` is never built.

A downstream project depends on the package and imports selectively:

```lean
require PropertyKindCalculus from git "…/PropertyKindCalculus" @ "main"   -- in the consumer lakefile

import PropertyKindCalculus                       -- core spine only, no examples
-- import PropertyKindCalculus.Examples           -- opt in to the examples too
```

The **core spine is Mathlib-free** and builds with only the Lean toolchain. The
PhysLib-backed coherence layer has landed as the separate `Dimension` library —
`dim` as a forgetful functor (`PropertyKindCalculus.Dimension`), Flater's
interaction algebra (`PropertyKindCalculus.Interaction`), and the `ℝ` quantity
carrier (`PropertyKindCalculus.QuantityReal`), with its worked examples in the
`DimensionExamples` library — the layer where PhysLib + Mathlib enter, so a plain
`import PropertyKindCalculus` stays Mathlib-free. PhysLib tracks the same toolchain
this package pins (`leanprover/lean4:v4.30.0`). The soil-moisture *retrieval* model
lives in a **separate downstream repository** that `require`s this package — an
application of the calculus, kept out of PKC so the package stays focused on
metrology and the ISO/IEC 80000 parts.

## Design blueprint

A [Verso](https://github.com/leanprover/verso) /
[verso-blueprint](https://github.com/leanprover/verso-blueprint) design document
lives in [`blueprint/`](blueprint/). It records the **proved spine** (each node
linked to a real, sorry-free declaration here, so its status is read from the
checked library) and the **capstone theorems we plan to provide** — the
dimension-1 disambiguation, dimensional coherence (`dim` is a homomorphism), the
Flater interaction algebra, unit-conversion round-trip, and extensivity — with a
generated dependency graph and status summary. It is a **separate Lake package**
(it pulls in Verso) so a plain `import PropertyKindCalculus` stays lightweight:

```bash
cd blueprint
lake update && lake build   # type-check the doc + its Lean links
./scripts/ci-pages.sh       # render both outputs + print absolute paths to open
./scripts/ci-pages.sh --no-pdf   # fast HTML-only loop (~50 s vs ~5.5 min; skips the WeasyPrint PDF)
```

Open either `_out/blueprint/html-single/index.html` (one self-contained page) or
`_out/blueprint/html-multi/index.html` (the full per-chapter site) directly as a
file — `ci-pages.sh` post-processes `html-multi` so chapter navigation works over
`file://`. Search and the dependency graph need an HTTP server (`python3 -m
http.server 8000 -d "$PWD/_out/blueprint/html-multi"`). See
[`blueprint/README.md`](blueprint/README.md) for details.

## Go fast, automatically — deployment and the megakernel backend

The *go fast, automatically* half of the discipline (the deployment-spectrum section of the
*Write Once, Correctly* blueprint chapter) is realized by instantiating **one** carrier-parametric
`[NumCarrier α]` model at different carriers — moving along the spectrum is *choosing a carrier, not
rewriting the model*:

- **CPU, single-threaded** (`α := Float`) — the universal baseline and the per-pixel *oracle*; runs
  any science model, including ones whose I/O–compute interleaving defeats parallelism.
- **CPU, multi-threaded** — coarse-grained Lean-`Task` sharding over the pixel axis (`runSharded`);
  needs a model with good arithmetic intensity *and* independent work-items.
- **GPU, eager** (`α := CudaT`) — one pre-compiled CUDA kernel per operation, dispatched by FFI. This
  is *not* an IR interpreted on the GPU and involves no IR; it is eager, operation-at-a-time launch,
  so every intermediate round-trips through DRAM → *memory-bound* (arithmetic intensity ≈ 0.17 vs an
  ideal ≈ 13.75 for the AVS fit). The current production GPU path.
- **GPU, megakernel-compiled** — record the branchless model at the tape carrier → CSE its distinct-op
  DAG → emit one fused CUDA `__global__` kernel (one thread/pixel, the whole model in registers, DRAM
  touched only for inputs/outputs). A genuine *ahead-of-time* compilation Lean → recorded IR → `.cu`,
  *not* an interpreter; *compute-bound*, approaching the roofline. Needs a model with good AI
  properties (branchless — guaranteed by `NumCarrier` — and register-fittable).

The **megakernel codegen backend** lives in the `Torch` library and is verified:

- `PropertyKindCalculus.Torch.Paradigm.TapeCodegen` — generic `Tape → CUDA`/C-stub codegen, a `Float`
  reference interpreter (the generated kernel's semantics *and* the CPU bit-exact validator), and
  arithmetic-intensity accounting.
- `PropertyKindCalculus.Examples.TapeCodegenDemo` — the AVS Stage-2 residual + 4 Jacobian columns
  recorded, CSE'd to a 28-node DAG (18 ops), codegen'd, and `#guard`'d **bit-identical** to the `Float`
  source with no CUDA toolchain.
- `PropertyKindCalculus.Examples.TapeCodegenProof` — recorder faithfulness for **all** inputs
  (6 sorry-free theorems; axioms `[propext, Classical.choice, Quot.sound]`).
- `PropertyKindCalculus.Examples.LmStepCodegenDemo` — the *whole* projected-LM step (residual +
  Jacobian reduction over *K* rows → normal equations → Marquardt damping → 4×4 Cholesky solve →
  box clip) recorded, CSE'd to a **322-node** DAG, codegen'd, and `#guard`'d **bit-identical** to the
  `Float` source — arithmetic intensity **4.48/step (≈ 268.7 for the ×60 fit)**, the honest whole-step
  number.

Compile the emitted kernel with `nvcc --fmad=false -prec-div=true -prec-sqrt=true` (no FMA-contraction,
no re-association) to stay bit-identical to the eager path — the speedup is pure memory-traffic
elimination, orthogonal to the numerics.

### Follow-ons

Status: ✅ done · 🚧 in progress · ⬜ planned

- ✅ Generic `Tape → CUDA` megakernel codegen (+ portable C-stub twin) and AI accounting.
- ✅ AVS residual/Jacobian recorded → CSE DAG → codegen → CPU bit-exact `#guard` (`TapeCodegenDemo`).
- ✅ Recorder faithfulness proved for all inputs, axiom-audited (`TapeCodegenProof`).
- ✅ **Recorded the *whole* trust-region step, not just the residual/Jacobian fragment**
  (`Examples.LmStepCodegenDemo`, parallel to `TapeCodegenDemo`). One full `lmStep` iteration —
  fold the residual + 4 Jacobian columns over all *K* observation rows into the 4×4 normal equations
  (`JᵀJ`, `Jᵀr`, a *reduction*), Marquardt-damp the diagonal, solve the 4×4 SPD system by unrolled
  Cholesky (`solveSPD4`), update θ, and box-clip — recorded self-contained over `[NumCarrier α]`,
  CSE'd, codegen'd, and `#guard`'d **bit-identical** to the `Float` source. This is the *honest*
  whole-step number: the fragment (28 nodes, AI 0.56/step) undercounts because it omits the O(*K*)
  reduction and the Cholesky tail.
  - *Result (K=5).* a **322-node** DAG — 297 ops: mul 138, add 85, sub 43, **div 14, sqrt 4, min 4,
    max 4, exp 5** (CSE folds the two attenuations/row to one) — i.e. the reduction, the linear solve
    (`div`/`sqrt`), and the box clip (`min`/`max`) the fragment lacked, and every op was already in the
    codegen's table (**no backend change needed**). **AI 4.48/step (8× the fragment), ≈ 268.7 for the
    ×60 whole-fit** (vs eager ≈ 0.17) — the compute-bound, whole-fit-in-registers number that decides
    CPU-vs-GPU for the deployed fit.
  - *Loop constants.* the λ value and box bounds `lb`/`ub` — which `NumCarrier`, offering only
    `0`/`1`/`Nat` literals, cannot express — enter the tape via **`BatchCarrier.const (C := TapeBuilder)`**
    (`Paradigm.TapeBatchCarrier`), the app-level constant-lifting instantiated at the recording carrier
    (it delegates to `TapeBuilder.const`, an unnamed `fill`-leaf). Recording the step is thus the same
    app code a `[BatchCarrier C]` deployment runs, only at `C := TapeBuilder`.
- ✅ **Decoupled `BatchCarrier` from the CUDA-only `Buffer.atten` and made the fused op domain-neutral**
  so the `Torch` library builds green CPU-side (`lake build Torch`). The old `FusedAtten` class named a
  soil-moisture `exp(−2·b·ndvi)` device kernel present only in the CUDA/deploy fork, so the module — and
  hence the whole `Torch` lib — did not compile in the default config *and* tied PKC to the
  soil-moisture domain. It is now the domain-neutral **`FusedExp`** class of _fused forms_ — bit-exact
  single-op refinements of hot composed sub-expressions — with a first primitive
  `scaledProdExp c x y = exp(c·x·y)`, realized by a portable `CudaT.scaledProdExp` (composed from the
  dual-backend `Buffer` kernels), **one instance for both** the CPU-stub and GPU (`-K cuda`) builds, with
  a clean seam for a `-K cuda` single-fused-kernel override. The class is extensible — further forms
  (`exp(a+c·x)`, `exp(−γ·x²)`, `logSumExp`, …) drop in as hot paths warrant — and the megakernel codegen
  is its general counterpart (it fuses the *whole* model, not one named shape). The soil-moisture
  attenuation is just `scaledProdExp (−2) b ndvi` (a bit-exact twin of the composed `attenuation`),
  defined downstream in the science model — not in PKC. This also unblocked
  the `BatchCarrier (TapeBuilder)` recording instance (`Paradigm.TapeBatchCarrier`) the step demo uses.
  (A separate stale import — `Torch.Fp32`'s `BridgeFP32.Ops`, renamed in TorchLean 4.32 — was fixed in
  the same pass so the full lib is green.)
- ✅ **Eager AI is now *computed*, not cited.** `TapeCodegen.aiReport`/`intensity` used to report only
  the *fused* (megakernel-target) intensity; the **eager ≈ 0.17** the batched apps run at was merely
  *cited* in docstrings/demos. `aiReport` now also accumulates the eager carrier's DRAM traffic
  `eagerBytes = Σ over op-nodes of (nParents + 1)·4` (every op reads its operand buffers and writes its
  result buffer through global memory), and `intensity` returns an `Intensity` record carrying the
  computed `aiEager` alongside `aiStep`/`aiFit`. `LmStepCodegenDemo` now prints the honest,
  machine-checked roofline gap: **eager 0.117 vs fused 4.48/step (38×), vs 268.7 for the ×60 whole-fit
  (2301×)** — no asserted constants. This is the accounting the two recordings below consume to produce
  a genuine per-application AI report.
- ✅ **Deployed `tile_gpu` + `tile_retrieve` kernels recorded and measured — homed downstream in SMM.**
  The deployed weighted trust-region AVS fit and the projected-Newton retrieval lived inside the
  `gpu-smap-nisar-sm` CLIs (below which nothing could import them), so they were first **hoisted into
  soil-moisture-model** as the single source of truth (`kernel.avs_weighted` + `kernel.batch_helpers` =
  `ObsW`/`buildObsW`/`normalEqsAvsW`/`lmStepAvsW`/`sseAvsW`/`penTR`/`trStep`; `kernel.retrieve` =
  `rEffOf`/`rOfSm`/`newtonStep`/`retrieveSm`). Two SMM recorders (`examples.tile_gpu_ai`,
  `examples.tile_retrieve_ai`) then record the **real deployed defs** at `C := TapeBuilder`, hash-cons,
  and report eager-vs-fused AI, each `#guard`ed **bit-identical** to a scalar fp64 oracle carrier
  (`examples.scalar_oracle`, `Scalar1 s := Float` — needed because these defs are `[BatchCarrier C]`, not
  `[NumCarrier α]`, so they have no direct `Float` instance). Since the megakernel records ONE step and
  loops it (the thunk-tape unrolls exponentially), each kernel is split into setup (×1) + iterated body
  (×60 fit / ×12 Newton). Measured (bit-exact):
  - `tile_gpu` **fit body** (one weighted `trStep`, K=5): 442 ops, **eager 0.115 vs fused 4.70/step,
    282 for the ×60 fit — a 2460× roofline gap**; **setup** (Mironov ε + Fresnel + weight): eager 0.142
    vs fused 8.25 (58×).
  - `tile_retrieve` **Newton body** (one step, 3× dielectric): 217 ops (16 `sqrt`, 22 `div`), only 3
    inputs → **eager 0.156 vs fused 24.7/step, 296 for the ×12 — a 1905× gap (159× per step)**, the
    densest kernel in the study; **R_eff setup**: eager 0.19 vs fused 0.79 (4.1×).

  (The recorders derive both the eager and fused AI from PKC's `intensity` / `aiReport.eagerBytes`: SMM's
  PKC pin was bumped to the eager-AI-accounting commit, so they delegate rather than recompute the eager
  traffic.)
- ✅ **The third retrieval method — the closed-form `smOfReflectivityHH` — recorded and measured.**
  `examples.tile_retrieve_reflectivity_ai` (SMM) records the deployed closed-form Stage-3 inverse
  (`tile_retrieve_reflectivity` / `kernel.retrieve_analytic`). Being plain `[NumCarrier α]`, its bit-exact
  oracle is `α := Float` directly (`mironovCoeffsFloat`) — **no `Scalar1` carrier needed**. Measured
  (bit-exact): the **whole per-pixel retrieval** (Fresnel-HH quadratic root + 8 Mironov loss-coupling
  sweeps + final Step-2/3) is **511 ops** (34 `sqrt`, 37 `div`), 2 inputs → **eager 0.143 vs fused 71.7 —
  a 500× roofline gap**, and 71.7 is the highest single-kernel fused AI in the study. It has no outer loop
  (the sweeps are unrolled internally), so its 511 ops are the *entire* retrieval — fewer than the Newton
  path's 217 × 12 = 2604 — the closed form's whole point. The shared recorder harness (`aiBlock` + the
  record→CSE→oracle→`#guard` pattern) was factored into `examples.ai_recorder` and both prior recorders
  refactored onto it.
  - **Pitfall found + fixed — deferred carriers unroll folds exponentially.** A naïve recording (call
    `smOfReflectivityHH (α := TapeBuilder)` and run the thunk) blew up to **>100 GB at elaboration** and
    had to be OOM-capped. `TapeBuilder` is a *deferred* carrier: every reference to a value re-runs its
    emission, so the closed form's 8-deep loss-coupling fold — whose accumulator is reused ~4× per sweep —
    unrolls ~4⁸× *before* `cseCompact` can dedup it. Fix: thread the fold through the tape monad and
    **materialize the accumulator to one node per sweep** (`⟨pure id⟩` re-emits nothing), making the
    recording linear in the sweep count (build dropped from >100 GB / OOM to **6.3 s**). The `#guard`
    against `smOfReflectivityHH (α := Float)` keeps the hand-threaded fold bit-exact to the deployed def.
    This is a general hazard for any science model recorded through a deferred/thunk carrier — see the
    blueprint's WriteOnce chapter for the write-up.
  The **table-lookup** method stays off this list — a gather is inexpressible in `NumCarrier`, so it has
  no AI row; its CPU/GPU baselines are the deploy item's concern.
- ✅ **The SSOT is complete — the `gpu-smap-nisar-sm` CLIs are rewired onto the hoisted SMM defs.**
  `tile_gpu.lean` and `tile_retrieve.lean` no longer carry local copies of the kernels: they `import`
  `kernel.avs_weighted` / `kernel.batch_helpers` / `kernel.retrieve` and keep only the app-specific shell
  (the `IO` driver `fitAvsTR`, `computeChunk`, the scalar-carrier Layer-0 twin, npy I/O, QC flags, the
  CLI). `tile_retrieve`'s retrieval body is now `rEffOf` + `retrieveSm` + `rOfSm`; `tile_gpu`'s
  observation build is `buildObsW` and its trust-region step/objective are the imported `trStep`/`penTR`
  (`fitAvsTR` runs exactly them and adds only the liveness guard). The app's trust-region parity proofs
  (`parity/tile_tr_refine`, `tile_tr_kinds`) are repointed at `SoilMoisture.Algorithm.AvsWeighted` and
  **still pass unchanged** — the `SatisfiesM` refinement and the `rfl`/induction erasure now certify the
  *hoisted* defs, a machine-checked guarantee the deployed fit's numeric content did not move. Full
  `lake build` green (the pin is bumped, the `FusedExp` edit committed); both CLIs smoke-tested on
  synthetic tiles (`tile_gpu`'s batched-`CudaT` and scalar-`Float` carriers agree bit-for-bit;
  `tile_retrieve`'s `R_eff` matches the closed formula exactly). Payoff realized: the duplication is gone,
  so a fit/retrieval change lands in one place and the deployment and the AI recorders can never drift.
  `tile_retrieve_reflectivity` (imports `smOfReflectivityHH`) and `tile_retrieve_lut` (imports
  `kernel.r_lut`) were already SSOT-clean; the deliberately out-of-framework `tile_retrieve_lut_eager` GPU
  baseline was correctly left untouched.
- ✅ **The proof runs end to end — the generated kernel is the source kernel for all inputs.**
  `examples.tape_codegen_end_to_end` lifts recorder-faithfulness (`examples.tape_codegen_proof`, which
  pins the *stored* values at the placeholder recording inputs) to the codegen-relevant statement: for
  **every** input environment `env`, `evalTape env` on the recorded DAG computes the source
  `[NumCarrier α]` kernel at `env` — not just the one pixel `examples.tape_codegen_demo` `#guard`s. The
  vehicle is an `evalTape`-denotation bridge `Faithful` mirroring `paradigm.tape_parity`'s `Evaluates`
  but tracking the re-interpreted `Float` alongside the stored tensor; each `NumCarrier` op preserves it
  (`Faithful_add/sub/mul/exp/…`), so the AVS Stage-2 residual + four Jacobian columns chain to
  `resJac (α := Float)` at `env` (`residual_kernel_faithful`, sorry-free — axioms `[propext,
  Classical.choice, Quot.sound]`). The **`cExpr` ↔ `cOp` rendering table** (`rendering_table_binary`/
  `_unary`/`_reject`) certifies the emitted CUDA/C covers exactly the interpreter's op alphabet, so the
  generated source and the validated `evalTape` are the same program. `cseCompact` value-preservation is
  pinned at both ends: node-locally, `cseKey_denotation_sound` proves the merge key is denotation-sound
  for op nodes (the interpreter reads only op-name + remapped parents, never the stored bits, so any two
  nodes CSE may collapse are interchangeable for all inputs — no `Float.toBits` injectivity needed); and
  concretely, `#guard cse_preserves_resJac` machine-checks that on the deployed `resJac` tape every
  node's stored value is bit-identical to its CSE-remapped node's.
- ✅ Lifted `cseKey_denotation_sound` across the whole hash-cons pass for an *arbitrary* well-formed
  tape (`examples.tape_cse_structural`). `cseCompact`'s `Id.run` `for`-loop is reformulated as a fold
  (`cseCompact_eq_foldl`) and a `Std.HashMap`/`remap`/`newTape` **loop invariant** (`Inv`, preserved by
  `inv_step`, established by `Array.foldl_induction` in `cseFold_inv`) yields three sorry-free
  whole-pass corollaries (axioms `[propext, Classical.choice, Quot.sound]`): `cseCompact_structural` —
  every original node's CSE-remapped node carries the **same op name, parents remapped by the same map,
  and a bit-identical stored value**, the whole-pass promotion of the node-local `cseKey_denotation_sound`;
  `cseCompact_wellFormed` — the compacted tape stays well-formed; and `cseCompact_preserves_stored` — the
  arbitrary-tape generalisation of the machine-checked `cse_preserves_resJac`. No `Float.toBits`
  injectivity is used: the invariant is over op names, ids, and bit patterns.
- ⬜ Wrap the structural correspondence in the `evalTape`-fold argument to get the pointwise
  `evalTape`-denotation equality (`∀ env id, valsC.getD (remap id) 0 = vals.getD id 0`): an `evalTape`
  value-characterisation (a `foldlM` invariant) + strong induction on `id` over `cseCompact_structural`.
  Op nodes need no `Float.toBits` injectivity (the interpreter reads only op-name + remapped parents);
  **const leaves do** — `evalTape` reads their stored value via `nodeScalar`, so equal value-*bits* give
  equal denotation only under `toBits` injectivity (absent in core), which the concrete
  `#guard cse_preserves_resJac` discharges empirically for the deployed kernel.
- ⬜ GPU landing (gated): wire the generated `.cu` through the lakefile `extern_lib` /
  `buildNativeBackendLib` slot, compile, validate against the fp64 oracle, and measure achieved
  throughput / arithmetic intensity against the eager path; likewise override `CudaT.scaledProdExp` with
  a single fused device kernel under `-K cuda`.
- ⬜ Apply the backend to the deployed SMAP–NISAR kernels in the downstream application — and deploy
  **both** Stage-3 CLIs side by side, because the A/B is the point. Three Stage-3 methods exist, and
  the distinction must stay sharp:
  1. **Table lookup** (operational `r_lut.py` / SMM `kernel.r_lut`): nearest clay+angle node, linear
     interp along SM — a *gather*. `retrieveSmFromR` is host-scalar (`Array Float` in, `Option Float`
     out): there is no carrier parameter to instantiate, so on the tape/CUDA carrier it is not merely
     slow, it is **inexpressible** (`NumCarrier` has no indexing) and its GPU column is structurally
     empty. To be fair: the GPU hardware gathers fine (texture/L2), and TorchLean's eager engine even
     exposes `gather*` ops — the exclusion is the *verified write-once vocabulary's*, by design. So
     deploy the LUT twice, once per meaning of "runs":
     - ✅ `tile_retrieve_lut` (CPU): a small host CLI over `kernel.r_lut` — per-pixel scalar loop over
       precomputed nearest-angle slices (SM 100∈[0,0.6] × clay 20∈[0,1] × the tile-40° nearest angle
       node 38.889°), reusing the shared `rEffOf` for Step 1. **Built + validated** (~3.8 ms/1600 px;
       SM∈[0,0.6], monotone in R_eff, NaN range-guard faithful to `no_solution_above/below`). Fills the
       CPU wall-time cell. (`r_lut_example` remains the demo-scale monotonicity/QC witness.)
     - ✅ `tile_retrieve_lut_eager` (GPU): an **eager-tensor port** on the `Cuda.Tape` engine (A4500
       under `-K cuda`, C stubs otherwise) — the clay slice + `invΔ` table uploaded as leaves, an
       on-device `gatherRowsNat` at the nearest-clay node, then the SM inversion. Design finding worth
       keeping: the eager tensor vocabulary (`const/add/sub/mul/max/min/clamp/relu/reduceSum/gather*`)
       has **no compare / select / round / div**, so the intended 7-step bisection + NaN range-guard is
       *inexpressible in the tensor API* — the thesis, one layer up. What IS expressible is a branchless
       **clamped-ramp** `pos = Σⱼ clamp((R_eff−slice[j])·invΔ[j],0,1)`, **bit-exact to `np.interp`
       in-range** (validated to ~6e-8 vs the fp64 CPU LUT), whose one deviation is that it **clamps**
       out-of-range instead of returning NaN — no comparison to flag it. This is the *deliberately
       deficient* baseline: it runs and times, but records **no tape**, compiles to **no megakernel**,
       and sits **outside the verified single-source story** — no erasure/parity theorem, plus the LUT's
       accuracy bias — exactly the artifact class the calculus exists to eliminate. (GPU run needs a
       one-time `pixi install --manifest-path cuda-toolchain/pixi.toml`, then `./cuda.sh exe`.)
  2. **Equations, iterated** (`tile_retrieve`): 12 projected-Newton steps on the same physics
     (~36 forward evals/px) — fixed trip count, hence recordable; the ×12 body measured above.
  3. **Equations, solved** (`tile_retrieve_reflectivity` / SMM `kernel.retrieve_analytic`,
     `smOfReflectivityHH`): closed-form Fresnel-HH + Mironov root formulas, 8 unrolled loss-coupling
     sweeps, ~2 forward-evals/px.

  All the CLIs share one I/O + flags/QC contract (2 vs 3 already validated NaN-mask-identical on
  synthetic tiles), so outputs diff directly. CPU compares all three (closed form 18.5 ms vs Newton
  28.3 ms per 160×160 tile; the host-scalar LUT now measured too); GPU compares 2 vs 3
  *inside* the verified pipeline, with `tile_retrieve_lut_eager` alongside as the out-of-framework
  baseline — the LUT's absence *from the verified column* is the SMM textbook Ch06 “was the look-up
  table an accelerator?” verdict (which also
  measures the LUT's ~6e-3 m³/m³ angle-quantization bias vs 2e-8 for the closed form, so the
  performance table should sit beside the accuracy one). Record (3) à la `examples.tile_retrieve_ai`,
  codegen both equation kernels, measure. Optional nvrtc runtime kernel specialization per tile shape.

## References

The primary sources are vendored under [`References/`](References/) so the
docstrings' `§x.y` citations resolve to a local copy:

* [`References/ontology-on-property.pdf`](References/ontology-on-property.pdf) —
  René Dybkær, *An Ontology on Property for Physical, Chemical, and Biological
  Systems* (2009).
* [`References/NIST.TN.1943.pdf`](References/NIST.TN.1943.pdf) — David Flater,
  *Architecture for Software-Assisted Quantity Calculus*, NIST Technical Note
  1943 (2016).
* [`References/VIM4-2CD-2023-07-31.pdf`](References/VIM4-2CD-2023-07-31.pdf) —
  JCGM/WG2, *International Vocabulary of Metrology* (VIM), 4th edition, 2nd
  Committee Draft (2CD), 2023-07-31. The `VIM4 2CD x.y` clause citations in the
  docstrings resolve to this copy.

## Roadmap (faithful to Dybkær's chapter structure)

Status: ✅ built & proved · 🚧 next · ⬜ planned

| Module | Source | Status |
|---|---|---|
| `Foundations` — system, object | Dybkær Ch. 3 | ✅ |
| `Scale` — operator-based scale types + monotonicity meta-thm | Ch. 12 (Fig. 12.21) | ✅ |
| `Kind` — kind-of-property / -quantity + scale divisions | Ch. 6, §13.2–3 | ✅ |
| `Specialization` — `Specializes` closure (preorder) + comparability | OML / §6 | ✅ |
| `PropertyKindCalculus.Examples.MiniLengthWidth` (in the `Examples` lib) — length/width/height as checked facts | — | ✅ |
| `Examination` — principle / method / procedure (as defining aspects) + refinement preorder & principle-coherence | Ch. 7, 14 | ✅ |
| `PropertyKindCalculus.Examples.MiniExamination` (in the `Examples` lib) — refinement chain + examination-individuates-kinds as checked facts | — | ✅ |
| `PropertyValue` + `ValueScale` — number × reference; value-comparability equivalence + scale-gated operators | Ch. 9, 16, 10, 17 | ✅ |
| `PropertyKindCalculus.Examples.MiniValueScale` (in the `Examples` lib) — same-kind comparison + quantity-vs-nominal value + value scale as checked facts | — | ✅ |
| `Unit` — metrological unit = *chosen reference quantity of a kind*; commensurability equivalence + number-and-reference round-trip, gated to unitary kinds | Ch. 18, §13.3.3 | ✅ |
| `PropertyKindCalculus.Examples.MiniUnit` (in the `Examples` lib) — metre/centimetre commensurable, metre/kilogram not; ordinal & nominal kinds bear no unit; "5 cm" round-trips as checked facts | — | ✅ |
| `Dimension` — `dim` as the forgetful functor into PhysLib's `Dimension`; the dimension-1 disambiguation capstone (distinct kinds, one dimension) + product-multiplicativity coherence | Ch. 19 | ✅ |
| `PropertyKindCalculus.Examples.Dimension` (in the `DimensionExamples` lib) — vwc/gwc/permittivity/reflectivity all dimension-one yet pairwise-distinct kinds; dimensional algebra (area = L², speed = L·T⁻¹); forgetful-functor coherence as checked facts | — | ✅ |
| `ScaleSpanning` (in the `Dimension` lib) — scale-spanning units (R13, Finkelstein–Whitehead 2025): a third unit category beyond base and derived; the candela reduces to power and the mole to one (mechanically reducible), the kelvin's reduction is invisible to the dimension layer (Θ kept independent), the ampere is a genuine base — so scale-spanning is **not a function of dimension** | Finkelstein–Whitehead 2025 | ✅ |
| `PropertyKindCalculus.Examples.ScaleSpanning` (in the `DimensionExamples` lib) — the candela/mole reducible, the kelvin invisible, the ampere a genuine base, and the R13 capstone as checked facts | — | ✅ |
| `Interaction` — `KMul`/`KDiv` as a curated partial product, the multiplication–division round-trip, and the `dim`-homomorphism coherence capstone | Flater App. C | ✅ |
| `PropertyKindCalculus.Examples.Interaction` (in the `DimensionExamples` lib) — the SI-mechanics algebra: torque × angle = energy holds while torque × angle = torque is rejected; energy ≠ torque yet one dimension; coherence and round-trip as checked facts | — | ✅ |
| `Extensivity` — extensive kinds (additivity over a decomposition) + the n-ary aggregation capstone + a non-extensive counterexample | §13.5 | ✅ |
| `PropertyKindCalculus.Examples.MiniExtensivity` (in the `Examples` lib) — mass aggregates over a three-part assembly (3+5+7=15); volume on mixing is sub-additive (96 < 50+50) as checked facts | — | ✅ |
| `Quantity` — representation-parametric value `Quantity k R` over a `Carrier`-typed numeric carrier; same-kind addition (R4) + additivity laws proved **once** over any lawful carrier; carriers `Int` + `ℝ` (lawful), `Float` (executable) (R10) | — | ✅ |
| `PropertyKindCalculus.Examples.MiniQuantity` (in the `Examples` lib) — the same value layer at `Int` (laws transfer) and `Float` (runs, `#eval`); kind-gated add as checked facts | — | ✅ |
| `PropertyKindCalculus.QuantityReal` (in the `Dimension` lib) — the `ℝ` proof carrier: the `Carrier ℝ`/`LawfulCarrier ℝ` instances for `Quantity k R` | — | ✅ |
| `PropertyKindCalculus.Examples.QuantityReal` (in the `DimensionExamples` lib) — the core additivity laws transfer to `Quantity k ℝ` with no `ℝ`-specific proof as checked facts | — | ✅ |
| `QuantityRefinement` — the exec/spec refinement bridge: `CarrierRefinement E S` + the kind-indexed capstone `Quantity.add_refines` (a law over the lawful spec carrier descends to the exec carrier as one rounding step) (R10 capstone) | — | ✅ |
| `PropertyKindCalculus.Examples.MiniRefinement` (in the `Examples` lib) — a toy rounding carrier instantiating the bridge as checked facts | — | ✅ |
| `Torch` (in the `Torch` lib) — TorchLean instance: unconditional `CarrierRefinement FP32 ℝ` (genuine binary32 rounding) + the conditional `IEEE32Exec` executable refinement (overflow an explicit side condition); `Quantity.add_refines` realized at binary32 | — | ✅ |
| `QuantityVector` — vector/tensor quantities as a numerical array × one scalar unit (ISO 80000-2 §18, R11): pointwise `Carrier (Fin n → R)`, additivity laws transfer | — | ✅ |
| `Iso80000.References` (in the `Iso80000` lib) — references catalogue citing all 12 ISO/IEC 80000 parts by name + version | — | ✅ |
| `Iso80000.Part3` (in the `Iso80000` lib) — ISO 80000-3 *Space and time* **full catalogue** (all 42 items, 3-1.1 … 3-26.3): the length family as a specialization lattice (R2) individuated **by measurement principle** (width ≠ distance proved, not by fiat), the dimension-collision capstones (plane vs solid angle, Hz vs rad/s, velocity vs speed — same dimension, distinct kind), and all dimensional facts as checked computations | ISO 80000-3 | ✅ |
| `UnitPrefix` — SI prefixes (VIM4 §1.19) + prefixed units: the centimetre as *centi* · metre, with the §1.22 conversion factor and §1.20/§1.21 multiple/submultiple read off the projection | VIM4 | ✅ |
| `Iso80000.Part3.AreaElement` (in the `Iso80000` lib) — item 3-3's *Remarks* mathematics formalized analytically: the metric tensor (Gram), the surface element `dA = √g`, the area integral, with `(dA)² = g`, regularity, and the flat-patch correctness anchor proved | ISO 80000-3 | ✅ |
| `Iso80000.Part3.VolumeElement` (in the `Iso80000` lib) — item 3-4's *Remarks* mathematics: the 3×3 metric tensor, the volume element `dV = √g`, the volume integral, and the flat-region correctness anchor (`= |det A|`) proved | ISO 80000-3 | ✅ |
| `QuantityClassification` — verified classification (R12): the kind-law families `ProductKind` / `QuotientKind` / `ReciprocalKind` + their certificates + smart constructors; kind-laws stated to instantiate at the quantity level (axiom-free, Mathlib-free) | — | ✅ |
| `Iso80000.Part3.AreaClassification` (in the `Iso80000` lib) — R12 area instance: a rectangle's area certified as `width × height` by construction, and every certified surface area proved `≥ 0` (property transport from the defining relation) | ISO 80000-3 | ✅ |
| `Iso80000.Part3.DefiningRelations` (in the `Iso80000` lib) — the algebraic *Remarks* (curvature = 1/ρ, repetency = 1/λ, frequency = 1/T, speed = s/t, plane angle = s/r) as R12 kind-laws: the dimension *follows from* the relation (plane angle computed dimension-one because it is a ratio of two lengths) | ISO 80000-3 | ✅ |
| `Iso80000.Part4` (in the `Iso80000` lib) — ISO 80000-4 *Mechanics* **full catalogue** (all 54 items, 4-1 … 4-32): the force family as a specialization lattice (R2) individuated **by measurement principle** (static vs kinetic friction force proved distinct, not by fiat), the textbook torque-vs-energy dimension collision (N·m ≠ J, same dimension `M·L²·T⁻²`), and dimensional facts as checked computations | ISO 80000-4 | ✅ |
| `Iso80000.Part4.DefiningRelations` (in the `Iso80000` lib) — the algebraic *Remarks* as R12 kind-laws, several **cross-part**: momentum = mass × velocity and pressure = force / area build Part-4 kinds out of Part-3 kinds; efficiency computed dimension-one because it is a ratio of two powers | ISO 80000-4 | ✅ |
| `Iso80000.Part5` (in the `Iso80000` lib) — ISO 80000-5 *Thermodynamics* **full catalogue** (all 54 items, 5-1 … 5-36, every sub-suffixed item): the **scale-type** distinction between thermodynamic temperature (ratio) and Celsius temperature (interval) at the same dimension `Θ` (R6 on the standard), the entropy-vs-heat-capacity dimension collision (both `J/K`, not commensurable despite the same unit symbol), the thermodynamic-potential specialization lattice (internal energy, enthalpy, Helmholtz, Gibbs — R2), and dimensional facts as checked computations over the temperature generator | ISO 80000-5 | ✅ |
| `Iso80000.Part5.DefiningRelations` (in the `Iso80000` lib) — the algebraic *Remarks* as R12 kind-laws, several **cross-part**: specific heat capacity = heat capacity / mass and density of heat flow rate = heat flow rate / area build Part-5 kinds out of Part-4 and Part-3 kinds; the ratio of specific heats computed dimension-one because it is a ratio of two specific heat capacities | ISO 80000-5 | ✅ |
| `Iso80000.Part6` (in the `Iso80000` lib) — IEC 80000-6 *Electromagnetism* **full catalogue** (all 85 items, 6-1 … 6-62, every sub-suffixed item), the one IEC-published part: the new **electric-current** base axis (the ampere as `C·T⁻¹` over PhysLib's charge generator), the **scale-type** distinction between gauge-dependent electric potential (interval) and potential difference (ratio) at the same dimension `V` (R6), the AC power family as a specialization lattice (active/reactive/apparent power — R2) carrying three unit strings (`W`/`var`/`VA`) over one dimension, and the power/resistance dimension collisions | IEC 80000-6 | ✅ |
| `Iso80000.Part6.DefiningRelations` (in the `Iso80000` lib) — the algebraic *Remarks* as R12 kind-laws: Ohm's law (resistance = voltage / current), the power product (power = voltage × current), the conductance/admittance/permeance/resistivity reciprocals, and the power factor; the electric-current law (current = charge / time) **crosses into Part 3**; the power factor computed dimension-one because it is a ratio of two powers | IEC 80000-6 | ✅ |
| `Iso80000.Part7` (in the `Iso80000` lib) — ISO 80000-7 *Light and radiation* **full catalogue** (all 66 items, 7-1.1 … 7-37, every sub-suffixed item): the **radiant / luminous / photon trios** as distinct kinds individuated **by radiation mode** (R2), the candela and mole handled by the **scale-spanning** reduction (R13) so luminous flux ≡ radiant flux in dimension yet not in kind (the watt and the lumen not commensurable), the steradian reduced (radiant flux ≡ radiant intensity), and the **widest dimension-one family** in the series | ISO 80000-7 | ✅ |
| `Iso80000.Part7.DefiningRelations` (in the `Iso80000` lib) — the algebraic *Remarks* as R12 kind-laws, several **cross-part**: radiant flux = radiant energy / time, irradiance = radiant flux / area, radiant intensity = radiant flux / solid angle (the steradian dropping), and the luminous efficacy computed dimension-one because it is a ratio of two fluxes (the candela reducing to power) | ISO 80000-7 | ✅ |
| `Iso80000.Part8` (+ `.DefiningRelations`, in the `Iso80000` lib) — ISO 80000-8 *Acoustics* **full catalogue** (all 18 items, 8-1 … 8-17): the logarithmic **levels** collapse to dimension one (the acoustic face of R1), a genuine collision (sound pressure ≡ sound energy density, `M·L⁻¹·T⁻²`), and the **boundary case** where the dimension *does* discriminate (the two homonymous impedances); sound intensity = pressure × velocity as a kind-law | ISO 80000-8 | ✅ |
| `Iso80000.Part9` (+ `.DefiningRelations`, in the `Iso80000` lib) — ISO 80000-9 *Physical chemistry and molecular physics* **full catalogue** (all 62 items, 9-1 … 9-49): the sharpest **mole reduction** (R13) — molar mass *is* a mass, amount concentration *a number density* — the seven-fold `J/mol` collision, and a second dimension-one family; molar quantities = `X / n` kind-laws crossing to ISO 80000-3/4/5 | ISO 80000-9 | ✅ |
| `Iso80000.Part10` (+ `.DefiningRelations`, in the `Iso80000` lib) — ISO 80000-10 *Atomic and nuclear physics* **full catalogue** (all 125 items, 10-1.1 … 10-89): the **gray/sievert collision** — the standard's own two-name disambiguation of one dimension (`J/kg`, `L²·T⁻²`) — the becquerel collision (`T⁻¹`), and the widest dimension-one family in the physical parts; dose equivalent = absorbed dose × quality factor as a kind-law | ISO 80000-10 | ✅ |
| `Iso80000.Part11` (in the `Iso80000` lib) — ISO 80000-11 *Characteristic numbers* **full catalogue** (all 115 items, 11-4.1 … 11-9.2, every sub-suffixed item): the limit case of **R1** — *every* characteristic number is dimension one, so the dimension functor collapses the entire part to one point and the 115 kinds are held apart entirely **by measurement principle** (R2), including the sub-suffixed homonyms (two Froude, five Stokes, four Bejan numbers — same name, distinct kind); with parts 8, 9, 12 now mapped its `workToGoParts` is empty — every referenced part is specified | ISO 80000-11 | ✅ |
| `Iso80000.Part12` (+ `.DefiningRelations`, in the `Iso80000` lib) — ISO 80000-12 *Condensed matter physics* **full catalogue** (all 60 items, 12-1.1 … 12-38.2): the part where **collisions are the rule** — thirteen lengths, seven energies, five *named* temperatures, five carrier densities, five reciprocal lengths, each family one dimension; Seebeck = voltage / temperature and Peltier = Seebeck × temperature as kind-laws crossing to ISO 80000-5 | ISO 80000-12 | ✅ |
| `Iso80000.Part13` (+ `.DefiningRelations`, in the `Iso80000` lib) — IEC 80000-13 *Information science and technology* **full catalogue** (all 42 items, 13-1 … 13-42), the second IEC part: dimension one shared by distinct kinds with incommensurable **scale-spanning** special units (the shannon, the erlang, the bit; R13), the rates re-dimensioning to `T⁻¹`; signal energy = carrier power × bit period as a kind-law | IEC 80000-13 | ✅ |
| `Iso80000` — the remaining parts (1 *General*, 2 *Mathematics*) quantity-kinds + units | ISO/IEC 80000 | ⬜ |
| `DedicatedKind` — dedicated kind-of-property = system × component × kind-of-property (the IUPAC/IFCC `System — Component ; kind` syntax); the principled form of the vwc-vs-gwc distinctness (same target, different kind-of-property) | Dybkær Ch. 20 | ✅ |
| `PropertyKindCalculus.Examples.Dedicated` (in the `Examples` lib) — *"soil — water ; volume fraction"* vs *"… ; mass fraction"* as distinct dedicated kinds (distinct **because the kinds-of-property differ**), the systematic-term rendering, and a different-component variant as checked facts | — | ✅ |
| `Model.SI` — **subsumed by the `Iso80000` layer**: the SI base quantities are exercised against the real standard across Parts 3–13 (length / mass / time, Θ, electric current, luminous intensity & amount of substance), each with checked dimensional facts and coherent units | — | ✅ |
| `Model.SoilMoisture` — **moved to a separate downstream repository**: soil-moisture retrieval is an *application* of the calculus, kept out of PKC to avoid conflating it with the metrology / ISO-IEC focus; the dimension-one witnesses (vwc, gwc, permittivity, reflectivity) stay in `Dimension` as the `dim_not_injective` capstone | — | → repo |

## What builds today

`lake build` compiles the spine and the worked examples with **no `sorry`**,
proving: `ScaleType` is a linear order; operator availability is monotone in
scale; `Specializes` is a preorder; mutual comparability is reflexive/symmetric;
examination refinement (procedure ⊑ method ⊑ principle) is a preorder that
preserves the underlying principle, and the examination principle is a defining
aspect that individuates kinds; that a *property value* is comparable only with
values of the same kind — comparability is an equivalence relation and comparable
values share the same operator set — and that a *value scale* holds only mutually
comparable values, with operator availability inherited monotonically from the
scale layer; that a *metrological unit* is a chosen reference of a *unitary* kind
only — nominal and ordinal kinds bear none (Dybkær §9.13.4) — with commensurability
("of the same kind") an equivalence relation and the number-and-reference form
(`number × unit`) a faithful round-trip; and (in the examples) that `width`/`height` are distinct sub-kinds of
`length` — distinct *because they are examined differently*, yet mutually
comparable — with "the width of a pencil" specified as an instance, and "5 cm"
specified as a quantity value distinct in kind from a mass or a blood-group value,
measured in a centimetre that is commensurable with the metre but not the kilogram;
and that an *extensive* kind aggregates additively over a decomposition of a system
into disjoint parts — the value of the whole is the sum over the parts, proved by
induction on the decomposition (the aggregation capstone) — while *volume on mixing*
is a checked counterexample (50 mL water + 50 mL ethanol ≈ 96 mL < 100 mL), so it is
**not** extensive and assuming additivity would be unsound; and that a *quantity
value* is **parametric in its numeric representation** (R10) — `Quantity k R` is
indexed by both a kind `k` and a carrier type `R`, with same-kind addition
`Quantity k R → Quantity k R → Quantity k R` (so adding a length to a mass is a
type error), and the additivity laws (commutativity, associativity, the zero unit)
proved **once** over any lawful carrier and reused verbatim at `Int` and (in the
examples) holding for free, while the same layer runs at `Float` — a `Carrier` but
deliberately not a *lawful* one, since floating-point addition is not associative,
which is exactly the gap the exec/spec refinement bridge closes: a
`CarrierRefinement E S` packages a forgetful `toSpec` and a spec-side `round` with
the law `toSpec (x +ᴱ y) = round (toSpec x +ˢ toSpec y)`, and its kind-indexed
capstone `Quantity.add_refines` (axiom-free) lifts that to quantities, so a law
proved over the lawful carrier descends to an executable one as a single rounding
step. The same carrier-parametricity gives *vector* quantities for free
(ISO 80000-2 §18, R11): a numerical vector `Fin n → R` is a lawful carrier
pointwise, so a vector quantity is one kind with one **scalar** unit over a
numerical array — not a per-coordinate bag of number×unit values — and the
additivity laws transfer to it unchanged.

The spine also specifies Dybkær's **dedicated kind-of-property** (Ch. 20): a
generic kind-of-property bound to the *system* it characterizes and a *pertinent
component*, in the IUPAC/IFCC `System — Component ; kind-of-property` syntax (the
"NPU" form used in laboratory medicine). This gives the *principled* form of the
soil-moisture distinctness — volumetric and gravimetric water content are the
*same measurement target* (soil — water) examined as two different
kinds-of-property (volume fraction vs mass fraction), so `vwc ≠ gwc` is proved
**because the kinds-of-property differ**, with the system and component held
identical, not from differing identity strings. It is exactly the construct the
QUDV → OML/OWL2 lineage cannot express: OWL2 can record that a quantity *has* a
system and a component, but it cannot make those two dedicated kinds provably
distinct while keeping both dedicated to the same system and component.

`lake build Dimension` additionally checks the PhysLib-backed coherence layer
(this is the one library that pulls in PhysLib + Mathlib). The dimension module
proves that `dim` — the forgetful functor that sends a kind to its PhysLib
`Dimension` — is **not injective**, the motivating capstone. Volumetric and
gravimetric water content (and relative permittivity and reflectivity) are
pairwise-distinct kinds that all forget to the dimensionless `1`, so PhysLib's
`Dimension`, and any dimension-only type system, cannot tell them apart while the
kind layer keeps them distinct. The functor still preserves products (the
dimension of a product is the product of the dimensions, exponents adding), and
the dimensional algebra computes in PhysLib's group (area = L², speed = L·T⁻¹).

The interaction module then adds Flater's **kind product** as a *curated, partial*
ternary relation (`InteractionAlgebra`): an application lists the products it
sanctions, and each must be dimensionally coherent — bundling that obligation with
the relation makes the **homomorphism** `KMul k₁ k₂ k₃ → dim k₃ = dim k₁ · dim k₂`
hold by construction (this is the coherence capstone). Its division dual `KDiv` is
the product read backwards, so multiplication and division are inverse by
definition. The worked SI-mechanics algebra carries the point: `torque × angle =
energy` is sanctioned while `torque × angle = torque` is **rejected** — even
though the dimensions would balance — because dimensional coherence is necessary,
not sufficient; `energy ≠ torque` as kinds yet they share one dimension. All
sorry-free.

`lake build Dimension` also provides the **`ℝ` proof carrier** for the
representation-parametric `Quantity k R` (`PropertyKindCalculus.QuantityReal`): the
`Carrier ℝ`/`LawfulCarrier ℝ` instances, so the additivity laws proved once in the
core specialize to `Quantity k ℝ` with no `ℝ`-specific proof — the R10 payoff in one
line. The `Int` and `Float` carriers ship with the Mathlib-free core; `ℝ` lands here
because it needs Mathlib.

`lake build DimensionExamples` then checks the Mathlib-backed worked examples — the
dimension functor, the interaction algebra, the `ℝ` quantity-law transfer, the
ISO 80000 catalogue, and the ISO 80000-2 §18 vector quantity — kept under
`examples/` so that no library module carries `example`/`#eval`/`#guard` code
(the Mathlib-free spine examples stay in the `Examples` library).

`lake build Iso80000` checks the standards-grounded layer: a references catalogue
that cites each of the twelve ISO/IEC 80000 parts by name and version only — e.g.
`IEC 80000-6, Edition 2.0, 2022-11`, with no normative content reproduced — and the
**full catalogue of ISO 80000-3 *Space and time*** (all 42 items, 3-1.1 … 3-26.3),
each carrying its exact item locator as data and its dimensional facts checked in
PhysLib's group. Part 3 is where the calculus meets the real standard: its length
family (width, height, distance, radius, …) is specified as a specialization lattice
over the general length kind, each species individuated **not by fiat but by a
measurement principle** (so `width ≠ distance` is *proved*, requirement R2); its
dimension collisions (plane vs solid angle, hertz vs radian-per-second, velocity vs
speed — same dimension, distinct kind) are the dimension-1 disambiguation on standard
quantities; and selected *Remarks* are formalized as mathematics — the surface and
volume elements (`√g`), and the algebraic relations (curvature, frequency, speed,
plane angle) as R12 kind-laws where the dimension *follows from* the relation.

The same build also checks the **full catalogue of ISO 80000-4 *Mechanics*** (all 54
items, 4-1 … 4-32). Part 4 carries the calculus's two theses on textbook quantities:
the force family (weight, the friction forces, drag, …) is a specialization lattice
over the general force kind, individuated by measurement principle (so static and
kinetic friction forces are *proved* distinct kinds though dimensionally identical,
R2); the torque-versus-energy collision is the headline dimension clash — both are
`M·L²·T⁻²`, yet the newton metre is not commensurable with the joule, because the
kinds differ; and the algebraic *Remarks* are R12 kind-laws, several **crossing into
Part 3** — momentum is mass × velocity, pressure is force / area, so mechanical kinds
are built out of space-and-time kinds — with efficiency computed dimension-one because
it is a ratio of two powers.

The same build checks the **full catalogue of ISO 80000-5 *Thermodynamics*** (all 54
items, 5-1 … 5-36, every sub-suffixed item included). Part 5 brings the one axis Parts
3 and 4 could not show — the **scale type**: thermodynamic temperature and Celsius
temperature share the dimension `Θ`, yet the first is ratio-scale (the kelvin admits
`×`,`÷`) and the second only interval-scale (a ratio of Celsius temperatures is
undefined), so the two are *proved* distinct kinds by scale alone (requirement R6 on
the standard). It sharpens the dimension-collision thesis with entropy versus heat
capacity — both `J/K`, not commensurable even though their units carry the *same
symbol* — and lays out the thermodynamic potentials (internal energy, enthalpy, the
Helmholtz and Gibbs energies) as a specialization lattice over energy (R2); the
algebraic *Remarks* are R12 kind-laws, several **crossing into Parts 3 and 4** —
specific heat capacity is heat capacity / mass, the density of heat flow rate is heat
flow rate / area — with the ratio of specific heats computed dimension-one because it
is a ratio of two specific heat capacities.

The same build checks the **full catalogue of IEC 80000-6 *Electromagnetism*** (all 85
items, 6-1 … 6-62, every sub-suffixed item included) — the one IEC-published part. Part
6 brings the last SI base quantity the earlier parts did not exercise, **electric
current**: PhysLib takes electric charge `C` as its generator, so the ampere appears as
`C·T⁻¹` and every electromagnetic dimension — capacitance `C²·M⁻¹·L⁻²·T²`, resistance
`M·L²·T⁻¹·C⁻²`, magnetic flux `M·L²·T⁻¹·C⁻¹` — is a checked computation over it. It
repeats the **scale-type** thesis on electromagnetism: electric potential is
gauge-dependent (fixed only up to an additive reference), hence interval-scale, while
electric potential difference, of the same dimension `V`, is ratio-scale — *proved*
distinct kinds by scale alone (R6). And it gives the sharpest **dimension does not
classify** case yet: active, reactive, and apparent power are all `M·L²·T⁻³`, yet the
standard spends *three* unit strings on the one dimension — the watt, the var, the
volt-ampere — and arranges them as a specialization lattice over power (R2); the
algebraic *Remarks* are R12 kind-laws — Ohm's law, the power product, the reciprocal
pairs — with the electric-current law (current = charge / time) **crossing into Part 3**
and the power factor computed dimension-one because it is a ratio of two powers.

The same build checks the **full catalogue of ISO 80000-7 *Light and radiation*** (all 66
items, 7-1.1 … 7-37, every sub-suffixed item included). Part 7 reaches two SI base
quantities PhysLib's five-generator `Dimension` does not carry — **luminous intensity**
and **amount of substance** — and handles both by the Finkelstein–Whitehead
**scale-spanning** reduction (requirement **R13**, `lake build Dimension`), not by a new
generator: the candela is the dimension of *power*, the steradian and the mole are
dimension one. So the standard's **radiant / luminous / photon trios** become distinct
kinds individuated **by radiation mode** (R2) — and, the candela reducing to power,
*luminous flux ≡ radiant flux in dimension yet not in kind*, the widest **dimension does
not classify** case in the series: the watt of radiant flux and the lumen of luminous
flux are not commensurable though both are `M·L²·T⁻³`, and the steradian reduces too, so
radiant flux ≡ radiant intensity. R13 itself is the unit-layer twin of R1 — *whether a
unit is scale-spanning is not a function of its dimension*: the candela and mole are
mechanically reducible (the dimension layer sees it), the kelvin is not (Θ kept
independent, so the dimension layer cannot), and the ampere is a genuine base — proved
distinct. The algebraic *Remarks* are R12 kind-laws — radiant flux = radiant energy /
time, irradiance = flux / area, radiant intensity = flux / solid angle (the steradian
dropping) — several **crossing into Part 3**, and the luminous efficacy computed
dimension-one because it is a ratio of two fluxes.

The same build checks the **full catalogue of ISO 80000-11 *Characteristic numbers*** (all
115 items, 11-4.1 … 11-9.2, every sub-suffixed item included) — the part where **dimension
does not classify the kind** (R1) becomes *total*. A characteristic number is a
dimensionless ratio, so **every one of the 115 is dimension one**: the dimension functor
collapses the whole part to a single point, and the 115 kinds are held apart entirely **by
measurement principle** (R2), carried as each kind's examination principle. This is the
sharpest form of R2 in the series — ISO 80000-11 reuses one *name* across its
transport-phenomena clauses (the two Froude numbers, the five Stokes numbers, the four
Bejan numbers), so a sub-suffixed sibling shares *both* its name and its dimension with the
others and only the measurement principle tells them apart. Where a definition leans on a
part this library has not yet specified (ISO 80000-8 *Acoustics*, ISO 80000-9 *Physical
chemistry*, ISO 80000-12 *Condensed matter physics*), that dependency is recorded
explicitly as `workToGoParts` rather than left silent.

`lake build Torch` checks the TorchLean-backed instance of the refinement bridge —
the only library that depends on TorchLean. `FP32` (TorchLean's binary32 rounding
spec) is an *unconditional* `CarrierRefinement` of `ℝ`, so `Quantity.add_refines`
holds at genuine binary32; the *executable* `IEEE32Exec` refines `ℝ` only on the
finite, no-overflow path, with overflow carried as an explicit hypothesis rather
than silently dropped — the class of failure this rigor work exists to surface.

## Versioning

PropertyKindCalculus is a pure-Lean project, so its version is declared **once** — in
the Lean package manifest — as the single source of truth:

| Location | Field |
|---|---|
| [lakefile.lean](lakefile.lean) | `version := v!"X.Y.Z"` |

Nothing else needs to be kept in lockstep. In particular, the **blueprint reads that
same line at build time** (via its `{version}[]` Verso role in
[`Version.lean`](blueprint/PropertyKindCalculusBlueprint/Version.lean)), so the
published document's version can never drift from the source — the front-page
sentence *"PropertyKindCalculus X.Y.Z is a Lean 4 formalization…"* is generated, not
hand-typed. (Lake does not track the parent `lakefile.lean` as a dependency of the
blueprint, so after a bump an *incremental* local build may show the stale cached
value; CI builds the document fresh, and `lake clean` in `blueprint/` forces a local
refresh.)

### Bumping the version

[`scripts/bump-version.sh`](scripts/bump-version.sh) shows or bumps the version and
verifies each write:

```sh
scripts/bump-version.sh        # print the current version
scripts/bump-version.sh +p     # patch  X.Y.Z   -> X.Y.(Z+1)
scripts/bump-version.sh +m     # minor  X.Y.Z   -> X.(Y+1).0
scripts/bump-version.sh +M     # major  (X+1).0.0
```

A grep to sanity-check the declaration by hand:

```sh
grep -n '^\s*version := v!' lakefile.lean
```

### Cutting a release

After a bump, commit and tag:

```sh
scripts/bump-version.sh +m
git commit -am "chore: bump version to $(scripts/bump-version.sh)"
git tag "v$(scripts/bump-version.sh)"
```

The script keeps L4YAML's multi-site `SITES` structure, so if a language binding is
ever added (a Python or Rust package, say), its manifest becomes one extra line in
that array and the bumper will then keep all sites in lockstep and refuse to bump a
divergent set.
