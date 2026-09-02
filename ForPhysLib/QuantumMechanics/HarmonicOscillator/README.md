# The pilot directory: `Physlib/QuantumMechanics/HarmonicOscillator`, mirrored

The first directory of the three-directory campaign (see
[`PLAN.md`](../../PLAN.md#the-three-directory-campaign)): the quantum harmonic
oscillator, taken whole, with the PhysLib files as the literal reference. Every module
here *imports* the PhysLib module it mirrors and builds the kinded layer on top —
nothing upstream changes, or even imports this.

The pilot went first because it could falsify: its quantities are partial linear
operators on a Hilbert space (`Q.HS →ₗ.[ℂ] Q.HS`), its scalars are `ℂ`, its
characteristic length is built through half-integer-dimension intermediates, and its
`ξEquiv` rescaling is textbook nondimensionalization. None of that had faced the
calculus. The verdict: **no core change forced** — one carrier constructor
(`Carrier.ofZeroAdd`) and the measurand/observable vocabulary went *upstream to PKC*
as generic API; nothing quantum-specific remained in either.

## The files

| file | ladder rung | what it holds |
|---|---|---|
| `Feasibility.lean` | before the ladder | F1–F4 as build artifacts: the operator carrier stands up, only the radicand-first ξ survives kinding, the SI numeral pinned, the eigenvalues kinded per mode |
| `Kinds.lean` | Stage 0 | 18 kinds — 10 proved against PKC's ISO 80000 catalogue, 8 local mints each saying why the standard does not list it; the three-energy collision decided |
| `Metrology.lean` | Stage 1 | 16 `DimensionedKind` pairings, the Stage-0 lookup proved by `decide`/`rfl`, ten authored edge laws, coverage pinned clean |
| `Kinded.lean` | Stage 2 | the re-authoring: the licensed-fold eigenvalue, the radicand-first ξ, the Born density, spacings vs the silent reference, the kinded TISE (M-T1–M-T3) |
| `Measurand.lean` | Stage 2 | M-T4 realized: the Hamiltonian as PKC's `Observable` at `𝕜 = ℂ`, identified as a `Measurand` with the eigenvalue set as indications |
| `Operators.lean` | Stage 3 | the kind algebra as `KindMul`/`KindDiv` table entries: `*` and `/` elaborate through the table, unregistered pairs refuse |
| `Audits.lean` | Stage 4 | the directory namespace under CI: the 20-site boundary audit pinned, silent clean/ratchet/dimensional gates, the interior gated empty, the ingest boundary measured |
| `Orthonormality.lean` | the first patch | upstream's `@[sorryful]` `eigenstates_orthonormal`, discharged — statement verbatim, sorry-free |
| `Heisenberg.lean` | the second patch | `ℏ/2 ≤ σ_x σ_p` proved for every normalized Schwartz state from upstream's own Robertson bound and CCR; the ground state's `σ_x = ξᵢ/√2` by the Gaussian second moment and `σ_p = ℏ/(√2 ξᵢ)` by differentiating the Gaussian, so saturation `σ_x σ_p = ℏ/2` is exact; the bound kinded through the `length · momentum → action` entry |
| `HarmonicOscillator.checked_by.yaml` | Stage 4 | the API-map delta, keyed by the upstream `TODO` texts |

## The cost line

What the layer costs, measured — every number quoting a build artifact at this commit.

| | count | artifact |
|---|---|---|
| kinds | 18 — 10 catalogue-checked (9 verbatim lookups + the length species by the catalogue's own constructor), 8 local mints | `Kinds.lean`; the `decide`/`rfl` blocks in `Metrology.lean` |
| dimensional pairings | 16, plus 2 kinds unpaired on purpose (their dimensions `L⁻ᵈ`/`Lᵈ` are the model's parameter; the coherence is the parametric theorem `bornDensity_dim_coherent`) | `Metrology.lean` |
| kind edges | 21 — 10 authored laws, 10 operator-table entries (7 in Stage 3, 3 probe-era), 1 aggregation license (`±`) | `#kind_dimensional_coverage` pins in `Metrology.lean`/`Operators.lean`; the silent directory-wide `#kind_dimensional_clean` in `Audits.lean` |
| join entries | 1 — `T̂ + V̂` at mechanical energy; `T̂ + p̂²` refused | `Feasibility.lean` (F1a, F1c) |
| boundary sites | 20 — 15 attested, 3 raw ingest mints, 2 erasure-only; by tier: 12 ingest, 5 crossings, 1 constant, 1 carrier-vocabulary, 1 emission | the pinned `#kind_boundary_audit` in `Audits.lean` |
| unkinded surface | interior: 0 positions (gated); ingest boundary: 15 naked positions, all the oscillator structure, its occupation labels, coordinate indices, its Hilbert space, its operator domains, or the one emitted `ℝ` | the `#kind_unkinded` ledgers in `Audits.lean` |
| lines | 2,099 total, of which 994 are code (the rest is documentation, including the pinned audit reports); the mirrored source is 1,727 total / 1,085 code, none of which changed | `wc -l`; comment-stripped count |
| proof debt | 0 `sorry`; every theorem here at `propext, Classical.choice, Quot.sound`; 1 upstream `@[sorryful]` discharged and 1 theorem upstream never stated (`heisenberg_uncertainty`) proved | `#print axioms` |

Two cost notes the table cannot carry. First, the ceremony per declaration is small
and front-loaded: a kinded quantity is one `def` with one attestation or mint, its
erasure to the source form is one theorem (usually `rfl`), and existing PhysLib
theorems close kinded goals verbatim (`ξ_sq`, `eigenEnergy_strictMono`,
`hamiltonian`'s definition). Second, the catalogue does most of the Stage-0 work: 10
of 18 kinds are lookups the build re-checks, not designs.

## The findings

Each finding is a fact about the *source* that only became statable, or only became
checked, with the layer on.

1. **Only one of the library's two ξ spellings survives kinding.** The 1D file's
   radicand-first `ξ = √(ℏ/(m·ω))` passes through two registered edges and one
   attested root; the `d`-dimensional file's root-first `ξᵢ = √ℏ/(√m·√ωᵢ)` has
   half-integer-dimension intermediates named by no kind, on purpose. The respelling
   is PhysLib's own `ξ_sq`, in one line (`xi_radicand_first`).
2. **The wavefunction itself carries the half-power rule.** `|ψ|²` is the kinded
   object (a probability density over position); ψ at `L^(−d/2)` is its attested
   root, and the `1/√ξᵢ` in each `eigenCoeff` is that root's trace in the source.
   `∫|ψₙ|² = 1` is now a theorem, consumed from the discharged orthonormality.
3. **The eigenvalues read against a silent reference.** `V(0) = 0` at equilibrium is
   declared by nothing but the shape of `potentialFunction`'s definition — pinned as
   `potential_zero_at_equilibrium`. The level *spacings* (`ℏωᵢ` through the
   scale-gated subtraction) cancel it; the zero-point energy is the one number that
   reads on it.
4. **The SI numeral is a silent unit commitment.** `Constants.ℏ` is a positive real
   whose J·s reading lives in docstring prose (pinned in F3) — and the 1D
   oscillator's docstring promises "three real parameters … a value of Planck's
   constant ℏ" while the structure carries two fields and takes ℏ from the global
   constant.
5. **Mathlib's `SMul` is where kinds go unseen.** `kineticOperator = (2m)⁻¹ • p̂²`
   rides a dimensionful scalar across `SMul` (F1d); the TISE's right-hand side
   `E • ψ` is the same crossing in the subject's defining equation. Both are attested
   once and counted by the audit — measured, not prevented.
6. **The dimension-1 and energy conflations are real and decidable.** Three kinds sit
   at dimension one (quantum number, dimensionless coordinate, probability) and three
   at `M·L²·T⁻²` (kinetic, potential, mechanical energy); nothing dimensional
   separates them, the kind layer does, by `decide`.
7. **The audit adjudicated a crossing the author had misplaced.** `ξEquiv`'s kinded
   reading consumes the raw oscillator (the `ξᵢ` scale factors ride inside `Q`), so
   the interior contract refused it and it sits on the measured boundary — the Stage-4
   gate doing its job during authoring, not after.
8. **Definitional equality does not make one vocabulary for instance search.** The
   probe's catalogue lookups and Stage 0's literals are the same kinds by `rfl`, but
   the operator table is found only at the spelling an instance head is written in —
   so Stage 3 spells each head at the kinds the quantities actually carry.
9. **Upstream owns every part of Heisenberg's inequality and has never joined them.**
   The abstract Robertson bound, the canonical commutator, and the self-adjoint
   position operator all exist upstream, but the bound is instantiated nowhere and
   `ℏ/2` appears nowhere else in the library. `heisenberg_uncertainty` is that join —
   for every normalized Schwartz state — and the ground state saturates it exactly:
   `σ_x = ξᵢ/√2` by the same Hermite machinery as the orthonormality discharge, and
   `σ_p = ℏ/(√2 ξᵢ)` because `𝐩` sends the Gaussian to `(iℏ/ξᵢ²) ·` its `𝐱`-image,
   so the momentum moments are the position moments already computed.

## The metrological TODO slate

`Eigenstates.lean` opens with six analysis TODOs; each casts a metrological shadow the
analysis statement cannot express, because the vocabulary to state it does not exist
without the kind layer. The four shadows are delivered here as M-T1–M-T4 (`Kinded.lean`
and `Measurand.lean`), and the mirror also *pays*: `Orthonormality.lean` discharges the
first upstream TODO outright, statement verbatim; `Heisenberg.lean` proves a theorem
the upstream TODO list could not even request (`ℏ/2 ≤ σ_x σ_p`, from parts the library
already owned); and the kinded TISE and the indication predicate hold the statements
of two more, waiting on the upstream analysis.
The offer upstream is a human's to make
([AI-POLICY §3.1](https://github.com/leanprover-community/physlib/blob/master/AI-POLICY.md)).
