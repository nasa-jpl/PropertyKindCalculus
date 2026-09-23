/-
# The harmonic oscillator as a metrology benchmark

Aggregator for the four honest attempts at typing the same physics, scored against the
requirement list in
`ForPhysLib/CaseStudies/HarmonicOscillator/README.md`.

The occasion is [physlib#1579](https://github.com/leanprover-community/physlib/pull/1579),
where the harmonic oscillator was proposed as a first place to apply PhysLib's
`Dimension`/`Unit` layer. It is a good choice — good enough that it also shows what
dimensional analysis structurally cannot do.

**One attempt, one file, every requirement.** Each attempt file runs the whole list MR1–MR19 (plus the appended MR32),
tier by tier, so it reads end to end as a single account of a single idea. The only
cross-attempt module is the scorecard, because a head-to-head comparison is the one thing that
cannot live inside either head.

  * `Attempt1Reals`     — plain reals in a bundle (PhysLib's status quo), with the
    structure-bundling defence stated at full strength and then shown to end at the first
    function boundary. Wins authoring ergonomics outright and permanently.
  * `Attempt2Dimension` — PhysLib `Dimension` / `WithDim`: the PR's proposal, which wins the
    whole of Tier 1 and cannot reach Tier 2 or 3, because `WithDim`'s only discrimination is
    equality of dimensions.
  * `Attempt3Tagged`    — Buckingham-π object tagging on a basis-parametric `Dimension B`.
    Wins object identity, and pays for it: the total mass becomes inexpressible, the
    frequency ratio keeps a residual tag, and the phase `ωt` is no longer dimensionless.
  * `Attempt4Pkc`       — a kind layer *above* the dimension layer: `KindOfProperty` (scale
    type, examination principle), `IndividualQuantity o k R` (object in the type), `Extensive`
    (licensed aggregation), `DedicatedKind` (`System — Component ; kind`), the carrier axis of
    `Quantity k R`, and `InFrame`'s frame/variance indices.
  * `Scorecard`         — the head-to-head verdicts, re-derived so the README's table cannot
    drift from the files; plus the one comparison that is inherently cross-attempt, the four
    authorings of `V = m·ω²·x²` and the proof that they compute the same number.

The conclusion the benchmark supports is narrow: PhysLib's `Dimension` is the right bottom
layer — PKC consumes it as `DimensionedKind.toDimension` — and the harmonic oscillator
demonstrates that something has to sit above it.
-/

module

public import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt1Reals
public import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt2Dimension
public import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt3Tagged
public import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt4Pkc
public import ForPhysLib.CaseStudies.HarmonicOscillator.Scorecard

@[expose] public section



