/-
# ForPhysLib.CaseStudies

The worked case studies backing [the proposal](../ForPhysLib/README.md) — each one a system
typed several ways and scored against the requirements of `ForPhysLib/REQUIREMENTS.md`, with
every verdict a build artifact rather than prose.

  * `HarmonicOscillator` — the first, occasioned by
    [physlib#1579](https://github.com/leanprover-community/physlib/pull/1579): four honest
    attempts at typing the same physics (plain reals, PhysLib `WithDim`, Buckingham-π object
    tagging, PKC), each run end to end against MR1–MR19, plus the appended MR32.

A case study is a *directory*, prose beside the sources that back each claim: its `README.md`
links to the requirement headings it exercises and never restates them.
-/
import ForPhysLib.CaseStudies.HarmonicOscillator
