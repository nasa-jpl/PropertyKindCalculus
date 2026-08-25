/-
# PropertyKindCalculus.Tests — the validation-test suite

A build-time regression suite that checks the two properties a "machine-checked" claim rests on but
that `lake build` does not verify on its own, for **every** verifiable requirement (R1–R18):

  * **inhabitation / non-vacuity** — each requirement's theorem is applied to a *concrete* witness
    whose premises are discharged by `decide`/`rfl`/a constructor, so a theorem that were vacuously
    true (an empty universal, an unsatisfiable premise) could not compile here. This is the
    "validate the target is inhabited, not merely well-formed" discipline, carried over from the
    L4YAML workstream and placed in `tests/` rather than inline in the library.
  * **axiom profile** — each requirement theorem's `#print axioms` is pinned with `#guard_msgs`, so
    a proof silently relocated behind a `sorry` (which emits *no* warning on its caller — only the
    axiom set reveals it) is caught. No probe here depends on `sorryAx`.

Organized by dependency tier, matching the layering of the requirement catalogue:

  * `Tests.Core` — the Mathlib-free core spine (R2, R3, R4, R6, R8, R9, R10, R11, R12, R16, R17,
    R19), grouped by the catalogue's `RequirementGroup`;
  * `Tests.Dimension` — the PhysLib/Mathlib-backed dimension layer (R1, R5, R7, R13, R17-ℝ);
  * `Tests.Uncertainty` — the Mathlib/Torch-backed uncertainty layer (R14, R15, R18);
  * `Tests.Torch` — the TorchLean-backed `Torch` library's kind layer (the kinded fused
    forms), driven at a host stub carrier so it needs no GPU;
  * `Tests.ForMathlib` — the Mathlib staging area's digraph/quiver theory: classical theorems
    applied to concrete witnesses, decidability instances driven by `decide`, axiom profiles
    pinned.

Every probe file is imported by its tier index and, through the `Tests` library's `.andSubmodules`
glob, also built directly by `lake build Tests` — an *unindexed* probe would still be built here, so
it cannot silently go unchecked. CI builds this library (and the layers it reaches into), so all
sixteen verifiable requirements are CI-enforced, not just the nine in the core spine.
-/

import PropertyKindCalculus.Tests.Core
import PropertyKindCalculus.Tests.Dimension
import PropertyKindCalculus.Tests.ForMathlib
import PropertyKindCalculus.Tests.Uncertainty
import PropertyKindCalculus.Tests.Torch
