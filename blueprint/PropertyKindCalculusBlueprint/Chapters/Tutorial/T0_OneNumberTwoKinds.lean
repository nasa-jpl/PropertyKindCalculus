import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References

-- A tutorial chapter: no nodes, no `{deftech}`. The code blocks are SubVerso anchors quoted
-- live from `examples/Tutorial/HarmonicOscillatorSquare.lean` (the `Tutorial` library); the
-- blueprint build refuses a block whose text no longer matches the anchored region.

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "Tutorial.HarmonicOscillatorSquare"

#doc (Manual) "T0 — One number, two kinds" =>
%%%
tag := "tutorial-t0"
%%%

Nothing to write yet. Read three lines that a dimension-and-units library accepts and this
calculus refuses, each with the error the elaborator prints. The names (`Body.A`, `mA`,
`angFreqK`, …) are declared in the next chapter; here only the shape matters.

_Comparability._ Angular frequency and frequency have one dimension, reciprocal time, and a
dimension layer makes them one thing; the ForPhysLib case study proves that identity and
scores every attempt that rests on dimension alone as failing the requirement. Here the two
are distinct values of {tech}[kind-of-property] and no dimension is in sight:

```anchor sameDimension
/- One dimension, two kinds (MR4): angular frequency and frequency share 1/time, so a
dimension layer identifies them; the kind keeps them apart with no dimension in sight. -/
/--
error: Application type mismatch: The argument
  f
has type
  IndividualQuantity Body.A frequencyK Int
but is expected to have type
  IndividualQuantity Body.A angFreqK Int
in the application
  IndividualQuantity.add ⋯ ω f
-/
#guard_msgs in
example := fun (ω : IndividualQuantity Body.A angFreqK Int)
    (f : IndividualQuantity Body.A frequencyK Int) =>
  IndividualQuantity.add DifferenceKind.ofScale ω f
```

_Bearer._ Two bodies' masses have one kind and one unit, and a units library adds them
without comment. Here the body is a type index of the quantity, so the sum is not a term,
and B's mass cannot be passed where A's is expected:

```anchor bottomEdge
/- Bottom edge: masses of two bodies do not add. -/
/--
error: Application type mismatch: The argument
  mB
has type
  IndividualQuantity Body.B massK Int
but is expected to have type
  IndividualQuantity Body.A massK Int
in the application
  IndividualQuantity.add ⋯ mA mB
-/
#guard_msgs in
example := IndividualQuantity.add DifferenceKind.ofScale mA mB
/- Nor stiffnesses of two springs. -/
/--
error: Application type mismatch: The argument
  kC
has type
  IndividualQuantity Spring.kC stiffnessK Int
but is expected to have type
  IndividualQuantity Spring.kA stiffnessK Int
in the application
  IndividualQuantity.add ⋯ kA kC
-/
#guard_msgs in
example := IndividualQuantity.add DifferenceKind.ofScale kA kC
/- B's mass cannot stand in for A's. -/
/--
error: Type mismatch
  mB
has type
  IndividualQuantity Body.B massK Int
but is expected to have type
  IndividualQuantity Body.A massK Int
-/
#guard_msgs in
example : IndividualQuantity Body.A massK Int := mB
```

_Composition._ Summing the bodies' angular frequencies over the pair is a sum of two
quantities of one kind, and a units library adds them too. Here a sum over a whole goes
through an assembly license keyed by the sort of the whole, and the registry carries no
license for angular frequency over a coupled pair, so the term does not exist:

```anchor angFreq
/- Angular frequency carries no license for the pair, so `2 + 4` is not a term. -/
/--
error: failed to synthesize instance of type class
  Assembles pairS angFreqK

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example := fun (f : (b : Body) →
      IndividualQuantity (Composite.part (σ := pairS) (Sum.inl b : Part)) angFreqK Int) =>
  assemble (k := angFreqK) pairS Composite.whole
    (fun b : Body => Composite.part (Sum.inl b)) bodies f
```

What the weaker systems do with the same three lines is the case study's scorecard, row by
row. Attempt 1 is bare reals, attempt 2 is PhysLib's dimension type, attempt 3 tags the
object into the type by hand, and attempt 4 is this calculus:

:::table +header
* - requirement
  - 1 · reals
  - 2 · dimension type
  - 3 · tagged
  - 4 · this calculus
* - MR4 — same-dimension kinds stay apart
  - ❌
  - ❌
  - ❌
  - ✅
* - MR7 — object identity
  - ⚠️
  - ❌
  - ✅
  - ✅
* - MR8 — aggregation licensed per kind, in both directions
  - ❌
  - ❌
  - ❌
  - ✅
:::

The third row is the discriminating one. Attempt 3 buys object identity by making "being
oscillator A" part of the type, and pays with the sum it can no longer write: addable and
distinguishable become each other's negation. The chapters that follow show the line that
dissolves the dilemma — the object and the kind are two independent indices of one quantity.

Reference: {ref "foundations"}[Foundations] for the square, {ref "dimension"}[Dimension as a
forgetful functor] for why dimension cannot decide comparability, and
`ForPhysLib/CaseStudies/HarmonicOscillator/README.md` for the full scorecard.
