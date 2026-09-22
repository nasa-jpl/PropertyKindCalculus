/-
`PropertyKindCalculus.Uncertainty.Adequacy.Significance` — **Stage 3.4: the Axis-U significance
yardstick** (`UNCERTAINTY.md` §4.4, §6). This is the module that *closes the coupling* between the
two areas of the workstream: uncertainty propagation (Area 1) and numerical adequacy (Area 2).

Until here the two areas were exercised from *separate* inputs: `DegenhardtSensitivity` fed the
autograd sensitivities `cᵢ` into GUM/Willink, while `AdequacySwamping` passed the `Adequacy` carrier
*absolute* uncertainties chosen by hand (`Adequacy.input 1.0 1.0`). The design (`UNCERTAINTY.md`
§4.4) makes both areas read the **same** descriptor `InputDist`: its `moments` supply the standard
uncertainty `uᵢ = √variance` and its `support` supplies the input box, while the autograd `cᵢ`
supply the *significance scale* `cᵢ·uᵢ` — the contribution of input `i`'s uncertainty to the output,
in output units. A contribution below half a ulp of the accumulator is numerically invisible; the
`Adequacy` carrier flags it (`Adequacy.Soundness.verdict_sound`, A3). So *"is this model
floating-point-adequate?"* is answered **at the scale the uncertainty descriptor itself defines** —
one descriptor, both areas, no extra inputs.

The mechanism is again the write-once discipline (P1): a genuine WO1 kernel
`f {α} [NumCarrier α] (x₁ … xₙ : α) : α` is instantiated *twice* from one source — at
`TapeBuilder .scalar` (to read the `cᵢ` by reverse-mode autograd, via `Sensitivity`) and at
`Adequacy` (to run the adequacy verdict, seeded from the same descriptor). `analyze` performs both
in one pass and returns the coefficients, the per-input significance scales `cᵢ·uᵢ`, and the verdict.

Honest scope. The *soundness* of the flag is inherited — it is the Stage-3/3.1 A3 verdict
(`verdict_sound`), here merely **fed** the autograd-propagated significance scale; Stage 3.4 adds no
new rigor, it wires the two areas together. The `Adequacy` carrier runs over host `Float`
(uncertifiable FFI, `UNCERTAINTY.md` §4.6 F); the sound magnitude-range propagation over the
`support` box is the `RInterval` grounding already re-exposed by `Adequacy.Fp32Grounding`
(`interval_add_sound`), the `ℝ`-rigor tie referenced here rather than re-run.

**Metrological kinding.** The GUM budget quantities carry their kinds via `Uncertainty.Budget`: an
input uncertainty is a `Quantity kᵢ`, a sensitivity a `Quantity (kₒ/kᵢ)`, a contribution and the
combined uncertainty a `Quantity kₒ`. `analyzeQ` produces a kind-typed `CouplingResultQ kₒ`, whose
fields cannot be swapped or mixed (unlike two naked `List Float`). The model itself stays *carrier-raw*
— it runs kind-erased on the tape and the adequacy carrier; the kinds are the caller-declared
metrological overlay on the *budget*, gated by `ProductKind kₛ kᵢ kₒ` (the GUM units cancellation).
Depends on TorchLean (the tape carrier, via `Sensitivity`); lives in `UncertaintyRigor` alongside it.
-/

module

public import PropertyKindCalculus.Uncertainty.Adequacy
public import PropertyKindCalculus.Uncertainty.Sensitivity
public import PropertyKindCalculus.Uncertainty.Budget

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open Spec TorchLean TorchLean.Tensor
open PropertyKindCalculus (Quantity ProductKind KindOfProperty)
open PropertyKindCalculus.Paradigm (TapeBuilder NumCarrier)

namespace PropertyKindCalculus.Uncertainty.Adequacy

open PropertyKindCalculus.Uncertainty (InputDist MomentData stdUnc stdUncQ sensitivityQ
  contributionQ combinedQ)

/-! ## Seeding the adequacy carrier from the input descriptor (Area 2 ← the descriptor)

The `Adequacy` carrier is `Float` by nature (the executable path). Seeding it from the descriptor is
therefore the *erasure* boundary: the input's magnitude is its mean, its carried uncertainty is the
carrier `stdUnc = √variance` of `Budget` — the same formula the kinded `stdUncQ` overlays. -/

/-- Seed one `Adequacy` input from an `InputDist` descriptor: its `value` is the mean `E(Xᵢ)`, its
carried `unc` is the standard uncertainty `uᵢ = √variance` (`Budget.stdUnc`, the `Float` erasure the
kinded `stdUncQ` overlays). Lets the *same* descriptor drive the adequacy analysis — no hand-picked
uncertainty. -/
def ofInputDist (d : InputDist Float) : Adequacy :=
  input d.moments.mean (stdUnc d.moments)

/-- Seed the full positional input list of a write-once model from the descriptors (Area 2's inputs,
from the one descriptor list Area 1 also reads). -/
def adequacyInputs (inputs : List (InputDist Float)) : List Adequacy :=
  inputs.map ofInputDist

/-- The **magnitude scale of a bounded input's support box** `[lo, hi]`: `max |lo| |hi|`, the largest
value the model can present for this input (`none` for an unbounded family such as a normal). This is
the executable reading of *"`InputDist.support` supplies the input box"* (`UNCERTAINTY.md` §4.4); the
*sound* interval propagation of that box is the `RInterval` grounding of `Adequacy.Fp32Grounding`. -/
def supportMagnitude (d : InputDist Float) : Option Float :=
  d.support.map fun (lo, hi) => max lo.abs hi.abs

/-! ## One-pass coupling of the two areas — kind-typed GUM budget -/

/-- A **write-once positional list-kernel**, instantiable at every numeric carrier. A genuine WO1
kernel `f {α} [NumCarrier α] (x₁ … xₙ : α) : α` becomes a `ListModel` by
`fun | [x₁, …, xₙ] => f x₁ … xₙ | _ => 0` — the same source `analyzeQ` runs at both
`TapeBuilder .scalar` (for the `cᵢ`) and `Adequacy` (for the verdict), kind-erased in both. -/
abbrev ListModel := {α : Type} → [NumCarrier α] → List α → α

/-- The **kind-typed** result of coupling the two areas from one descriptor list, at output kind `kₒ`:
the GUM uncertainty budget — per-input `contributions` `uᵢ(y)` and the `combined` standard uncertainty
`u_c(y)`, *both* `Quantity kₒ Float` — and the numerical-adequacy `verdict`. The former two swappable
`List Float` fields are now a `List (Quantity kₒ Float)` and a `Quantity kₒ Float`; swapping them, or
mixing a contribution with an input uncertainty (`Quantity kᵢ`), is a type error. -/
structure CouplingResultQ (kO : KindOfProperty) where
  /-- Per-input GUM contributions `uᵢ(y) = |cᵢ|·u(xᵢ)`, in output units (`Quantity kₒ`). -/
  contributions : List (Quantity kO Float)
  /-- Combined standard uncertainty `u_c(y) = √(Σ uᵢ(y)²)`, in output units. -/
  combined : Quantity kO Float
  /-- The adequacy verdict of the same model, seeded from the same descriptors (Area 2). -/
  verdict : Adequacy

/-- **The Stage-3.4 driver (kind-typed).** For a model whose inputs share a kind `kᵢ` and whose output
has kind `kₒ`, with the sensitivity kind `kₛ` satisfying `kₛ·kᵢ = kₒ` (the `ProductKind` witness — the
GUM units cancellation), instantiate the model *twice* from one source: at `TapeBuilder .scalar` to
read the sensitivities `cᵢ` by one reverse pass, and at `Adequacy` to run the numerical-adequacy
verdict on inputs seeded from the *same* descriptors. The `cᵢ` are stamped `Quantity kₛ` at the
boundary (`sensitivityQ`) and folded with the kinded input uncertainties (`stdUncQ`) into the kinded
GUM budget (`contributionQ`/`combinedQ`). One descriptor, both areas, every quantity kinded. -/
def analyzeQ {kO kI kS : KindOfProperty} (h : ProductKind kS kI kO)
    (model : ListModel) (inputs : List (InputDist Float)) :
    Except String (CouplingResultQ kO) := do
  let cs ← Sensitivity.gradient (model (α := TapeBuilder Shape.scalar))
    (inputs.map fun d => d.moments.mean)
  let contribs := (cs.zip inputs).map fun (c, d) =>
    contributionQ h (sensitivityQ (kS := kS) c) (stdUncQ (k := kI) d.moments)
  let verdict := model (α := Adequacy) (adequacyInputs inputs)
  pure { contributions := contribs, combined := combinedQ contribs, verdict := verdict }

/-! ## Seeding faithfulness — the carrier reads exactly the descriptor -/

/-- The seeded value is the descriptor's mean (Area 2 sees `E(Xᵢ)`). -/
@[simp] theorem ofInputDist_value (d : InputDist Float) :
    (ofInputDist d).value = d.moments.mean := rfl

/-- The seeded uncertainty is the descriptor's standard uncertainty `√variance` — the `Float` erasure
of the kinded `stdUncQ` the budget authors. -/
@[simp] theorem ofInputDist_unc (d : InputDist Float) :
    (ofInputDist d).unc = stdUnc d.moments := rfl

/-- A freshly-seeded input starts with an empty report (no site is charged until an operation
runs). -/
@[simp] theorem ofInputDist_report (d : InputDist Float) :
    (ofInputDist d).report = {} := rfl

end PropertyKindCalculus.Uncertainty.Adequacy

end -- pkc-blanket-expose
end -- pkc-blanket
