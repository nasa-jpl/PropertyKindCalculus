/-
`PropertyKindCalculus.Uncertainty.Budget` — the **kinded GUM uncertainty budget** (`UNCERTAINTY.md`
§4.4). The GUM propagation `u_c(y)² = Σ (∂f/∂xᵢ)²·u(xᵢ)²` traffics in three metrologically-distinct
quantities that a naked `Float` conflates. This module gives each its own kind, so the type system
carries the metrological intent and forbids the conflations:

  * an **input standard uncertainty** `u(xᵢ) = √variance` — *inherits its input's kind* `kᵢ` (the
    uncertainty of a length is a length): `stdUncQ : … → Quantity kᵢ Float`;
  * a **sensitivity coefficient** `cᵢ = ∂f/∂xᵢ` — a *quotient* kind `kₛ = kₒ/kᵢ` (output-per-input):
    `sensitivityQ : Float → Quantity kₛ Float` stamps the (kind-blind) autograd magnitude with its
    static kind at the boundary;
  * an **output contribution** `uᵢ(y) = |cᵢ|·u(xᵢ)` — the *output* kind `kₒ`, obtained by the
    dimensionally-gated `contributionQ`. Its `ProductKind kₛ kᵢ kₒ` argument is the GUM
    units-cancellation `(kₒ/kᵢ)·kᵢ = kₒ` made a **typechecking obligation** — you cannot form a
    contribution unless the sensitivity and input kinds multiply into the output kind.

The combined standard uncertainty `u_c(y) = √(Σ uᵢ(y)²)` (`combinedQ`) is then the quadrature of the
contributions, which are *homogeneous* at `kₒ` — so it, too, is a `Quantity kₒ Float`. A
`CouplingResult`'s former two swappable `List Float` fields become a `List (Quantity kₒ Float)` and a
`Quantity kₒ Float`: swapping them, or mixing a contribution with an input uncertainty, is now a type
error.

Honest scope. `ProductKind.ofRatio` is deliberately *liberal* — it signs any ratio-scale triple
(`QuantityClassification.lean`), so the `ProductKind kₛ kᵢ kₒ` gate enforces the *shape* of the GUM
law and forbids un-sanctioned kind mixing, but the caller still asserts that `kₛ` really is `kₒ/kᵢ`
(the curated-edge discipline of the whole calculus). The kinds are the write-once overlay.

**Carrier-generic.** The budget is a write-once model over `[NumCarrier R]` (the two-axis discipline:
one budget × any carrier), not a `Float`-only computation. `NumCarrier` extends `MathCarrier`, so
`sqrt`/`abs`/`+`/`×` are all available — the same primitives run at `ℝ` (to *prove* budget laws), at
`Float`/`FP32` (execution), or at the `Adequacy` carrier (to adequacy-check the budget's *own*
quadrature — does `√(Σ uᵢ²)` silently drop a small contribution?). `combinedQ` computes on the carrier
and re-stamps the output kind, leaving the transient squared kind `kₒ²` an erasure detail; the
autograd source that feeds `sensitivityQ` is inherently `Float` (that specialization is `analyzeQ`'s,
not the budget's). Mathlib- and TorchLean-free.
-/

module

public import PropertyKindCalculus.OperatorTable
public import PropertyKindCalculus.Paradigm.NumCarrier
public import PropertyKindCalculus.Uncertainty.InputDist

@[expose] public section Blanket

namespace PropertyKindCalculus.Uncertainty

open PropertyKindCalculus (Quantity ProductKind KindOfProperty MathCarrier)
open PropertyKindCalculus.Paradigm (NumCarrier)

variable {R : Type} [NumCarrier R]

/-- The **standard uncertainty** `u = √variance` (VIM 2.30; the second cumulant `κ₂ = u²`), at any
numeric carrier `R`. The single source of the formula: the kinded overlay `stdUncQ` and the `Float`
seeding of the (kind-erased) adequacy carrier both read it. -/
def stdUnc (m : MomentData R) : R := MathCarrier.sqrt m.variance

/-- **Input standard uncertainty** `u(xᵢ)` at the *input's* kind `k` — the uncertainty of a
`Quantity k` quantity is itself a `Quantity k`. The write-once overlay of the carrier `stdUnc`. -/
def stdUncQ {k : KindOfProperty} (m : MomentData R) : Quantity k R :=
  ⟨stdUnc m⟩

@[simp] theorem stdUncQ_magnitude {k : KindOfProperty} (m : MomentData R) :
    (stdUncQ (k := k) m).magnitude = stdUnc m := rfl

/-- **Stamp a raw derivative magnitude as a sensitivity coefficient** at kind `kₛ = kₒ/kᵢ`. This is
the boundary at which a kind-blind number (the reverse-mode tape's, at `Float`; a symbolic
derivative's, at `ℝ`) acquires its (static, from the model's signature) metrological *kind* — the
honest place the erasure is re-dressed, analogous to an ingest mint. -/
def sensitivityQ {kS : KindOfProperty} (c : R) : Quantity kS R := ⟨c⟩

omit [NumCarrier R] in
@[simp] theorem sensitivityQ_magnitude {kS : KindOfProperty} (c : R) :
    (sensitivityQ (kS := kS) c).magnitude = c := rfl

/-- **GUM uncertainty contribution** `uᵢ(y) = |cᵢ|·u(xᵢ)`, at the *output* kind `kₒ`. The
`ProductKind kₛ kᵢ kₒ` witness is the metrological gate: the term typechecks only when the sensitivity
kind `kₛ` times the input kind `kᵢ` lands in the output kind `kₒ` — the GUM units cancellation
`(kₒ/kᵢ)·kᵢ = kₒ`. Built through the kind-preserving `Quantity.abs` and the named `Quantity.mul`, so
the product certificate transports. -/
def contributionQ {kO kI kS : KindOfProperty} (h : ProductKind kS kI kO)
    (c : Quantity kS R) (u : Quantity kI R) : Quantity kO R :=
  Quantity.mul h (Quantity.abs c) u

@[simp] theorem contributionQ_magnitude {kO kI kS : KindOfProperty} (h : ProductKind kS kI kO)
    (c : Quantity kS R) (u : Quantity kI R) :
    (contributionQ h c u).magnitude = MathCarrier.abs c.magnitude * u.magnitude := rfl

/-- **Combined standard uncertainty** `u_c(y) = √(Σ uᵢ(y)²)` — the quadrature of the (output-kind,
homogeneous) contributions, so itself a `Quantity kₒ R`. Summing in quadrature *is* the independence
assumption of GUM (§4.4). Computes on the carrier `R` and re-stamps `kₒ`; run at `R := Adequacy` it
adequacy-checks its own sum of squares. -/
def combinedQ {kO : KindOfProperty} (contribs : List (Quantity kO R)) : Quantity kO R :=
  ⟨MathCarrier.sqrt (contribs.foldl (fun acc x => acc + x.magnitude * x.magnitude) 0)⟩

@[simp] theorem combinedQ_magnitude {kO : KindOfProperty} (contribs : List (Quantity kO R)) :
    (combinedQ contribs).magnitude
      = MathCarrier.sqrt (contribs.foldl (fun acc x => acc + x.magnitude * x.magnitude) 0) := rfl

end PropertyKindCalculus.Uncertainty

end Blanket
