/-
`PropertyKindCalculus.Uncertainty.EvidenceKinds` — **the kind vocabulary of the evidence and
conformity layer**: every quantity `Evidence.lean` and `Conformity.lean` touch that is not the
measurand's own, plus the laws that license their arithmetic.

WHY KINDS HERE AT ALL. The measurand's estimate and its standard uncertainty carry the
measurand's kind, and `Budget.lean` already says so. Everything *else* in a conformity assessment
is dimension one — a probability, a coverage factor, a count of indications, a number of degrees
of freedom — so a dimension-only type system collapses all four, and the collapse lands exactly
where the confusion is most expensive. `k = Φ⁻¹(1 − p)` takes a probability and returns a
coverage factor; `t_p(ν)` takes a probability *and* a number of degrees of freedom and returns a
coverage factor; `ν = n − 1` takes a count of indications and returns degrees of freedom. On a
`Float`-typed API every one of those arguments fits every one of those slots, and every swap
produces a plausible number: a 0.95 read as a coverage factor, a `ν` read as a risk. This module
is the instrument that survives the dimensional collapse, and the layer that assesses conformity
must not be the one written below its own discipline.

FOUR KINDS, NOT ONE. They are deliberately not one "dimensionless" kind, and they are not
mutually comparable in Dybkær's sense: no function in this library ever adds a probability to a
coverage factor, or compares a count of indications against a number of degrees of freedom. Where
two of them *are* related — `ν` from `n`, a factor from a probability — the relation is a named
crossing or an authored law below, written where it is used, never an implicit conversion.

WHAT STAYS OUT. `Sampling.lean`'s rational approximations (`normalCDF`, `studentTQuantile`) take
and return bare `Float`s on purpose: they are the numerics layer, the analogue of
`MathCarrier.sqrt`, and kinding a polynomial evaluation would state a metrological claim about an
approximation coefficient. The kinds start one level up, at the first function whose arguments
mean something.
-/

module

public import PropertyKindCalculus.Kind
public import PropertyKindCalculus.Quantity
public import PropertyKindCalculus.QuantityClassification
public import PropertyKindCalculus.Bounds

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Uncertainty

open PropertyKindCalculus

/-! ### The kinds -/

/-- **Probability** — a coverage probability, a specific consumer's or producer's risk, a target
risk. ONE kind for all of them: they are mutually comparable in Dybkær's sense, and this library
genuinely subtracts and compares them against each other (a coverage probability `P` and its tail
`1 − P`; a realized risk against the target risk it was supposed to hold). Role is a distinction
between *individuals*, carried by parameter names. -/
def probability : KindOfProperty :=
  { id := "probability", scale := .ratio }

/-- **Coverage factor** — the pure number multiplying a standard uncertainty to obtain an expanded
uncertainty or a guard band (GUM 2.3.6, `k`). Deliberately NOT a probability, even though the two
are related by `k = Φ⁻¹(1 − p)` and appear in the same expression: `1.96` and `0.95` are both
dimension one, both plausible in either slot, and reading one as the other is the single most
likely silent error in this arithmetic. -/
def coverageFactor : KindOfProperty :=
  { id := "coverage factor", scale := .ratio }

/-- **Degrees of freedom** `ν` — what qualifies a standard uncertainty, and what fixes the
coverage factor at a given probability (GUM G.3). Ratio-scale and *not* integer-valued:
Welch–Satterthwaite returns a non-integer, and an unqualified uncertainty is stated at `ν = ∞`. -/
def degreesOfFreedom : KindOfProperty :=
  { id := "degrees of freedom", scale := .ratio }

/-- **Count of repeated indications** `n` — how many readings a Type A evaluation was made from
(GUM 4.2). Deliberately distinct from `degreesOfFreedom`, which it differs from by exactly one for
a simple mean: `s/√n` divides by the count and `s²` divides by the degrees of freedom, so the two
appear one line apart in the same formula and swapping them is a silent error of `√(n/(n−1))`. -/
def indicationCount : KindOfProperty :=
  { id := "repeated indication count", scale := .ratio }

/-! ### The distinctness facts

Each names a swap that would otherwise typecheck, and each is the reason its kind exists rather
than being folded into a neighbour. -/

/-- A coverage factor is not a probability. The swap that motivated this module: `k = Φ⁻¹(1 − p)`
consumes one and produces the other, so on a `Float` API each of `1.96` and `0.95` fits the
other's slot and returns a number that looks like an answer. -/
theorem coverageFactor_ne_probability : coverageFactor ≠ probability := by decide

/-- A coverage factor is not a number of degrees of freedom — `t_p(ν)` takes the second and
returns the first, one function, both dimension one. -/
theorem coverageFactor_ne_degreesOfFreedom : coverageFactor ≠ degreesOfFreedom := by decide

/-- `ν` is not `n`. They differ by one for a simple mean and appear one line apart in GUM 4.2. -/
theorem degreesOfFreedom_ne_indicationCount : degreesOfFreedom ≠ indicationCount := by decide

/-! ### The named probabilities

Coverage probabilities that appear by name in the GUM's own tables, as *values* of the
`probability` kind rather than as literals at their call sites. -/

/-- The 95 % coverage probability — GUM Table G.2's first column. -/
def p95 : Quantity probability Float := ⟨0.95⟩

/-- The 99 % coverage probability — GUM Table G.2's second column. -/
def p99 : Quantity probability Float := ⟨0.99⟩

/-- Certainty. The unit of the `probability` kind, and what a coverage probability is subtracted
from to obtain its tail. -/
def certainty : Quantity probability Float := ⟨1.0⟩

/-! ### The laws and crossings

Every one of these is an *authored claim*, in the sense of `QuantityClassification.lean`'s trust
model: the checker verifies everything given the witnesses, and the witnesses are reviewed. They
are collected here, in full, so the layer's kind algebra is the finite list below. -/

/-- **The expansion law**: a coverage factor times a standard uncertainty is a quantity of the
measurand's own kind. This is what makes `U = k·u` and `g = k·u` legitimate constructions rather
than re-stampings — the coverage factor is dimension one *in the specific role of expanding an
uncertainty*, and that role is what the law records.

The measurand's kind must be ratio-scale, which is the metrological precondition for a standard
uncertainty in the first place. (For an interval-scale measurand — a Celsius temperature — the
evidence is stated at the kind of its *differences*, which is ratio-scale; the law applies
there.) -/
theorem expansionLaw (k : KindOfProperty) (hk : k.IsRational) :
    ProductKind coverageFactor k k :=
  ProductKind.ofRatio coverageFactor k k rfl hk hk

/-- **A ratio-scale measurand admits differences.** The licence a guard band needs to be
subtracted from a tolerance limit, derived from the same `IsRational` an evidence record already
carries rather than demanded again at every call site. Ratio is the richest scale, so it allows
everything the poorer ones do (`Scale.lean`'s monotonicity); this is that fact, at the one place
this layer needs it. -/
theorem differenceOfRational {k : KindOfProperty} (hk : k.IsRational) : DifferenceKind k :=
  DifferenceKind.ofScale (by rw [(hk : k.scale = .ratio)]; trivial)

/-- **A ratio-scale measurand admits order.** The licence a *limit* needs to exist at all — a
bound presupposes a side to be on. -/
theorem orderOfRational {k : KindOfProperty} (hk : k.IsRational) : OrderKind k :=
  OrderKind.ofScale (by rw [(hk : k.scale = .ratio)]; trivial)

/-- **The band-reading law**: a guard band divided by the standard uncertainty it qualifies — two
quantities of the measurand's own kind — is a coverage factor. The converse of `expansionLaw`, and
the licence for asking of an existing margin "how many `u` is this?". -/
theorem bandReadingLaw (k : KindOfProperty) (hk : k.IsRational) :
    QuotientKind k k coverageFactor :=
  QuotientKind.ofRatio k k coverageFactor hk hk rfl

/-- **The cost-ratio crossing**: the break-even risk of a decision is the ratio of the cost of a
wrong rejection to the total cost of being wrong — two quantities of one cost kind, whose quotient
this law declares to be a *probability*.

The strongest claim in this module, and the one most worth writing out: nothing about a ratio of
two wall-clock durations makes it a probability. It becomes one only through the decision-theoretic
argument that at the break-even point the two expected costs are equal, and that argument is what
the witness stands for. Requiring both costs to share `kc` is the other half — a wall-clock cost
divided by a monetary one is a number with no meaning, and exactly the kind that looks fine in a
spreadsheet. -/
theorem costRatioIsRisk (kc : KindOfProperty) (hc : kc.IsRational) :
    QuotientKind kc kc probability :=
  QuotientKind.ofRatio kc kc probability hc hc rfl

/-- **The crossing from a count of indications to degrees of freedom**: `ν = n − 1` for the mean
of `n` indications (GUM 4.2.2). Written as a named crossing and not as arithmetic, because it is
not arithmetic: the two kinds are distinct, nothing licenses subtracting a pure `1` from a count
to obtain degrees of freedom, and *which* function of `n` the degrees of freedom are is a property
of the estimator (it is `n − 1` for a mean, and something else for a fit with more parameters).
Naming it is what leaves room for the other estimators to arrive as siblings rather than as edits
to a subtraction. -/
def dofOfMean (n : Quantity indicationCount Float) : Quantity degreesOfFreedom Float :=
  ⟨n.magnitude - 1.0⟩

@[simp] theorem dofOfMean_magnitude (n : Quantity indicationCount Float) :
    (dofOfMean n).magnitude = n.magnitude - 1.0 := rfl

/-- **Degrees of freedom for an uncertainty that is not qualified by a finite number of them**
(GUM G.4.3: a Type B `u` whose bound is reliably known is taken as `ν = ∞`). Written as a float
infinity deliberately: it is the value at which Welch–Satterthwaite's `uᵢ⁴/νᵢ` term vanishes and
the `t` factor becomes the Gaussian one, so both behaviours come out of the arithmetic instead of
out of a case analysis that could disagree with it. -/
def dofUnbounded : Quantity degreesOfFreedom Float := ⟨1.0 / 0.0⟩

end PropertyKindCalculus.Uncertainty

end -- pkc-blanket-expose
end -- pkc-blanket
