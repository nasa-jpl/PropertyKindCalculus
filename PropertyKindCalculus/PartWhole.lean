/-
# PartWhole — a portion and the total it is taken from, as roles

A count of the valid pixels in a block and the block's own pixel count are the same kind
of quantity: both are counts over the same window, they add and compare meaningfully, and
splitting them into two kinds would be false — a portion of a thing is a quantity of the
same kind as the thing. That is exactly what leaves `f (part whole : Quantity k R)` open
to a call with its arguments the wrong way round, and the failure is silent: the division
that reads "what fraction of the total is this" returns a number greater than one instead
of one less than one, and every consumer downstream carries on.

This module puts the two roles into the type, as `Bounds` does for endpoints and `Axis`
for an extent and a position:

  * `Part k R` / `Whole k R` — one-field role wrappers over `Quantity k R`, field `q` as
    in every role wrapper here.
  * `Part.WithinWhole` is the only relation between them, and its arguments have different
    types, so "the total is at most the portion" is not a statement this API can make.
  * `Part.fractionOf` is the **eliminator**, and the reason the pair is worth having: the
    consumer that wants "how much of the whole is this" never writes the division, and
    therefore cannot write it upside down. The result is a quantity of a *different* kind
    — dividing a portion by its total is what creates the "fraction of total" role, which
    is why the operation is licensed by a `QuotientKind` edge rather than being free.

**Why not a bound.** A part is not an `UpperBound`-style constraint on the whole and the
whole is not a limit the part is checked against: `Bounds` carries *conformity* and
*saturation* questions about a threshold, and neither is what a portion asks of its total.
The shared fact — that a part does not exceed its whole — is a consequence of the
mereology, not a specification anyone imposes, and stating it through a bound would put a
requirement where a description belongs.

**What the roles do not claim.** That the parts of a whole are exhaustive, disjoint, or
even known: `Whole` names the total a portion is read against, nothing more. A vocabulary
for a *partition* — the parts summing to their whole — is a further commitment, and the
kernels this serves do not make it (a valid-pixel count and a block's total are one part
against one whole, with the complement unnamed).
-/

module

public import PropertyKindCalculus.QuantityClassification

public section -- pkc-blanket

namespace PropertyKindCalculus

/-- **A portion, as a role** — a quantity read as part of a larger total of its own kind:
the finite pixels within a reduction block, one tap's raw weight within a kernel's sum.
Distinct in *type* from the total it is taken from, which is what stops a call site from
handing over the two the wrong way round; the same *kind*, because a portion of a thing is
a quantity of the same kind as the thing. -/
structure Part (k : KindOfProperty) (R : Type) where
  /-- The portion quantity. -/
  q : Quantity k R

/-- **The total a portion is read against, as a role** — the dual of `Part`. Its own type
for the reason `LowerBound` is not `UpperBound`: the pair is exactly what a call site can
get backwards, and the arithmetic that follows gives no sign when it has. -/
structure Whole (k : KindOfProperty) (R : Type) where
  /-- The total quantity. -/
  q : Quantity k R

namespace Part

variable {k : KindOfProperty} {R : Type}

/-- **A role survives a representation cast** — the counterpart of `Quantity.castCarrier`
for this role. A portion counted at `Nat` and read at `Float` is the same portion of the
same total; what changes is how the number is written, which is precisely what
`castCarrier` is for. The eliminator below needs both sides at one carrier, so a pair born
as counts reaches it through this. -/
def castCarrier {S : Type} (f : R → S) (p : Part k R) : Part k S := ⟨p.q.castCarrier f⟩

@[simp] theorem castCarrier_magnitude {S : Type} (f : R → S) (p : Part k R) :
    (p.castCarrier f).q.magnitude = f p.q.magnitude := by rw [castCarrier]; rfl

/-- **The directional Prop former**: the portion does not exceed the total it is taken
from. The only relation statable between the two roles — with the part on the left, where
the mereology puts it — so the reversed reading is unwritable rather than merely wrong. -/
def WithinWhole [LE R] (p : Part k R) (w : Whole k R) : Prop :=
  p.q.magnitude ≤ w.q.magnitude

/-- **Executable** `part ≤ whole` — the `Bool` counterpart of `WithinWhole`, gated on the
carrier having decidable order (host scalars have it, batched deployment carriers do not).
The check a producer runs where the two numbers are born, not a fact threaded downstream. -/
def withinWhole [LE R] [∀ x y : R, Decidable (x ≤ y)] (p : Part k R) (w : Whole k R) :
    Bool :=
  decide (p.q.magnitude ≤ w.q.magnitude)

@[simp] theorem withinWhole_eq_true [LE R] [∀ x y : R, Decidable (x ≤ y)]
    (p : Part k R) (w : Whole k R) : p.withinWhole w = true ↔ p.WithinWhole w := by
  simp [withinWhole, WithinWhole]

/-- **The eliminator — what fraction of the whole this part is.** The division is written
once, here, in the only order the roles admit, so every consumer that needs a coverage, a
normalized weight, or a share gets it without spelling a quotient it could spell backwards.

The result kind is a *different* kind, and deliberately: dividing a portion by its own
total is precisely the operation that creates a "fraction of total" role out of two
quantities that carried no such meaning separately, so it is licensed by a `QuotientKind`
edge (ratio-scale on both operands and on the quotient — the autoParam discharges it for
concrete kinds) rather than being free. -/
def fractionOf [Div R] [ScalarCarrier R] (kFrac : KindOfProperty) (p : Part k R) (w : Whole k R)
    (h : QuotientKind k k kFrac := by exact QuotientKind.ofRatio _ _ _) : Quantity kFrac R :=
  Quantity.div h p.q w.q

@[simp] theorem fractionOf_magnitude [Div R] [ScalarCarrier R] (kFrac : KindOfProperty)
    (p : Part k R) (w : Whole k R) (h : QuotientKind k k kFrac) :
    (p.fractionOf kFrac w h).magnitude = p.q.magnitude / w.q.magnitude := by rw [fractionOf]; rfl

end Part

namespace Whole

variable {k : KindOfProperty} {R : Type}

/-- **A role survives a representation cast** — `Part.castCarrier`'s dual, and the reason
it exists: the eliminator takes the portion and the total at one carrier, so a pair born as
counts crosses to `Float` in the same step on both sides, in its own role on each. -/
def castCarrier {S : Type} (f : R → S) (w : Whole k R) : Whole k S := ⟨w.q.castCarrier f⟩

@[simp] theorem castCarrier_magnitude {S : Type} (f : R → S) (w : Whole k R) :
    (w.castCarrier f).q.magnitude = f w.q.magnitude := by rw [castCarrier]; rfl

end Whole

end PropertyKindCalculus

end -- pkc-blanket
