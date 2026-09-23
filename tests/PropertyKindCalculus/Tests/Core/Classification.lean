/-
# Validation probes — classification (R12)

Inhabitation and axiom-profile probes for verified classification. R12's content is that a
classification is a *certificate*, not an assertion — so the probe both (i) builds a quantity
through the product kind-law and confirms its certificate holds by construction, and (ii) shows,
as the Rule-2 boundary, that a bare-tagged quantity of the *same kind* fails the same
certificate. A certificate everything satisfied would classify nothing.
-/

module

public import PropertyKindCalculus
meta import PropertyKindCalculus

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.Classification

open PropertyKindCalculus

/-- Speed, time, length — three ratio kinds. -/
def speedK  : KindOfProperty := { id := "speed",  scale := .ratio }
def timeK   : KindOfProperty := { id := "time",   scale := .ratio }
def lengthK : KindOfProperty := { id := "length", scale := .ratio }

/-- The kind-law `length = speed × time` (all three ratio-scale). -/
theorem lengthLaw : ProductKind speedK timeK lengthK := ProductKind.ofRatio speedK timeK lengthK

/-- A concrete speed and time. -/
def v : Quantity speedK Int := ⟨60⟩
def τ : Quantity timeK  Int := ⟨2⟩

/-- A length built *through* the kind-law — classified `length` by construction. -/
def d : Quantity lengthK Int := Quantity.mul lengthLaw v τ

-- Inhabitation: the certificate is satisfied by construction on a concrete product, and the
-- magnitude computes (60 × 2 = 120) — the classification is a checked fact about real values.
theorem r12_certified : d.IsProduct lengthLaw v τ := Quantity.mul_isProduct lengthLaw v τ

#guard d.magnitude == 120

-- Boundary (Rule 2): a length asserted by fiat (`⟨999⟩`) — same kind, arbitrary magnitude —
-- *fails* the certificate against the same factors. So the certificate discriminates: it is not
-- vacuously true of every `Quantity lengthK`.
def dFake : Quantity lengthK Int := ⟨999⟩

theorem r12_fake_uncertified : ¬ dFake.IsProduct lengthLaw v τ := by
  unfold Quantity.IsProduct
  decide

/-- info: 'PropertyKindCalculus.Quantity.mul_isProduct' does not depend on any axioms -/
#guard_msgs in #print axioms Quantity.mul_isProduct

end PropertyKindCalculus.Tests.Classification

end Blanket
