/-
# Validation probes — `#kind_edges` (the witness-enumeration command)

The trust model says a model's kind algebra is exactly its authored witnesses, judged by
enumeration (`QuantityClassification`, "The trust model"; the command is the kind-algebra
analog of `#print axioms`). This probe authors one edge in each of the three styles the
command must find — a named witness theorem, a call-site witness inside a definition body
(reachable only through the lifted `._proof_N` auxiliary's *type*), and an operator-table
instance — and pins the complete sorted enumeration with `#guard_msgs`. A probe kind with
no authored edges pins the empty report.
-/
import PropertyKindCalculus.KindEdges

namespace PropertyKindCalculus.Tests.KindEdges

open PropertyKindCalculus

/-- A probe kind — the first factor. -/
def alphaK : KindOfProperty := { id := "kind-edges probe alpha", scale := .ratio }
/-- A probe kind — the second factor. -/
def betaK : KindOfProperty := { id := "kind-edges probe beta", scale := .ratio }
/-- A probe kind — the product, whose authored registry the probe pins. -/
def gammaK : KindOfProperty := { id := "kind-edges probe gamma", scale := .ratio }
/-- A probe kind with no authored edges at all. -/
def orphanK : KindOfProperty := { id := "kind-edges probe orphan", scale := .ratio }

/-- Style 1 — a named witness theorem: the edge is the theorem's type. -/
theorem alpha_beta_gamma : ProductKind alphaK betaK gammaK := ProductKind.ofRatio _ _ _

/-- Style 2 — a call-site witness: the edge is written inline in the body and lifted by
Lean into `combine._proof_1 : ProductKind alphaK betaK gammaK`, found via its type. -/
def combine {R : Type} [Mul R] (x : Quantity alphaK R) (y : Quantity betaK R) :
    Quantity gammaK R :=
  Quantity.mul (ProductKind.ofRatio alphaK betaK gammaK) x y

/-- Style 3 — an operator-table registration: the edge is the instance's type. -/
instance tableEntry : KindMul alphaK betaK gammaK := ⟨ProductKind.ofRatio _ _ _⟩

/--
info: authored kind edges mentioning 'PropertyKindCalculus.Tests.KindEdges.gammaK':
PropertyKindCalculus.Tests.KindEdges.alpha_beta_gamma: alphaK · betaK → gammaK
PropertyKindCalculus.Tests.KindEdges.combine: alphaK · betaK → gammaK
PropertyKindCalculus.Tests.KindEdges.tableEntry: [table] alphaK · betaK → gammaK
-/
#guard_msgs in #kind_edges gammaK

/-- info: no authored kind edges mention 'PropertyKindCalculus.Tests.KindEdges.orphanK' -/
#guard_msgs in #kind_edges orphanK

end PropertyKindCalculus.Tests.KindEdges
