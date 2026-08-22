/-
# Validation probes — `#kind_edges` (the witness-enumeration command)

The trust model says a model's kind algebra is exactly its authored witnesses, judged by
enumeration (`QuantityClassification`, "The trust model"; the command is the kind-algebra
analog of `#print axioms`). This probe authors one edge in each of the three styles the
command must find — a named witness theorem, a call-site witness inside a definition body
(on both of the elaborator's spellings: lifted into a `._proof_N` auxiliary found by the
type scan, or left inline and read off the producer application by the body scan), and an
operator-table instance — and pins the complete sorted enumeration with `#guard_msgs`. A
probe kind with no authored edges pins the empty report. The body-scan collector is
additionally probed in isolation, on a hand-built expression, so its reading does not
depend on which spelling the elaborator happens to choose for any probe definition.
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

/-- Style 3 — an operator-table registration: the edge is the instance's type. Note the
instance's *value* holds a producer application too; the body scan skips instances
(`bodyScannable`), which is why the pin below shows exactly one `tableEntry` line. -/
instance tableEntry : KindMul alphaK betaK gammaK := ⟨ProductKind.ofRatio _ _ _⟩

/-- Style 2, the other spelling — a call-site witness authored in a `let`-bound,
`Id.run do` shape the elaborator has been observed to leave inline (unlifted). The pin
below is stable *whichever* spelling this toolchain chooses: a lifted auxiliary's type
and the inline producer application render the same line, attributed to this
definition. -/
def combineInline {R : Type} [Mul R] (x : Quantity alphaK R) (y : Quantity betaK R)
    (h : alphaK.IsRational := by rfl) : Quantity gammaK R := Id.run do
  let w : ProductKind alphaK betaK gammaK :=
    ProductKind.ofRatio alphaK betaK gammaK h
  return Quantity.mul w x y

/--
info: authored kind edges mentioning 'PropertyKindCalculus.Tests.KindEdges.gammaK':
PropertyKindCalculus.Tests.KindEdges.alpha_beta_gamma: alphaK · betaK → gammaK
PropertyKindCalculus.Tests.KindEdges.combine: alphaK · betaK → gammaK
PropertyKindCalculus.Tests.KindEdges.combineInline: alphaK · betaK → gammaK
PropertyKindCalculus.Tests.KindEdges.tableEntry: [table] alphaK · betaK → gammaK
-/
#guard_msgs in #kind_edges gammaK

/-- info: no authored kind edges mention 'PropertyKindCalculus.Tests.KindEdges.orphanK' -/
#guard_msgs in #kind_edges orphanK

/- The body-scan collector in isolation, on a hand-built expression — deterministic
regardless of the elaborator's lifting choice for the probe definitions above. The proof
arguments are fillers (the collector reads only the kind positions), and the producer sits
under a binder to exercise the recursion. -/
/-- info: alphaK · betaK → gammaK -/
#guard_msgs in
#eval show Lean.MetaM Unit from do
  let kc : Lean.Name → Lean.Expr := fun n => Lean.mkConst n
  let a := kc ``alphaK
  let app := Lean.mkApp6 (kc ``ProductKind.ofRatio) a (kc ``betaK) (kc ``gammaK) a a a
  let wrapped := Lean.mkLambda `x .default (kc ``Nat) app
  for (spec, args) in PropertyKindCalculus.KindEdges.collectProducedEdges wrapped #[] do
    let pps ← args.mapM fun e => return toString (← Lean.Meta.ppExpr e)
    Lean.logInfo (spec.fmt pps)

end PropertyKindCalculus.Tests.KindEdges
