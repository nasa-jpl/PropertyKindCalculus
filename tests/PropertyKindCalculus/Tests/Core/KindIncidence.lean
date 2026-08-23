/-
# Validation probes — `#kind_occurrences` (the incidence harvest)

The occurrence reading of the `Core.KindEdges` probe definitions, plus a chain over
fresh kinds (fresh so that file's pinned edge enumerations are untouched). The claims
pinned here: `combine` and `combineInline` — two witness spellings — print the *same*
occurrence line, because the edge is read off the consumer's instantiated binder type;
a `let`-bound intermediate renders by its binder name; a hypothesis witness contributes
no occurrence while its caller's discharging site does, with the helper itself as the
consuming application; a repeated operand is two incidence positions; and the
`let`-bound-witness resolution path is pinned on a hand-built expression, deterministic
whatever spelling the elaborator chose for the probe definitions.
-/
import PropertyKindCalculus.KindIncidence
import PropertyKindCalculus.Tests.Core.KindEdges

namespace PropertyKindCalculus.Tests.KindIncidence

open PropertyKindCalculus
open PropertyKindCalculus.Tests.KindEdges

-- The two witness spellings pin the same line: the edge is read off the consumer's
-- instantiated binder type, not the witness argument's spelling.
/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindEdges.combine':
alphaK · betaK → gammaK ⟨x, y⟩
-/
#guard_msgs in #kind_occurrences combine

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindEdges.combineInline':
alphaK · betaK → gammaK ⟨x, y⟩
-/
#guard_msgs in #kind_occurrences combineInline

/-- A probe kind — the chain's intermediate product. -/
def deltaK : KindOfProperty := { id := "kind-incidence probe delta", scale := .ratio }
/-- A probe kind — the chain's final quotient. -/
def epsilonK : KindOfProperty := { id := "kind-incidence probe epsilon", scale := .ratio }

/-- A two-step chain: the product lands in a `let`, and the quotient consumes the
binder — ordered incidence (`t` is the numerator) with the intermediate named. -/
def chainQ {R : Type} [Mul R] [Div R] (x : Quantity alphaK R) (y : Quantity betaK R) :
    Quantity epsilonK R :=
  let t := Quantity.mul (ProductKind.ofRatio alphaK betaK deltaK) x y
  Quantity.div (QuotientKind.ofRatio deltaK betaK epsilonK) t y

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.chainQ':
alphaK · betaK → deltaK ⟨x, y⟩
deltaK / betaK → epsilonK ⟨t, y⟩
-/
#guard_msgs in #kind_occurrences chainQ

/-- The helper's witness is a *hypothesis* — lambda-bound, assumed: no occurrence
here. -/
def scaleBy {R : Type} [Mul R] (h : ProductKind alphaK betaK deltaK)
    (x : Quantity alphaK R) (y : Quantity betaK R) : Quantity deltaK R :=
  Quantity.mul h x y

/-- info: no inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.scaleBy' -/
#guard_msgs in #kind_occurrences scaleBy

/-- The caller discharges the license, so the occurrence sits here — and the *helper* is
the consuming application: the reader is generic over consumers, not a list of smart
constructors. -/
def scaled {R : Type} [Mul R] (x : Quantity alphaK R) (y : Quantity betaK R) :
    Quantity deltaK R :=
  scaleBy (ProductKind.ofRatio alphaK betaK deltaK) x y

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.scaled':
alphaK · betaK → deltaK ⟨x, y⟩
-/
#guard_msgs in #kind_occurrences scaled

/-- A repeated operand is two incidence positions: the same quantity fills numerator and
denominator. -/
def selfRatio {R : Type} [Div R] (q : Quantity alphaK R) : Quantity epsilonK R :=
  Quantity.div (QuotientKind.ofRatio alphaK alphaK epsilonK) q q

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.selfRatio':
alphaK / alphaK → epsilonK ⟨q, q⟩
-/
#guard_msgs in #kind_occurrences selfRatio

/-- The unary power family: one operand, the exponent printed as edge data. -/
def rootOf {R : Type} [MathCarrierExt R] (a : Quantity alphaK R) : Quantity betaK R :=
  Quantity.rpow (PowerKind.ofRatio (1 / 2) alphaK betaK) a

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.rootOf':
alphaK ^ 1 / 2 → betaK ⟨a⟩
-/
#guard_msgs in #kind_occurrences rootOf

/- The occurrence collector in isolation, on a hand-built `let`-bound-witness
expression — the binder-resolution path (`witnessAuthored` through the `let`, operand
`.bvar`s named from the walk context), deterministic regardless of the elaborator's
choices for the probe definitions above. -/
/-- info: alphaK · betaK → gammaK ⟨x, y⟩ -/
#guard_msgs in
#eval show Lean.MetaM Unit from do
  let kc : Lean.Name → Lean.Expr := fun n => Lean.mkConst n
  let qty : Lean.Expr → Lean.Expr := fun k => Lean.mkApp2 (kc ``Quantity) k (kc ``Nat)
  let pk := Lean.mkApp3 (kc ``ProductKind) (kc ``alphaK) (kc ``betaK) (kc ``gammaK)
  let app := Lean.mkApp8 (kc ``Quantity.mul) (kc ``Nat) (kc ``instMulNat)
    (kc ``alphaK) (kc ``betaK) (kc ``gammaK)
    (.bvar 0) (.bvar 2) (.bvar 1)
  let body := Lean.Expr.letE `w pk (kc ``alpha_beta_gamma) app false
  let e := Lean.mkLambda `x .default (qty (kc ``alphaK))
    (Lean.mkLambda `y .default (qty (kc ``betaK)) body)
  let env ← Lean.getEnv
  for o in ← PropertyKindCalculus.KindEdges.collectOccurrences env
      (PropertyKindCalculus.KindIncidence.operandCarriers env) e do
    Lean.logInfo o.render

end PropertyKindCalculus.Tests.KindIncidence
