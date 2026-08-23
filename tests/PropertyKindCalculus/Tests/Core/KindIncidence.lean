/-
# Validation probes — the step harvest (`#kind_occurrences` / `#kind_ports` / `#kind_graph`)

The occurrence reading of the `Core.KindEdges` probe definitions, plus a chain over
fresh kinds (fresh so that file's pinned edge enumerations are untouched). The claims
pinned here: `combine` and `combineInline` — two witness spellings — print the *same*
occurrence line, because the edge is read off the consumer's instantiated binder type;
a `let`-bound intermediate renders by its binder name; a hypothesis witness contributes
no enumerated occurrence while its caller's discharging site does, with the helper
itself as the consuming application; a repeated operand is two incidence positions; and
the `let`-bound-witness resolution path is pinned on a hand-built expression,
deterministic whatever spelling the elaborator chose for the probe definitions.

The port reading is pinned on the same definitions plus configuration-flavored ones:
a hypothesis binder is not a port, so a helper has an interface even where it has no
occurrences; a kind-generic signature renders its kind variables by binder name; a
`@[kindConst]` constant the body reads is a configuration port — read twice it is *one*
port while the occurrence keeps both incidence positions, and the two readings name the
node identically; outputs are the result type's product components with positions kept,
so an un-kinded component leaves a visible gap; a signature with no carrier-typed
positions pins the empty report.

The graph reading closes the file — both renderings above are projections of the one
constructed object, and these pins are the spot check. `#kind_graph` pins the wiring:
the identity wire reaching a pass-through's and a tuple's output ports; an assumed
license wiring the helper's own graph; a nested producer landing on a synthesized node
the outer operand names exactly; a `[table]` product read through one level of instance
unfolding, authored at the registered instance and assumed at a threaded instance
binder; attested / gated / declared-constant sources carrying the audit's tiers; an
erasure marking its exit; a raw mint refused — and `#kind_graph_decide` has the kernel
re-derive a harvested verdict as a `decide` theorem.
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

/-- The helper's witness is a *hypothesis* — lambda-bound, assumed: no enumerated
occurrence here (the graph below wires it, marked). -/
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

/- The occurrence walk in isolation, on a hand-built `let`-bound-witness expression —
the binder-resolution path (`witnessAuthored` through the `let`, operand `.bvar`s named
from the walk context), deterministic regardless of the elaborator's choices for the
probe definitions above. -/
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
  for o in ← PropertyKindCalculus.KindIncidence.occurrencesOfValue env
      (PropertyKindCalculus.KindIncidence.operandCarriers env) e do
    Lean.logInfo o.render

/-! ## The port harvest — `#kind_ports` -/

-- The chain's interface: two inputs, one output; the `let`-bound intermediate `t` is
-- interior (an occurrence datum above), not a port.
/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.chainQ':
input x : alphaK
input y : betaK
output result : epsilonK
-/
#guard_msgs in #kind_ports chainQ

-- The hypothesis binder is not a port: `scaleBy` has an interface (unlike its
-- occurrence report, which is empty — the license is discharged by its caller).
/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.scaleBy':
input x : alphaK
input y : betaK
output result : deltaK
-/
#guard_msgs in #kind_ports scaleBy

/-- A kind-generic step, the pilot chain's shape: the ports render the kind *variable*
by its binder name. -/
def genericLerp {k : KindOfProperty} (tab : Quantity k (Array Float)) :
    Quantity k (Array Float) :=
  tab

/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.genericLerp':
input tab : k
output result : k
-/
#guard_msgs in #kind_ports genericLerp

/-- A declared constant mint — the configuration value the port probes below read. -/
@[kindConst] def refQ : Quantity deltaK Nat := ⟨2⟩

/-- A step reading a configuration constant: `refQ` enters as a config port, and the
occurrence pin below names the same node as an operand — the two readings agree. -/
def normalized (y : Quantity betaK Nat) : Quantity epsilonK Nat :=
  Quantity.div (QuotientKind.ofRatio deltaK betaK epsilonK) refQ y

/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.normalized':
input y : betaK
config refQ : deltaK
output result : epsilonK
-/
#guard_msgs in #kind_ports normalized

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.normalized':
deltaK / betaK → epsilonK ⟨refQ, y⟩
-/
#guard_msgs in #kind_occurrences normalized

/-- A configuration constant read twice: *one* port — a port is an interface node —
while the occurrence below keeps both incidence positions. -/
def selfRef : Quantity epsilonK Nat :=
  Quantity.div (QuotientKind.ofRatio deltaK deltaK epsilonK) refQ refQ

/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.selfRef':
config refQ : deltaK
output result : epsilonK
-/
#guard_msgs in #kind_ports selfRef

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.selfRef':
deltaK / deltaK → epsilonK ⟨refQ, refQ⟩
-/
#guard_msgs in #kind_occurrences selfRef

/-- A multi-output step: the result type's product components are the output positions.
The bare `Nat` component states no kind and is no port — the numbering keeps its gap
visible. -/
def swapPair {R : Type} (x : Quantity alphaK R) (y : Quantity betaK R) :
    Quantity betaK R × Nat × Quantity alphaK R :=
  (y, 0, x)

/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.swapPair':
input x : alphaK
input y : betaK
output result.1 : betaK
output result.3 : alphaK
-/
#guard_msgs in #kind_ports swapPair

/-- A signature with no carrier-typed positions at all. -/
def plainAdd (a b : Nat) : Nat := a + b

/-- info: no kind ports in 'PropertyKindCalculus.Tests.KindIncidence.plainAdd' -/
#guard_msgs in #kind_ports plainAdd

/-! ## The constructed graph — `#kind_graph`

Every pin above is a projection of the object pinned here. The wiring claims: an
occurrence lands on the node its position assigns (the `let` binder, the output port, a
synthesized interior node); what only *names* a node reaches its port through the
identity wire; sources carry the audit's tiers; and the verdict is computed on the
object, not read off a report. -/

-- The chain: the let binder is a derived introduction, the quotient lands on the
-- output port, and the graph is well-formed.
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.chainQ':
input x : alphaK
input y : betaK
output result : epsilonK
derived t : deltaK
alphaK · betaK → deltaK ⟨x, y⟩ ⇒ t
deltaK / betaK → epsilonK ⟨t, y⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph chainQ

-- The hypothesis-witness helper: its enumeration is empty, but its own graph is wired —
-- the assumed license derives the output within the interface that assumes it.
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.scaleBy':
input x : alphaK
input y : betaK
output result : deltaK
alphaK · betaK → deltaK ⟨x, y⟩ ⇒ result (assumed)
well-formed: true
-/
#guard_msgs in #kind_graph scaleBy

-- A pass-through: the output port is reached from the input by the identity wire.
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.genericLerp':
input tab : k
output result : k
k → k ⟨tab⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph genericLerp

-- A literal tuple: each kinded component reaches its positioned output port by a copy;
-- the bare component wires nothing.
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.swapPair':
input x : alphaK
input y : betaK
output result.1 : betaK
output result.3 : alphaK
betaK → betaK ⟨y⟩ ⇒ result.1
alphaK → alphaK ⟨x⟩ ⇒ result.3
well-formed: true
-/
#guard_msgs in #kind_graph swapPair

-- A configuration read is a source port, and the occurrence consumes it by name.
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.normalized':
input y : betaK
config refQ : deltaK
output result : epsilonK
deltaK / betaK → epsilonK ⟨refQ, y⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph normalized

-- A `@[kindConst]` declaration's own graph: the value is the declared constant mint,
-- wired through an attested source carrying the tier as its reason.
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.refQ':
output result : deltaK
attested "[kindConst]" _1 : deltaK
deltaK → deltaK ⟨_1⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph refQ

/-- A producer in an operand position: the inner product lands on a synthesized
interior node, and the outer quotient's operand names exactly that node — the wiring
connects, whichever occurrence the walk reaches first. -/
def nested {R : Type} [Mul R] [Div R] (x : Quantity alphaK R) (y : Quantity betaK R) :
    Quantity epsilonK R :=
  Quantity.div (QuotientKind.ofRatio deltaK betaK epsilonK)
    (Quantity.mul (ProductKind.ofRatio alphaK betaK deltaK) x y) y

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.nested':
deltaK / betaK → epsilonK ⟨_1, y⟩
alphaK · betaK → deltaK ⟨x, y⟩
-/
#guard_msgs in #kind_occurrences nested

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.nested':
input x : alphaK
input y : betaK
output result : epsilonK
derived _1 : deltaK
deltaK / betaK → epsilonK ⟨_1, y⟩ ⇒ result
alphaK · betaK → deltaK ⟨x, y⟩ ⇒ _1
well-formed: true
-/
#guard_msgs in #kind_graph nested

/-! ### Sources — the audit's tiers, carried into the graph -/

/-- A step whose output is an authored mint through the built-in attestor: the graph
introduces the attested source with its harvested reason and wires it to the output. -/
def attestedStep (m : Float) : Quantity deltaK Float :=
  Quantity.attest "vendor calibration sheet, 2026-08" m

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.attestedStep':
output result : deltaK
attested "vendor calibration sheet, 2026-08" _1 : deltaK
deltaK → deltaK ⟨_1⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph attestedStep

/-- A checked ingest — raw host data admitted through some check. -/
@[kindIngest] def gateIn (x : Float) : Quantity deltaK Float := ⟨max 0.0 x⟩

/-- A step whose output enters through the gate: a `gated` source. -/
def gatedStep (x : Float) : Quantity deltaK Float := gateIn x

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.gatedStep':
output result : deltaK
gated _1 : deltaK
deltaK → deltaK ⟨_1⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph gatedStep

/-- A raw mint: no reading recognizes the bare `⟨…⟩`, the output stays unreached, and
the verdict refuses — the boundary audit's "raw mints = 0", per step. The erased input
is marked as an exit on the way. -/
def rawStep (x : Quantity alphaK Nat) : Quantity alphaK Nat := ⟨x.magnitude + 1⟩

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.rawStep':
input x : alphaK
output result : alphaK
exit x
well-formed: false
-/
#guard_msgs in #kind_graph rawStep

/-! ### The operator table — incidence by one level of instance unfolding -/

open scoped PropertyKindCalculus.OperatorTable

/-- A `[table]` product: the license sits in the resolved instance argument, one unfold
away — the registered instance (`tableEntry`, from the `Core.KindEdges` probes) is the
authored license. -/
def tableProd (x : Quantity alphaK Nat) (y : Quantity betaK Nat) : Quantity gammaK Nat :=
  x * y

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.tableProd':
[table] alphaK · betaK → gammaK ⟨x, y⟩
-/
#guard_msgs in #kind_occurrences tableProd

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.tableProd':
input x : alphaK
input y : betaK
output result : gammaK
[table] alphaK · betaK → gammaK ⟨x, y⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph tableProd

/-- The instance-binder twin of `scaleBy`: the table license is threaded, not
resolved — assumed, so the enumeration is empty while the helper's own graph wires. -/
def tHelperT {R : Type} [Mul R] [KindMul alphaK betaK gammaK]
    (x : Quantity alphaK R) (y : Quantity betaK R) : Quantity gammaK R :=
  x * y

/-- info: no inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.tHelperT' -/
#guard_msgs in #kind_occurrences tHelperT

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.tHelperT':
input x : alphaK
input y : betaK
output result : gammaK
[table] alphaK · betaK → gammaK ⟨x, y⟩ ⇒ result (assumed)
well-formed: true
-/
#guard_msgs in #kind_graph tHelperT

/-- The discharging caller: the table license is the resolved registered instance in
the helper's instance position — read directly off the binder type, operands full. -/
def tCallerT (x : Quantity alphaK Nat) (y : Quantity betaK Nat) : Quantity gammaK Nat :=
  tHelperT x y

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.tCallerT':
[table] alphaK · betaK → gammaK ⟨x, y⟩
-/
#guard_msgs in #kind_occurrences tCallerT

/-! ### Partial incidence — the sub-step boundary -/

/-- A helper exposing *one* of the family's two operands: full incidence inside (both
positions filled by `q`), so its own graph wires — assumed, like every hypothesis
license. -/
def halve {R : Type} [Div R] (h : QuotientKind alphaK alphaK epsilonK)
    (q : Quantity alphaK R) : Quantity epsilonK R :=
  Quantity.div h q q

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.halve':
input q : alphaK
output result : epsilonK
alphaK / alphaK → epsilonK ⟨q, q⟩ ⇒ result (assumed)
well-formed: true
-/
#guard_msgs in #kind_graph halve

/-- Its caller sees a two-operand family through a one-operand signature: the
enumeration keeps the partial incidence, but the graph excludes it from the wiring and
the verdict refuses — one step's graph states what its own body exhibits; composition
across steps closes at assembly. -/
def halved (q : Quantity alphaK Nat) : Quantity epsilonK Nat :=
  halve (QuotientKind.ofRatio alphaK alphaK epsilonK) q

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.halved':
alphaK / alphaK → epsilonK ⟨q⟩
-/
#guard_msgs in #kind_occurrences halved

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.halved':
input q : alphaK
output result : epsilonK
derived _1 : epsilonK
alphaK / alphaK → epsilonK ⟨q⟩ ⇒ _1 (partial)
well-formed: false
-/
#guard_msgs in #kind_graph halved

/-! ### The kernel route — `#kind_graph_decide` -/

-- The harvested graph, reflected and re-derived by kernel reduction: the wiring is a
-- theorem, not an evaluator run.
/--
info: kernel-accepted: the kind graph of 'PropertyKindCalculus.Tests.KindIncidence.chainQ' is well-formed (theorem 'PropertyKindCalculus.Tests.KindIncidence.chainQ.kindGraphWf')
-/
#guard_msgs in #kind_graph_decide chainQ

-- An ill-formed graph never reaches the kernel: the command refuses first.
/--
error: the kind graph of 'PropertyKindCalculus.Tests.KindIncidence.rawStep' is not well-formed — render it with #kind_graph
-/
#guard_msgs in #kind_graph_decide rawStep

end PropertyKindCalculus.Tests.KindIncidence
