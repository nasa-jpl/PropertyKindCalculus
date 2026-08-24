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
erasure marking its exit; a raw mint refused; a result returned bundled reading exactly
as the loose tuple of the same components, because the container's own constructor is
packaging the walk sees through — and `#kind_graph_decide` has the kernel re-derive a
harvested verdict as a `decide` theorem.
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
config PropertyKindCalculus.Tests.KindIncidence.refQ : deltaK
output result : epsilonK
-/
#guard_msgs in #kind_ports normalized

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.normalized':
deltaK / betaK → epsilonK ⟨PropertyKindCalculus.Tests.KindIncidence.refQ, y⟩
-/
#guard_msgs in #kind_occurrences normalized

/-- A configuration constant read twice: *one* port — a port is an interface node —
while the occurrence below keeps both incidence positions. -/
def selfRef : Quantity epsilonK Nat :=
  Quantity.div (QuotientKind.ofRatio deltaK deltaK epsilonK) refQ refQ

/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.selfRef':
config PropertyKindCalculus.Tests.KindIncidence.refQ : deltaK
output result : epsilonK
-/
#guard_msgs in #kind_ports selfRef

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.selfRef':
deltaK / deltaK → epsilonK ⟨PropertyKindCalculus.Tests.KindIncidence.refQ, PropertyKindCalculus.Tests.KindIncidence.refQ⟩
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
unkinded output result.2 : Nat
-/
#guard_msgs in #kind_ports swapPair

/-- A **container** position: a direction-locked interval bundles two endpoints, and the
signature states its kind through their field paths — the ports name the paths the body
spells (`box.lo.q`, `box.hi.q`), so bundling a pair of same-kind scalars into an `IccQ`
(where a swapped construction is a type error) costs the interface reading nothing. -/
def lowerEnd (box : IccQ alphaK Float) : Quantity alphaK Float := box.lo.q

/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.lowerEnd':
input box.lo.q : alphaK
input box.hi.q : alphaK
output result : alphaK
-/
#guard_msgs in #kind_ports lowerEnd

/-- A container *result*: the field paths port on the output side the same way. -/
def degenerate (x : Quantity alphaK Float) : IccQ alphaK Float := IccQ.of x x

/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.degenerate':
input x : alphaK
output result.lo.q : alphaK
output result.hi.q : alphaK
-/
#guard_msgs in #kind_ports degenerate

/-- A **named result bundle** — the record twin of a two-component tuple, its fields
carrying different kinds so the wiring per field is visible and a swap is a type
error. -/
structure Split (R : Type) where
  /-- The derived component. -/
  prod : Quantity deltaK R
  /-- The pass-through component. -/
  pass : Quantity alphaK R

/-- A step returning its two components **bundled**: a product and a pass-through, handed
back through the record's own constructor. -/
def bundledSplit (x : Quantity alphaK Float) (y : Quantity betaK Float) : Split Float :=
  ⟨Quantity.mul (ProductKind.ofRatio alphaK betaK deltaK) x y, x⟩

/-- The naked-tuple twin of `bundledSplit`, pinned beside it: the claim under both
readings is that re-typing a result from the loose tuple to the record that names its
components moves nothing but the port names. -/
def tupleSplit (x : Quantity alphaK Float) (y : Quantity betaK Float) :
    Quantity deltaK Float × Quantity alphaK Float :=
  (Quantity.mul (ProductKind.ofRatio alphaK betaK deltaK) x y, x)

/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.bundledSplit':
input x : alphaK
input y : betaK
output result.prod : deltaK
output result.pass : alphaK
-/
#guard_msgs in #kind_ports bundledSplit

/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.tupleSplit':
input x : alphaK
input y : betaK
output result.1 : deltaK
output result.2 : alphaK
-/
#guard_msgs in #kind_ports tupleSplit

/-- A signature with no carrier-typed positions at all: every position is named by the
unkinded reading — the report states the nonconformance instead of narrowing to an
empty kinded slice. -/
def plainAdd (a b : Nat) : Nat := a + b

/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.plainAdd':
unkinded input a : Nat
unkinded input b : Nat
unkinded output result : Nat
-/
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
unkinded output result.2 : Nat
betaK → betaK ⟨y⟩ ⇒ result.1
alphaK → alphaK ⟨x⟩ ⇒ result.3
well-formed: true
-/
#guard_msgs in #kind_graph swapPair

-- A container field path names an interface node, so it reaches the output port through
-- the identity wire — exactly as a binder does.
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.lowerEnd':
input box.lo.q : alphaK
input box.hi.q : alphaK
output result : alphaK
alphaK → alphaK ⟨box.lo.q⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph lowerEnd

-- … but a container assembled by a smart-constructor CALL produces nothing: `IccQ.of` is
-- a step like any other, opaque outside an assembly, so both ported endpoints stay
-- unreached and the verdict refuses — the same answer any un-read call gets.
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.degenerate':
input x : alphaK
output result.lo.q : alphaK
output result.hi.q : alphaK
well-formed: false
-/
#guard_msgs in #kind_graph degenerate

-- The container's own CONSTRUCTOR is a different matter: packaging is transparent to
-- dataflow, so each field lands on the slot its own path names. The record and the
-- tuple below are the same computation, and the two pins differ in exactly one thing —
-- the record names its positions. This is what makes a bundled return free: an author
-- who replaces `A × B` with the structure that says what A and B are keeps every wire.
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.bundledSplit':
input x : alphaK
input y : betaK
output result.prod : deltaK
output result.pass : alphaK
alphaK · betaK → deltaK ⟨x, y⟩ ⇒ result.prod
alphaK → alphaK ⟨x⟩ ⇒ result.pass
well-formed: true
-/
#guard_msgs in #kind_graph bundledSplit

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.tupleSplit':
input x : alphaK
input y : betaK
output result.1 : deltaK
output result.2 : alphaK
alphaK · betaK → deltaK ⟨x, y⟩ ⇒ result.1
alphaK → alphaK ⟨x⟩ ⇒ result.2
well-formed: true
-/
#guard_msgs in #kind_graph tupleSplit

-- A configuration read is a source port, and the occurrence consumes it by name.
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.normalized':
input y : betaK
config PropertyKindCalculus.Tests.KindIncidence.refQ : deltaK
output result : epsilonK
deltaK / betaK → epsilonK ⟨PropertyKindCalculus.Tests.KindIncidence.refQ, y⟩ ⇒ result
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
introduces the attested source with its harvested reason and wires it to the output.
The naked `Float` argument is the unkinded reading's exhibit — the red row — and its
occurrence inside the minting application is the unkinded flow: unkinded information
minting kinded information, the red arrow. -/
def attestedStep (m : Float) : Quantity deltaK Float :=
  Quantity.attest "vendor calibration sheet, 2026-08" m

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.attestedStep':
output result : deltaK
unkinded input m : Float
attested "vendor calibration sheet, 2026-08" _1 : deltaK
deltaK → deltaK ⟨_1⟩ ⇒ result
unkinded flow: m ⇒ _1
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
unkinded input x : Float
gated _1 : deltaK
deltaK → deltaK ⟨_1⟩ ⇒ result
unkinded flow: x ⇒ _1
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

/-! ### The audit's emission tier — the sanctioned grid↔kernel shell -/

/-- An emission shell: the tag sanctions this declaration's carrier-constructor mint,
which enters through a declared source carrying the tier as its reason — where the
same `⟨…⟩` in an untagged step (`rawStep`) is refused. -/
@[kindEmission] def liftRaw (v : Nat) : Quantity alphaK Nat := ⟨v⟩

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.liftRaw':
output result : alphaK
unkinded input v : Nat
attested "[kindEmission]" _1 : alphaK
alphaK → alphaK ⟨_1⟩ ⇒ result
unkinded flow: v ⇒ _1
well-formed: true
-/
#guard_msgs in #kind_graph liftRaw

/-! ### Do-elaboration transparency — a straight-line monadic body wires -/

/-- Both branches of an `ite` produce the target — the graph carries one occurrence
per branch — and the condition's erasure marks its exit on the way. -/
def clamped (x : Quantity alphaK Nat) : Quantity epsilonK Nat :=
  if x.magnitude == 0 then Quantity.div (QuotientKind.ofRatio alphaK alphaK epsilonK) x x
  else Quantity.div (QuotientKind.ofRatio alphaK alphaK epsilonK) x x

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.clamped':
input x : alphaK
output result : epsilonK
alphaK / alphaK → epsilonK ⟨x, x⟩ ⇒ result
alphaK / alphaK → epsilonK ⟨x, x⟩ ⇒ result
exit x
well-formed: true
-/
#guard_msgs in #kind_graph clamped

/-! ### The assembly — `#kind_assembly`, one multi-step graph

The members become each other's sub-steps: a call is a procedure edge, a walked call
site is dissected into the callee's box (operands `copy` onto the demoted input ports,
the callee's own level derives its outputs), a kind-generic callee is monomorphized by
its call site, and the verdict — with its kernel theorem — is computed on the
assembled object. Demotion runs at both ends of a wired call, so what stays a port is
the assembly's boundary: in each pin below only the top member's interface survives,
and every callee result the caller consumes reads `derived`. -/

-- The partial-incidence boundary closes at assembly: `halved`'s one-operand view of
-- `halve` was refused per step, and the assembled pair is well-formed — the helper's
-- full incidence lives in its own box, fed by the caller's wire.
/--
info: kind assembly of 2 steps:
level halved: walked
level halve: walked
input halved/q : alphaK
output halved/result : epsilonK
derived halve/q : alphaK
derived halve/result : epsilonK
[step halve] alphaK → epsilonK ⟨halved/q⟩ ⇒ halved/result
alphaK / alphaK → epsilonK ⟨halve/q, halve/q⟩ ⇒ halve/result
alphaK → alphaK ⟨halved/q⟩ ⇒ halve/q
cites: halved → halve
well-formed: true
-/
#guard_msgs in #kind_assembly [halved, halve]

/--
info: kernel-accepted: the kind assembly is well-formed (theorem 'PropertyKindCalculus.Tests.KindIncidence.halved.kindAssemblyWf')
-/
#guard_msgs in #kind_assembly_decide [halved, halve]

/-- A multi-output sub-step: its own graph wires each component port by a copy. -/
def splitQ (x : Quantity alphaK Nat) : Quantity alphaK Nat × Quantity alphaK Nat :=
  (x, x)

/-- A straight-line monadic caller destructuring a multi-output sub-step: `Id.run`,
the single-alternative matcher, and `pure` are transparent, so the binders `u` and `v`
name the callee's slots and the quotient consumes them. Per step the call is opaque —
the graph shows the named-but-underived operands and refuses. -/
def joinedVia (x : Quantity alphaK Nat) : Quantity epsilonK Nat := Id.run do
  let (u, v) := splitQ x
  return Quantity.div (QuotientKind.ofRatio alphaK alphaK epsilonK) u v

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.joinedVia':
input x : alphaK
output result : epsilonK
alphaK / alphaK → epsilonK ⟨u, v⟩ ⇒ result
well-formed: false
-/
#guard_msgs in #kind_graph joinedVia

-- Assembled, the destructured call emits one procedure edge per kinded slot, the
-- shared operand wire dedups, and the callee's box derives its component ports.
/--
info: kind assembly of 2 steps:
level joinedVia: walked
level splitQ: walked
input joinedVia/x : alphaK
output joinedVia/result : epsilonK
derived joinedVia/u : alphaK
derived joinedVia/v : alphaK
derived splitQ/x : alphaK
derived splitQ/result.1 : alphaK
derived splitQ/result.2 : alphaK
[step splitQ] alphaK → alphaK ⟨joinedVia/x⟩ ⇒ joinedVia/u
[step splitQ] alphaK → alphaK ⟨joinedVia/x⟩ ⇒ joinedVia/v
alphaK / alphaK → epsilonK ⟨joinedVia/u, joinedVia/v⟩ ⇒ joinedVia/result
alphaK → alphaK ⟨splitQ/x⟩ ⇒ splitQ/result.1
alphaK → alphaK ⟨splitQ/x⟩ ⇒ splitQ/result.2
alphaK → alphaK ⟨joinedVia/x⟩ ⇒ splitQ/x
cites: joinedVia → splitQ
well-formed: true
-/
#guard_msgs in #kind_assembly [joinedVia, splitQ]

/-- A monomorphic caller of the kind-generic pass-through: the assembly renames the
callee's box through the call's kind assignment. -/
def lerped (tab : Quantity alphaK (Array Float)) : Quantity alphaK (Array Float) :=
  genericLerp tab

/--
info: kind assembly of 2 steps:
level lerped: walked
level genericLerp: walked
input lerped/tab : alphaK
output lerped/result : alphaK
derived genericLerp/tab : alphaK
derived genericLerp/result : alphaK
[step genericLerp] alphaK → alphaK ⟨lerped/tab⟩ ⇒ lerped/result
alphaK → alphaK ⟨genericLerp/tab⟩ ⇒ genericLerp/result
alphaK → alphaK ⟨lerped/tab⟩ ⇒ genericLerp/tab
cites: lerped → genericLerp
well-formed: true
-/
#guard_msgs in #kind_assembly [lerped, genericLerp]

-- A member whose interior the walk cannot wire contributes its interface box: ports
-- plus its own procedure edge, interior accountability the audit's — rendered as such.
/--
info: kind assembly of 1 steps:
level rawStep: interface
input rawStep/x : alphaK
output rawStep/result : alphaK
[step rawStep] alphaK → alphaK ⟨rawStep/x⟩ ⇒ rawStep/result
well-formed: true
-/
#guard_msgs in #kind_assembly [rawStep]

/-! ### A container travelling between two steps

A step's value may travel bundled — an interval, a role wrapper — and the consumer takes
it bundled too. The producer then lands on one node **per carrier field path**, the same
paths the consumer's ports name, so the composition wires: `degenerate` mints an interval
and `lowerEnd` reads an endpoint off its role. The pair is written both ways below,
because the reading must not depend on the spelling: a `let`-bound intermediate and an
inline call differ in the node's *name* (`b.lo.q` against the synthesized `_1.lo.q`) and
in nothing else. -/

/-- The composition with the interval bound to a `let`. -/
def endOfBoxLet (x : Quantity alphaK Float) : Quantity alphaK Float :=
  let b : IccQ alphaK Float := degenerate x
  lowerEnd b

/-- The same composition written inline. -/
def endOfBoxInline (x : Quantity alphaK Float) : Quantity alphaK Float :=
  lowerEnd (degenerate x)

/--
info: kind assembly of 3 steps:
level endOfBoxLet: walked
level degenerate: interface
level lowerEnd: walked
input endOfBoxLet/x : alphaK
output endOfBoxLet/result : alphaK
derived endOfBoxLet/b.lo.q : alphaK
derived endOfBoxLet/b.hi.q : alphaK
derived degenerate/x : alphaK
derived degenerate/result.lo.q : alphaK
derived degenerate/result.hi.q : alphaK
derived lowerEnd/box.lo.q : alphaK
derived lowerEnd/box.hi.q : alphaK
derived lowerEnd/result : alphaK
[step degenerate] alphaK → alphaK ⟨endOfBoxLet/x⟩ ⇒ endOfBoxLet/b.lo.q
[step degenerate] alphaK → alphaK ⟨endOfBoxLet/x⟩ ⇒ endOfBoxLet/b.hi.q
[step lowerEnd] alphaK · alphaK → alphaK ⟨endOfBoxLet/b.lo.q, endOfBoxLet/b.hi.q⟩ ⇒ endOfBoxLet/result
[step degenerate] alphaK → alphaK ⟨degenerate/x⟩ ⇒ degenerate/result.lo.q
[step degenerate] alphaK → alphaK ⟨degenerate/x⟩ ⇒ degenerate/result.hi.q
alphaK → alphaK ⟨lowerEnd/box.lo.q⟩ ⇒ lowerEnd/result
alphaK → alphaK ⟨endOfBoxLet/x⟩ ⇒ degenerate/x
alphaK → alphaK ⟨endOfBoxLet/b.lo.q⟩ ⇒ lowerEnd/box.lo.q
alphaK → alphaK ⟨endOfBoxLet/b.hi.q⟩ ⇒ lowerEnd/box.hi.q
cites: endOfBoxLet → degenerate
cites: endOfBoxLet → lowerEnd
well-formed: true
-/
#guard_msgs in #kind_assembly [endOfBoxLet, degenerate, lowerEnd]

/--
info: kind assembly of 3 steps:
level endOfBoxInline: walked
level degenerate: interface
level lowerEnd: walked
input endOfBoxInline/x : alphaK
output endOfBoxInline/result : alphaK
derived endOfBoxInline/_1.lo.q : alphaK
derived endOfBoxInline/_1.hi.q : alphaK
derived degenerate/x : alphaK
derived degenerate/result.lo.q : alphaK
derived degenerate/result.hi.q : alphaK
derived lowerEnd/box.lo.q : alphaK
derived lowerEnd/box.hi.q : alphaK
derived lowerEnd/result : alphaK
[step lowerEnd] alphaK · alphaK → alphaK ⟨endOfBoxInline/_1.lo.q, endOfBoxInline/_1.hi.q⟩ ⇒ endOfBoxInline/result
[step degenerate] alphaK → alphaK ⟨endOfBoxInline/x⟩ ⇒ endOfBoxInline/_1.lo.q
[step degenerate] alphaK → alphaK ⟨endOfBoxInline/x⟩ ⇒ endOfBoxInline/_1.hi.q
[step degenerate] alphaK → alphaK ⟨degenerate/x⟩ ⇒ degenerate/result.lo.q
[step degenerate] alphaK → alphaK ⟨degenerate/x⟩ ⇒ degenerate/result.hi.q
alphaK → alphaK ⟨lowerEnd/box.lo.q⟩ ⇒ lowerEnd/result
alphaK → alphaK ⟨endOfBoxInline/_1.lo.q⟩ ⇒ lowerEnd/box.lo.q
alphaK → alphaK ⟨endOfBoxInline/_1.hi.q⟩ ⇒ lowerEnd/box.hi.q
alphaK → alphaK ⟨endOfBoxInline/x⟩ ⇒ degenerate/x
cites: endOfBoxInline → lowerEnd
cites: endOfBoxInline → degenerate
well-formed: true
-/
#guard_msgs in #kind_assembly [endOfBoxInline, degenerate, lowerEnd]

/-- A consumer of the **bundled return**: it takes the record `bundledSplit` hands back
and divides its two components. -/
def usesSplit (x : Quantity alphaK Float) (y : Quantity betaK Float) :
    Quantity epsilonK Float :=
  let g := bundledSplit x y
  Quantity.div (QuotientKind.ofRatio deltaK alphaK epsilonK) g.prod g.pass

-- The payoff of reading the constructor: `bundledSplit` is a WALKED level, so the
-- assembly states what its body actually did — `result.pass` is an identity wire from
-- `x` alone. Read as an interface box it would instead carry the level's own procedure
-- edge into every output, claiming the pass-through depends on `y` too: a bundled return
-- that cannot be walked does not merely lose a verdict, it over-connects.
/--
info: kind assembly of 2 steps:
level usesSplit: walked
level bundledSplit: walked
input usesSplit/x : alphaK
input usesSplit/y : betaK
output usesSplit/result : epsilonK
derived usesSplit/g.prod : deltaK
derived usesSplit/g.pass : alphaK
derived bundledSplit/x : alphaK
derived bundledSplit/y : betaK
derived bundledSplit/result.prod : deltaK
derived bundledSplit/result.pass : alphaK
[step bundledSplit] alphaK · betaK → deltaK ⟨usesSplit/x, usesSplit/y⟩ ⇒ usesSplit/g.prod
[step bundledSplit] alphaK · betaK → alphaK ⟨usesSplit/x, usesSplit/y⟩ ⇒ usesSplit/g.pass
deltaK / alphaK → epsilonK ⟨usesSplit/g.prod, usesSplit/g.pass⟩ ⇒ usesSplit/result
alphaK · betaK → deltaK ⟨bundledSplit/x, bundledSplit/y⟩ ⇒ bundledSplit/result.prod
alphaK → alphaK ⟨bundledSplit/x⟩ ⇒ bundledSplit/result.pass
alphaK → alphaK ⟨usesSplit/x⟩ ⇒ bundledSplit/x
betaK → betaK ⟨usesSplit/y⟩ ⇒ bundledSplit/y
cites: usesSplit → bundledSplit
well-formed: true
-/
#guard_msgs in #kind_assembly [usesSplit, bundledSplit]

/-! ### The declared boundary — `#kind_contract`

The wiring verdict is monotone under adding an unrelated member, so it cannot judge the
membership choice; the boundary can, because a member brings ports with it. The contract
below declares the interval composition's scope and interface together — three members,
one input, one output, the levels' intermediate results interior — and the pins judge it
three ways: as declared, with an unrelated pair added to the *declared* member list, and
with the input declared a `param`, which is the one refinement a declaration may make
over a computed role. -/

/-- The declared boundary of the interval composition. -/
def endOfBoxBoundary : Provenance.Contract String String where
  name := "endOfBox"
  members := [
    "PropertyKindCalculus.Tests.KindIncidence.endOfBoxLet",
    "PropertyKindCalculus.Tests.KindIncidence.degenerate",
    "PropertyKindCalculus.Tests.KindIncidence.lowerEnd"]
  ports := [
    ⟨"endOfBoxLet/x", "alphaK", .input⟩,
    ⟨"endOfBoxLet/result", "alphaK", .output⟩]
  exits := []

/--
info: kind contract over 3 steps:
contract 'endOfBox': 2 ports, 0 exits
boundary agrees: true
-/
#guard_msgs in #kind_contract endOfBoxBoundary

/--
info: kernel-accepted: 'PropertyKindCalculus.Tests.KindIncidence.endOfBoxBoundary' is the boundary of its 3-step assembly (theorem 'PropertyKindCalculus.Tests.KindIncidence.endOfBoxBoundary.kindContractOk')
-/
#guard_msgs in #kind_contract_decide endOfBoxBoundary

/-- The same interface claimed for a wider scope. -/
def endOfBoxOverclaimed : Provenance.Contract String String :=
  { endOfBoxBoundary with
    name := "endOfBox (overclaimed)"
    members := endOfBoxBoundary.members ++ [
      "PropertyKindCalculus.Tests.KindIncidence.halved",
      "PropertyKindCalculus.Tests.KindIncidence.halve"] }

-- The scope reading: two unrelated members join the assembly, the wiring verdict is
-- unmoved (`#kind_assembly` above says `true` for each part and the union is disjoint),
-- and the boundary reports exactly what they brought.
/--
info: kind contract over 5 steps:
contract 'endOfBox (overclaimed)': 2 ports, 0 exits
undeclared input halved/q : alphaK
undeclared output halved/result : epsilonK
boundary agrees: false
-/
#guard_msgs in #kind_contract endOfBoxOverclaimed

/-- The same boundary with the input declared a parameter — a claim about binding time,
which the walk cannot read and the comparison therefore accepts. -/
def endOfBoxParametric : Provenance.Contract String String :=
  { endOfBoxBoundary with
    name := "endOfBox (parametric)"
    ports := endOfBoxBoundary.ports.map fun p =>
      if p.node == "endOfBoxLet/x" then { p with dir := .param } else p }

/--
info: kind contract over 3 steps:
contract 'endOfBox (parametric)': 2 ports, 0 exits
params: endOfBoxLet/x
boundary agrees: true
-/
#guard_msgs in #kind_contract endOfBoxParametric

/-- The same boundary claiming the input is a constant this tier binds. -/
def endOfBoxMisconfigured : Provenance.Contract String String :=
  { endOfBoxBoundary with
    name := "endOfBox (misconfigured)"
    ports := endOfBoxBoundary.ports.map fun p =>
      if p.node == "endOfBoxLet/x" then { p with dir := .config } else p }

-- `config` says the tier binds the value, which is a harvested fact and not a claim the
-- contract may make: the port is at once undeclared and unrealized.
/--
info: kind contract over 3 steps:
contract 'endOfBox (misconfigured)': 2 ports, 0 exits
undeclared input endOfBoxLet/x : alphaK
unrealized config endOfBoxLet/x : alphaK
boundary agrees: false
-/
#guard_msgs in #kind_contract endOfBoxMisconfigured

-- The wiring readings over the same declared scope: the member list named once, and the
-- rendering identical to the bracket form's above, because it is the same assembly.
/--
info: kind assembly of 3 steps:
level endOfBoxLet: walked
level degenerate: interface
level lowerEnd: walked
input endOfBoxLet/x : alphaK
output endOfBoxLet/result : alphaK
derived endOfBoxLet/b.lo.q : alphaK
derived endOfBoxLet/b.hi.q : alphaK
derived degenerate/x : alphaK
derived degenerate/result.lo.q : alphaK
derived degenerate/result.hi.q : alphaK
derived lowerEnd/box.lo.q : alphaK
derived lowerEnd/box.hi.q : alphaK
derived lowerEnd/result : alphaK
[step degenerate] alphaK → alphaK ⟨endOfBoxLet/x⟩ ⇒ endOfBoxLet/b.lo.q
[step degenerate] alphaK → alphaK ⟨endOfBoxLet/x⟩ ⇒ endOfBoxLet/b.hi.q
[step lowerEnd] alphaK · alphaK → alphaK ⟨endOfBoxLet/b.lo.q, endOfBoxLet/b.hi.q⟩ ⇒ endOfBoxLet/result
[step degenerate] alphaK → alphaK ⟨degenerate/x⟩ ⇒ degenerate/result.lo.q
[step degenerate] alphaK → alphaK ⟨degenerate/x⟩ ⇒ degenerate/result.hi.q
alphaK → alphaK ⟨lowerEnd/box.lo.q⟩ ⇒ lowerEnd/result
alphaK → alphaK ⟨endOfBoxLet/x⟩ ⇒ degenerate/x
alphaK → alphaK ⟨endOfBoxLet/b.lo.q⟩ ⇒ lowerEnd/box.lo.q
alphaK → alphaK ⟨endOfBoxLet/b.hi.q⟩ ⇒ lowerEnd/box.hi.q
cites: endOfBoxLet → degenerate
cites: endOfBoxLet → lowerEnd
well-formed: true
-/
#guard_msgs in #kind_assembly endOfBoxBoundary

/--
info: kernel-accepted: the kind assembly is well-formed (theorem 'PropertyKindCalculus.Tests.KindIncidence.endOfBoxLet.kindAssemblyWf')
-/
#guard_msgs in #kind_assembly_decide endOfBoxBoundary

/-! ### The tier relation — `#kind_discharges`

Two declarations, no graph: what a deploying contract did with the parameters it
inherited. `endOfBoxParametric` above hands one down; the contracts below answer for it
three ways — bound within a wider scope, restated as a parameter of the wider scope, and
quietly relabelled per-datum data, which is the case the relation exists to refuse. -/

/-- A wider scope that binds the inherited parameter: `endOfBoxLet/x` is fed inside it,
so the port is interior and gone from this boundary. Members and exits are its own; only
the discharge is at issue here. -/
def endOfBoxDeployed : Provenance.Contract String String where
  name := "endOfBox (deployed)"
  members := endOfBoxParametric.members ++ [
    "PropertyKindCalculus.Tests.KindIncidence.halved"]
  ports := [⟨"endOfBoxLet/result", "alphaK", .output⟩]
  exits := []

/--
info: kind tier:
tier 'endOfBox (deployed)' over 'endOfBox (parametric)': 3 members inherited, 1 parameters
bound endOfBoxLet/x
discharges: true
-/
#guard_msgs in #kind_discharges endOfBoxDeployed endOfBoxParametric

/--
info: kernel-accepted: 'PropertyKindCalculus.Tests.KindIncidence.endOfBoxDeployed' discharges 'PropertyKindCalculus.Tests.KindIncidence.endOfBoxParametric' (theorem 'PropertyKindCalculus.Tests.KindIncidence.endOfBoxDeployed.kindDischarges.endOfBoxParametric')
-/
#guard_msgs in #kind_discharges_decide endOfBoxDeployed endOfBoxParametric

/-- A wider scope that does not bind the inherited parameter but keeps calling it one:
the obligation stays named, for the tier after this one. -/
def endOfBoxPassedOn : Provenance.Contract String String where
  name := "endOfBox (passed on)"
  members := endOfBoxDeployed.members
  ports := endOfBoxParametric.ports ++ [⟨"halved/result", "epsilonK", .output⟩]
  exits := []

-- Passing it on is the other lawful answer.
/--
info: kind tier:
tier 'endOfBox (passed on)' over 'endOfBox (parametric)': 3 members inherited, 1 parameters
restated endOfBoxLet/x
discharges: true
-/
#guard_msgs in #kind_discharges endOfBoxPassedOn endOfBoxParametric

-- And the case the relation exists for: the boundary is unchanged, the wiring verdict is
-- unchanged, `agrees` is unchanged — the only thing that moved is a role, and with it an
-- obligation that now belongs to nobody.
/--
info: kind tier:
tier 'endOfBox' over 'endOfBox (parametric)': 3 members inherited, 1 parameters
undischarged endOfBoxLet/x
discharges: false
-/
#guard_msgs in #kind_discharges endOfBoxBoundary endOfBoxParametric

/-- An unrelated scope, to ask the relation about a pair that does not stack. -/
def halvingBoundary : Provenance.Contract String String where
  name := "halving"
  members := [
    "PropertyKindCalculus.Tests.KindIncidence.halved",
    "PropertyKindCalculus.Tests.KindIncidence.halve"]
  ports := [
    ⟨"halved/q", "alphaK", .input⟩,
    ⟨"halved/result", "epsilonK", .output⟩]
  exits := []

-- A scope that is not a deployment of the algorithm at all: the members do not contain
-- it, so nothing it says about parameters is about this.
/--
info: kind tier:
tier 'endOfBox' over 'halving': 2 members inherited, 0 parameters
outside the scope: PropertyKindCalculus.Tests.KindIncidence.halved
outside the scope: PropertyKindCalculus.Tests.KindIncidence.halve
discharges: false
-/
#guard_msgs in #kind_discharges endOfBoxBoundary halvingBoundary

/-! ### The conditional output — a validity domain stated at the interface

A step that returns a quantity in some cases and nothing in others states the cases at
its boundary: the sum's carrier-bearing payload ports at the *case* that carries it, in
the `conditional` role. The wrapper itself is transparent to the walk — which case a
value took is the interface's claim, not a step in the derivation — so the guarded body
produces onto the conditional port exactly where the unguarded one produces onto a plain
output, and a case with no quantity in it contributes nothing. -/

/-- The partial-incidence helper, guarded by a domain check: the quotient in the valid
case and nothing outside it. -/
def halvedInDomain (lo q : Quantity alphaK Nat) : Option (Quantity epsilonK Nat) :=
  if lo ≤ q then some (halved q) else none

/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.halvedInDomain':
input lo : alphaK
input q : alphaK
conditional result.some : epsilonK
-/
#guard_msgs in #kind_ports halvedInDomain

-- `none` carries no quantity and produces nothing, so standalone — where the sub-step is
-- opaque — the conditional port stays unreached and the verdict refuses, exactly as a
-- plain output would.
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.halvedInDomain':
input lo : alphaK
input q : alphaK
conditional result.some : epsilonK
well-formed: false
-/
#guard_msgs in #kind_graph halvedInDomain

/-- The declared boundary of the guarded chain, with the case stated. -/
def halvedInDomainBoundary : Provenance.Contract String String where
  name := "halvedInDomain"
  members := [
    "PropertyKindCalculus.Tests.KindIncidence.halvedInDomain",
    "PropertyKindCalculus.Tests.KindIncidence.halved",
    "PropertyKindCalculus.Tests.KindIncidence.halve"]
  ports := [
    ⟨"halvedInDomain/lo", "alphaK", .input⟩,
    ⟨"halvedInDomain/q", "alphaK", .input⟩,
    ⟨"halvedInDomain/result.some", "epsilonK", .conditional⟩]
  exits := []

/--
info: kind assembly of 3 steps:
level halvedInDomain: walked
level halved: walked
level halve: walked
input halvedInDomain/lo : alphaK
input halvedInDomain/q : alphaK
conditional halvedInDomain/result.some : epsilonK
derived halved/q : alphaK
derived halved/result : epsilonK
derived halve/q : alphaK
derived halve/result : epsilonK
[step halved] alphaK → epsilonK ⟨halvedInDomain/q⟩ ⇒ halvedInDomain/result.some
[step halve] alphaK → epsilonK ⟨halved/q⟩ ⇒ halved/result
alphaK / alphaK → epsilonK ⟨halve/q, halve/q⟩ ⇒ halve/result
alphaK → alphaK ⟨halvedInDomain/q⟩ ⇒ halved/q
alphaK → alphaK ⟨halved/q⟩ ⇒ halve/q
cites: halvedInDomain → halved
cites: halved → halve
well-formed: true
-/
#guard_msgs in #kind_assembly halvedInDomainBoundary

/--
info: kind contract over 3 steps:
contract 'halvedInDomain': 3 ports, 0 exits
boundary agrees: true
-/
#guard_msgs in #kind_contract halvedInDomainBoundary

/-- The same boundary claiming the result is always there. -/
def halvedInDomainTotal : Provenance.Contract String String :=
  { halvedInDomainBoundary with
    name := "halvedInDomain (claimed total)"
    ports := halvedInDomainBoundary.ports.map fun p =>
      if p.dir == .conditional then { p with dir := .output } else p }

-- Whether an interface always produces a value is the plainest thing it has to say, so
-- the two output roles do not refine one another in either direction.
/--
info: kind contract over 3 steps:
contract 'halvedInDomain (claimed total)': 3 ports, 0 exits
undeclared conditional halvedInDomain/result.some : epsilonK
unrealized output halvedInDomain/result.some : epsilonK
boundary agrees: false
-/
#guard_msgs in #kind_contract halvedInDomainTotal

end PropertyKindCalculus.Tests.KindIncidence
