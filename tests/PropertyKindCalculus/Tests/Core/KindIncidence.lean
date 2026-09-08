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
open PropertyKindCalculus.Provenance (NodeId KindRef)
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
def chainQ {R : Type} [Mul R] [Div R] [ScalarCarrier R] (x : Quantity alphaK R) (y : Quantity betaK R) :
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
def scaleBy {R : Type} [Mul R] [ScalarCarrier R] (h : ProductKind alphaK betaK deltaK)
    (x : Quantity alphaK R) (y : Quantity betaK R) : Quantity deltaK R :=
  Quantity.mul h x y

/-- info: no inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.scaleBy' -/
#guard_msgs in #kind_occurrences scaleBy

/-- The caller discharges the license, so the occurrence sits here — and the *helper* is
the consuming application: the reader is generic over consumers, not a list of smart
constructors. -/
def scaled {R : Type} [Mul R] [ScalarCarrier R] (x : Quantity alphaK R) (y : Quantity betaK R) :
    Quantity deltaK R :=
  scaleBy (ProductKind.ofRatio alphaK betaK deltaK) x y

/--
info: inline kind occurrences in 'PropertyKindCalculus.Tests.KindIncidence.scaled':
alphaK · betaK → deltaK ⟨x, y⟩
-/
#guard_msgs in #kind_occurrences scaled

/-- A repeated operand is two incidence positions: the same quantity fills numerator and
denominator. -/
def selfRatio {R : Type} [Div R] [ScalarCarrier R] (q : Quantity alphaK R) : Quantity epsilonK R :=
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
  let app := Lean.mkApp9 (kc ``Quantity.mul) (kc ``Nat) (kc ``instMulNat)
    (kc ``instScalarCarrierNat)
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

/-! ### An abbreviation and a plural are not naked data

The unkinded reading answers "does this type carry kind information at all", and two
spellings used to answer no while carrying plenty. An **abbreviation** hides what it
abbreviates — a signature naming `Scaling R` says exactly what the arrow it stands for
says, so the test reduces at reducible transparency before looking. A **container** of
kinded values carries what its elements carry — `List (Sample R)` is a plural of a
kinded thing, not naked data — so a type argument is searched like the type itself.

The two then part ways. A **function over quantities ports at its kind signature** —
the arrow is an anonymous contract of input kinds and an output kind, so the harvest
reads the binder as a module-valued port (`alphaK → betaK` below), however an
abbreviation spells it. A **list** stays the verdict the reading already had a name
for — carries kinds, is not an interface node: a list has no fixed arity, so there is
no field path to name, and calling it naked over-reports the debt: a ledger that
counts a plural of quantities as unkinded data cannot be driven to zero, because
there is nothing there to fix. -/

/-- An abbreviation for a function over quantities — what a threaded model argument
looks like at a call boundary. -/
abbrev Scaling (R : Type) := Quantity alphaK R → Quantity betaK R

/-- A single-constructor record of quantities — the element type below. -/
structure Sample (R : Type) where
  a : Quantity alphaK R
  b : Quantity betaK R

/-- Both spellings in one signature, alongside a genuinely naked position so the pin
shows the reading still separates them. The probed value is let-bound before its
erasure — an inline compound there is refused, because an exit must name a node. -/
def foldSamples (f : Scaling Nat) (xs : List (Sample Nat)) (n : Nat) : Quantity deltaK Nat :=
  let probed := f ⟨0⟩
  ⟨xs.length + n + probed.magnitude⟩

/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.foldSamples':
input f : alphaK → betaK
output result : deltaK
unkinded input n : Nat
-/
#guard_msgs in #kind_ports foldSamples

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
def nested {R : Type} [Mul R] [Div R] [ScalarCarrier R] (x : Quantity alphaK R) (y : Quantity betaK R) :
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
def tHelperT {R : Type} [Mul R] [ScalarCarrier R] [KindMul alphaK betaK gammaK]
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
def halve {R : Type} [Div R] [ScalarCarrier R] (h : QuotientKind alphaK alphaK epsilonK)
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

/-! #### An operand that names no node gets one

`refName` reads a binder, a `let`, a container field path and a declared constant
faithfully, and reads an *application* by walking it down to its head constant — which
names a **declaration, not a node**. An occurrence citing such a name refers to a node no
introduction ever made, so `kindOf?` returns none and `occurrencesTyped` refuses. The
verdict was right and its reason was invented: the body's real defect is that an interior
value is unaccounted for, which is `sourcesReach`'s business. Operand naming and operand
declaration have to agree, so an operand that names no node is given one. -/

/-- A kind-preserving lift standing in for a carrier re-expression: it states no edge, so
a call to it is not a producer the walk recognizes. -/
def liftA (q : Quantity alphaK Nat) : Quantity alphaK Nat := q

/-- The consumer, handed a *call* in its operand slot rather than a binder. -/
def halvedLifted (q : Quantity alphaK Nat) : Quantity epsilonK Nat :=
  halve (QuotientKind.ofRatio alphaK alphaK epsilonK) (liftA q)

-- `_1` is the operand's own node, and it is `derived` with nothing deriving it: the
-- reading now says what the body actually does — it hides a value behind a helper — and
-- refuses on `sourcesReach`, the mint-accountability clause, instead of on a typing
-- failure the naming invented. Naming it after `liftA` would have cited a node that was
-- never introduced.
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.halvedLifted':
input q : alphaK
output result : epsilonK
derived _2 : epsilonK
derived _1 : alphaK
alphaK / alphaK → epsilonK ⟨_1⟩ ⇒ _2 (partial)
well-formed: false
-/
#guard_msgs in #kind_graph halvedLifted

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

/-! #### A member's call site is an edge, not a port

`@[kindConst]` on a *nullary* declaration says "a cited constant enters here", and the
reader declares a configuration port for it. Applied to arguments the same tag says
something else — the callee's result is a declared mint — and per step that is still
read as a port, because an opaque call has nowhere else to put the result. Assembled,
the call is dissected: the result comes off the procedure edge, so the port must go, or
the boundary carries an orphan named after a function that every deploying contract
would have to declare as configuration it does not configure. -/

/-- A blessed helper *with* an argument, its witness written inside so no binder states
the edge — the shape that separates the two readings. -/
@[kindConst]
def blessedHalve (q : Quantity alphaK Nat) : Quantity epsilonK Nat :=
  Quantity.div (QuotientKind.ofRatio alphaK alphaK epsilonK) q q

/-- Its caller. -/
def blessedHalved (q : Quantity alphaK Nat) : Quantity epsilonK Nat := blessedHalve q

-- per step: the call is opaque, so the callee's result is the declared constant and the
-- port carries the callee's name
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.blessedHalved':
input q : alphaK
config PropertyKindCalculus.Tests.KindIncidence.blessedHalve : epsilonK
output result : epsilonK
epsilonK → epsilonK ⟨PropertyKindCalculus.Tests.KindIncidence.blessedHalve⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph blessedHalved

-- assembled: the same call is a procedure edge, and the config port is gone — the
-- boundary is the caller's own interface, exactly as for the untagged `halve`
/--
info: kind assembly of 2 steps:
level blessedHalved: walked
level blessedHalve: walked
input blessedHalved/q : alphaK
output blessedHalved/result : epsilonK
derived blessedHalve/q : alphaK
derived blessedHalve/result : epsilonK
[step blessedHalve] alphaK → epsilonK ⟨blessedHalved/q⟩ ⇒ blessedHalved/result
alphaK / alphaK → epsilonK ⟨blessedHalve/q, blessedHalve/q⟩ ⇒ blessedHalve/result
alphaK → alphaK ⟨blessedHalved/q⟩ ⇒ blessedHalve/q
cites: blessedHalved → blessedHalve
well-formed: true
-/
#guard_msgs in #kind_assembly [blessedHalved, blessedHalve]

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

/-! ### Two calls, two boxes — a level belongs to a call site

A member wired from more than one call site is more than one instantiation. One box for
both would have to state both, and it cannot: the two calls' operands would land on one
input node — a conflation that *passes*, since both wires reach a declared node — and a
kind-generic callee would additionally have to hold two kinds at once, which
`occurrencesTyped` refuses. So the members expand into a call tree and each call takes
its own instance, named `member#k` while there is more than one to tell apart. -/

/-- A kind-generic pass-through on a scalar carrier — the shape a clamp or a saturation
takes: whatever kind goes in comes out. -/
def genericPass {k : KindOfProperty} {R : Type} (x : Quantity k R) : Quantity k R := x

/-- The product of two passed-through operands: one member, two call sites, two kinds. -/
def passedProduct {R : Type} [Mul R] [ScalarCarrier R] (x : Quantity alphaK R) (y : Quantity betaK R) :
    Quantity deltaK R :=
  Quantity.mul (ProductKind.ofRatio alphaK betaK deltaK) (genericPass x) (genericPass y)

/--

info: kind assembly of 2 steps:
level passedProduct: walked
level genericPass: walked
level genericPass#2: walked
input passedProduct/x : alphaK
input passedProduct/y : betaK
output passedProduct/result : deltaK
derived passedProduct/_1 : alphaK
derived passedProduct/_2 : betaK
derived genericPass/x : alphaK
derived genericPass/result : alphaK
derived genericPass#2/x : betaK
derived genericPass#2/result : betaK
alphaK · betaK → deltaK ⟨passedProduct/_1, passedProduct/_2⟩ ⇒ passedProduct/result
[step genericPass] alphaK → alphaK ⟨passedProduct/x⟩ ⇒ passedProduct/_1
[step genericPass#2] betaK → betaK ⟨passedProduct/y⟩ ⇒ passedProduct/_2
alphaK → alphaK ⟨genericPass/x⟩ ⇒ genericPass/result
betaK → betaK ⟨genericPass#2/x⟩ ⇒ genericPass#2/result
alphaK → alphaK ⟨passedProduct/x⟩ ⇒ genericPass/x
betaK → betaK ⟨passedProduct/y⟩ ⇒ genericPass#2/x
cites: passedProduct → genericPass
well-formed: true
-/
#guard_msgs in #kind_assembly [passedProduct, genericPass]

/-- info: kernel-accepted: the kind assembly is well-formed (theorem 'PropertyKindCalculus.Tests.KindIncidence.passedProduct.kindAssemblyWf') -/
#guard_msgs in #kind_assembly_decide [passedProduct, genericPass]

/-- A step that cites a declared constant — the shape a threshold or a calibration read
takes. -/
def offsetByRef (x : Quantity deltaK Nat) : Quantity deltaK Nat := x + refQ

/-- Two calls to it: two boxes, and *one* configuration port, because the constant is one
source however many instantiations read it. -/
def twiceOffset (x y : Quantity deltaK Nat) : Quantity epsilonK Nat :=
  Quantity.div (QuotientKind.ofRatio deltaK deltaK epsilonK) (offsetByRef x) (offsetByRef y)

/--

info: kind assembly of 2 steps:
level twiceOffset: walked
level offsetByRef: walked
level offsetByRef#2: walked
input twiceOffset/x : deltaK
input twiceOffset/y : deltaK
output twiceOffset/result : epsilonK
config offsetByRef/PropertyKindCalculus.Tests.KindIncidence.refQ : deltaK
derived twiceOffset/_1 : deltaK
derived twiceOffset/_2 : deltaK
derived offsetByRef/x : deltaK
derived offsetByRef/result : deltaK
derived offsetByRef#2/x : deltaK
derived offsetByRef#2/result : deltaK
deltaK / deltaK → epsilonK ⟨twiceOffset/_1, twiceOffset/_2⟩ ⇒ twiceOffset/result
[step offsetByRef] deltaK → deltaK ⟨twiceOffset/x⟩ ⇒ twiceOffset/_1
[step offsetByRef#2] deltaK → deltaK ⟨twiceOffset/y⟩ ⇒ twiceOffset/_2
deltaK ± deltaK → deltaK ⟨offsetByRef/x, offsetByRef/PropertyKindCalculus.Tests.KindIncidence.refQ⟩ ⇒ offsetByRef/result
deltaK ± deltaK → deltaK ⟨offsetByRef#2/x, offsetByRef/PropertyKindCalculus.Tests.KindIncidence.refQ⟩ ⇒ offsetByRef#2/result
deltaK → deltaK ⟨twiceOffset/x⟩ ⇒ offsetByRef/x
deltaK → deltaK ⟨twiceOffset/y⟩ ⇒ offsetByRef#2/x
cites: twiceOffset → offsetByRef
well-formed: true
-/
#guard_msgs in #kind_assembly [twiceOffset, offsetByRef]

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
def endOfBoxBoundary : Provenance.Contract NodeId KindRef where
  name := "endOfBox"
  members := [
    ``endOfBoxLet,
    ``degenerate,
    ``lowerEnd]
  ports := [
    ⟨((NodeId.binder "x").within ``endOfBoxLet), .decl ``alphaK, .input⟩,
    ⟨(NodeId.result.within ``endOfBoxLet), .decl ``alphaK, .output⟩]
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
def endOfBoxOverclaimed : Provenance.Contract NodeId KindRef :=
  { endOfBoxBoundary with
    name := "endOfBox (overclaimed)"
    members := endOfBoxBoundary.members ++ [
      ``halved,
      ``halve] }

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
def endOfBoxParametric : Provenance.Contract NodeId KindRef :=
  { endOfBoxBoundary with
    name := "endOfBox (parametric)"
    ports := endOfBoxBoundary.ports.map fun p =>
      if p.node == (NodeId.binder "x").within ``endOfBoxLet then { p with dir := .param }
      else p }

/--

info: kind contract over 3 steps:
contract 'endOfBox (parametric)': 2 ports, 0 exits
params: endOfBoxLet/x
boundary agrees: true
-/
#guard_msgs in #kind_contract endOfBoxParametric

/-- The same boundary claiming the input is a constant this tier binds. -/
def endOfBoxMisconfigured : Provenance.Contract NodeId KindRef :=
  { endOfBoxBoundary with
    name := "endOfBox (misconfigured)"
    ports := endOfBoxBoundary.ports.map fun p =>
      if p.node == (NodeId.binder "x").within ``endOfBoxLet then { p with dir := .config }
      else p }

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
def endOfBoxDeployed : Provenance.Contract NodeId KindRef where
  name := "endOfBox (deployed)"
  members := endOfBoxParametric.members ++ [
    ``halved]
  ports := [⟨(NodeId.result.within ``endOfBoxLet), .decl ``alphaK, .output⟩]
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
def endOfBoxPassedOn : Provenance.Contract NodeId KindRef where
  name := "endOfBox (passed on)"
  members := endOfBoxDeployed.members
  ports := endOfBoxParametric.ports ++ [⟨(NodeId.result.within ``halved), .decl ``epsilonK, .output⟩]
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
def halvingBoundary : Provenance.Contract NodeId KindRef where
  name := "halving"
  members := [
    ``halved,
    ``halve]
  ports := [
    ⟨((NodeId.binder "q").within ``halved), .decl ``alphaK, .input⟩,
    ⟨(NodeId.result.within ``halved), .decl ``epsilonK, .output⟩]
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
def halvedInDomainBoundary : Provenance.Contract NodeId KindRef where
  name := "halvedInDomain"
  members := [
    ``halvedInDomain,
    ``halved,
    ``halve]
  ports := [
    ⟨((NodeId.binder "lo").within ``halvedInDomain), .decl ``alphaK, .input⟩,
    ⟨((NodeId.binder "q").within ``halvedInDomain), .decl ``alphaK, .input⟩,
    ⟨((NodeId.result.field "some").within ``halvedInDomain), .decl ``epsilonK, .conditional⟩]
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
def halvedInDomainTotal : Provenance.Contract NodeId KindRef :=
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

/-! ### The decider — the case's predicate as data of the boundary

The `conditional` role records that cases exist; the `deciders` field names, per
conditional port, the declaration that decides them, so the domain a consumer must
establish is read off the boundary rather than excavated from the body. The checks are
the clause's hygiene: a decider must govern a conditional port — nothing else has cases
— and must name a declaration that exists. -/

/-- The domain that decides the guarded chain's case, named so a boundary can cite it. -/
def halvedDomain (lo q : Quantity alphaK Nat) : Prop := lo ≤ q

/-- The guarded boundary with its case decided by name. -/
def halvedInDomainDecided : Provenance.Contract NodeId KindRef :=
  { halvedInDomainBoundary with
    name := "halvedInDomain (case decided)"
    deciders := [(((NodeId.result.field "some").within ``halvedInDomain),
                  ``halvedDomain)] }

/--
info: kind contract over 3 steps:
contract 'halvedInDomain (case decided)': 3 ports, 0 exits
decides halvedInDomain/result.some: PropertyKindCalculus.Tests.KindIncidence.halvedDomain
boundary agrees: true
-/
#guard_msgs in #kind_contract halvedInDomainDecided

/-- A decider hung on an input: nothing there has cases. -/
def deciderOnAnInput : Provenance.Contract NodeId KindRef :=
  { halvedInDomainBoundary with
    name := "halvedInDomain (decider misplaced)"
    deciders := [(((NodeId.binder "lo").within ``halvedInDomain),
                  ``halvedDomain)] }

/--
error: the decider for 'halvedInDomain/lo' names a port with role 'input' — only a conditional port has cases to decide
-/
#guard_msgs in #kind_contract deciderOnAnInput

/-- A decider that names no declaration. -/
def deciderDangles : Provenance.Contract NodeId KindRef :=
  { halvedInDomainBoundary with
    name := "halvedInDomain (decider dangles)"
    deciders := [(((NodeId.result.field "some").within ``halvedInDomain),
                  `PropertyKindCalculus.Tests.KindIncidence.noSuchDomain)] }

/--
error: the decider 'PropertyKindCalculus.Tests.KindIncidence.noSuchDomain' for 'halvedInDomain/result.some' is not a declaration
-/
#guard_msgs in #kind_contract deciderDangles

/-! ### The aggregation clause — the declared mereology of the boundary

A produced port may declare its aggregation class: what distributing the computation
over a carving of a batch axis does to the value. The checks are the clause's hygiene —
a class governs a *produced* port, since a source composes nothing, and each name the
class carries answers for itself: a quasi-extensive tolerance is a `Quantity` at the
governed port's kind, a named sortal or condition a declaration that exists. The truth
of the class is the author's curated claim, exactly as an `Assembles` entry is; what an
extensive claim buys is `Recarving.distribution_license`, exercised in
`Tests/Core/Recarving.lean`. -/

/-- The per-join tolerance of the guarded chain's output — a quantity at the governed
port's kind, as a tolerance must be. -/
def halvedJoinTol : Quantity epsilonK Nat := ⟨1⟩

/-- A quantity at the input kind, to hang the wrong-kind refusal on. -/
def halvedJoinTolAtAlpha : Quantity alphaK Nat := ⟨1⟩

/-- The guarded boundary with its produced port declared extensive. -/
def halvedExtensive : Provenance.Contract NodeId KindRef :=
  { halvedInDomainBoundary with
    name := "halvedInDomain (extensive)"
    aggregations := [(((NodeId.result.field "some").within ``halvedInDomain), .extensive)] }

/--
info: kind contract over 3 steps:
contract 'halvedInDomain (extensive)': 3 ports, 0 exits
aggregates halvedInDomain/result.some: extensive
boundary agrees: true
-/
#guard_msgs in #kind_contract halvedExtensive

/-- The same port, additive only to within a named per-join tolerance. -/
def halvedQuasi : Provenance.Contract NodeId KindRef :=
  { halvedInDomainBoundary with
    name := "halvedInDomain (quasi-extensive)"
    aggregations := [(((NodeId.result.field "some").within ``halvedInDomain),
      .quasiExtensive ``halvedJoinTol)] }

/--
info: kind contract over 3 steps:
contract 'halvedInDomain (quasi-extensive)': 3 ports, 0 exits
aggregates halvedInDomain/result.some: quasi-extensive within PropertyKindCalculus.Tests.KindIncidence.halvedJoinTol
boundary agrees: true
-/
#guard_msgs in #kind_contract halvedQuasi

/-- The same port read as a count, keyed to the sortal that specifies what is
counted. -/
def halvedCounted : Provenance.Contract NodeId KindRef :=
  { halvedInDomainBoundary with
    name := "halvedInDomain (count keyed)"
    aggregations := [(((NodeId.result.field "some").within ``halvedInDomain),
      .countKeyed ``halvedDomain)] }

/--
info: kind contract over 3 steps:
contract 'halvedInDomain (count keyed)': 3 ports, 0 exits
aggregates halvedInDomain/result.some: count keyed by PropertyKindCalculus.Tests.KindIncidence.halvedDomain
boundary agrees: true
-/
#guard_msgs in #kind_contract halvedCounted

/-- An aggregation class hung on an input: a source composes nothing. -/
def aggregationOnAnInput : Provenance.Contract NodeId KindRef :=
  { halvedInDomainBoundary with
    name := "halvedInDomain (class misplaced)"
    aggregations := [(((NodeId.binder "lo").within ``halvedInDomain), .extensive)] }

/--
error: the aggregation class for 'halvedInDomain/lo' names a port with role 'input' — an aggregation class says how a produced value composes, and this port produces nothing
-/
#guard_msgs in #kind_contract aggregationOnAnInput

/-- A tolerance that names no declaration. -/
def aggregationTolDangles : Provenance.Contract NodeId KindRef :=
  { halvedInDomainBoundary with
    name := "halvedInDomain (tolerance dangles)"
    aggregations := [(((NodeId.result.field "some").within ``halvedInDomain),
      .quasiExtensive `PropertyKindCalculus.Tests.KindIncidence.noSuchTol)] }

/--
error: the tolerance 'PropertyKindCalculus.Tests.KindIncidence.noSuchTol' for 'halvedInDomain/result.some' is not a declaration
-/
#guard_msgs in #kind_contract aggregationTolDangles

/-- A tolerance that is not a quantity — the domain predicate, a `Prop`. -/
def aggregationTolNotAQuantity : Provenance.Contract NodeId KindRef :=
  { halvedInDomainBoundary with
    name := "halvedInDomain (tolerance not a quantity)"
    aggregations := [(((NodeId.result.field "some").within ``halvedInDomain),
      .quasiExtensive ``halvedDomain)] }

/--
error: the tolerance 'PropertyKindCalculus.Tests.KindIncidence.halvedDomain' for 'halvedInDomain/result.some' is not a 'Quantity' — a per-join tolerance is a kinded quantity, not a bare number
-/
#guard_msgs in #kind_contract aggregationTolNotAQuantity

/-- A tolerance at the wrong kind: a discrepancy in the *input* is not a claim about
what the port produces. -/
def aggregationTolWrongKind : Provenance.Contract NodeId KindRef :=
  { halvedInDomainBoundary with
    name := "halvedInDomain (tolerance at the wrong kind)"
    aggregations := [(((NodeId.result.field "some").within ``halvedInDomain),
      .quasiExtensive ``halvedJoinTolAtAlpha)] }

/--
error: the tolerance 'PropertyKindCalculus.Tests.KindIncidence.halvedJoinTolAtAlpha' for 'halvedInDomain/result.some' is a quantity at kind 'alphaK', which is not the port's kind 'epsilonK' — a join's discrepancy is a quantity of what the port produces
-/
#guard_msgs in #kind_contract aggregationTolWrongKind

/-- A sortal that names no declaration: a count of nothing specified is not a count. -/
def aggregationSortalDangles : Provenance.Contract NodeId KindRef :=
  { halvedInDomainBoundary with
    name := "halvedInDomain (sortal dangles)"
    aggregations := [(((NodeId.result.field "some").within ``halvedInDomain),
      .countKeyed `PropertyKindCalculus.Tests.KindIncidence.noSuchSortal)] }

/--
error: the aggregation class for 'halvedInDomain/result.some' names 'PropertyKindCalculus.Tests.KindIncidence.noSuchSortal', which is not a declaration
-/
#guard_msgs in #kind_contract aggregationSortalDangles

/-! ### The module-valued port — a functional argument ports at its kind signature

A kind-typed arrow is an anonymous contract — input kinds, an output kind — so the
harvest reads a functional binder as a port whose kind is that signature, joined with
`→`. The `suppliers` clause then declares which module a tier binds to it, checked
against the supplier's own type: the checks are the clause's hygiene — a supplier
governs a signature port, names a declaration, and that declaration's own signature is
the declared one. Whether two suppliers of one signature agree on *values* is a
`Relation` edge's theorem, not a port list's. -/

/-- A step that consumes a module: the map is a functional argument at a kind
signature, so it ports at that signature — the module-valued port. -/
def halvedThrough (f : Quantity alphaK Nat → Quantity epsilonK Nat)
    (q : Quantity alphaK Nat) : Quantity epsilonK Nat :=
  f q

/--
info: kind ports of 'PropertyKindCalculus.Tests.KindIncidence.halvedThrough':
input f : alphaK → epsilonK
input q : alphaK
output result : epsilonK
-/
#guard_msgs in #kind_ports halvedThrough

/-- The consuming step's boundary, with the module bound by name: `halved` supplies
the `alphaK → epsilonK` signature. -/
def halvedThroughBoundary : Provenance.Contract NodeId KindRef where
  name := "halvedThrough"
  members := [``halvedThrough]
  ports := [
    ⟨(NodeId.binder "f").within ``halvedThrough,
      .sig [.decl ``alphaK, .decl ``epsilonK], .param⟩,
    ⟨((NodeId.binder "q").within ``halvedThrough), .decl ``alphaK, .input⟩,
    ⟨(NodeId.result.within ``halvedThrough), .decl ``epsilonK, .output⟩]
  exits := []
  suppliers := [(((NodeId.binder "f").within ``halvedThrough), ``halved)]

/--

info: kind contract over 1 steps:
contract 'halvedThrough': 3 ports, 0 exits
params: halvedThrough/f
supplies halvedThrough/f: PropertyKindCalculus.Tests.KindIncidence.halved
boundary agrees: true
-/
#guard_msgs in #kind_contract halvedThroughBoundary

/-- A supplier hung on a single-kind port: a value is not a module. -/
def supplierOnAValue : Provenance.Contract NodeId KindRef :=
  { halvedThroughBoundary with
    name := "halvedThrough (supplier misplaced)"
    suppliers := [(((NodeId.binder "q").within ``halvedThrough), ``halved)] }

/--

error: the supplier for 'halvedThrough/q' names a port at kind 'alphaK' — only a module-valued port (a signature kind) takes a supplier
-/
#guard_msgs in #kind_contract supplierOnAValue

/-- A supplier that names no declaration. -/
def supplierDangles : Provenance.Contract NodeId KindRef :=
  { halvedThroughBoundary with
    name := "halvedThrough (supplier dangles)"
    suppliers := [(((NodeId.binder "f").within ``halvedThrough),
                   `PropertyKindCalculus.Tests.KindIncidence.noSuchSupplier)] }

/--

error: the supplier 'PropertyKindCalculus.Tests.KindIncidence.noSuchSupplier' for 'halvedThrough/f' is not a declaration
-/
#guard_msgs in #kind_contract supplierDangles

/-- A supplier that is not a function over quantities — the domain predicate, whose
codomain is a `Prop`. -/
def supplierNotAModule : Provenance.Contract NodeId KindRef :=
  { halvedThroughBoundary with
    name := "halvedThrough (supplier not a module)"
    suppliers := [(((NodeId.binder "f").within ``halvedThrough),
                   ``halvedDomain)] }

/--

error: the supplier 'PropertyKindCalculus.Tests.KindIncidence.halvedDomain' for 'halvedThrough/f' states no kind signature — its explicit arguments are not a function over kinded quantities
-/
#guard_msgs in #kind_contract supplierNotAModule

/-- A supplier of the wrong signature: same-kind identity where the port maps between
kinds. -/
def epsPass (q : Quantity epsilonK Nat) : Quantity epsilonK Nat := q

/-- The boundary with a re-typing binding declared. -/
def supplierWrongSignature : Provenance.Contract NodeId KindRef :=
  { halvedThroughBoundary with
    name := "halvedThrough (supplier at the wrong signature)"
    suppliers := [(((NodeId.binder "f").within ``halvedThrough),
                   ``epsPass)] }

/--

error: the supplier 'PropertyKindCalculus.Tests.KindIncidence.epsPass' for 'halvedThrough/f' states the signature 'epsilonK → epsilonK', which is not the port's 'alphaK → epsilonK' — binding a module of a different signature re-types the argument
-/
#guard_msgs in #kind_contract supplierWrongSignature

/-! ### Re-expression — a conversion that stays inside the calculus

Two references for one kind-of-property are two kinds when a model keeps them apart, and
carrying a value from one to the other is an edge like any other: the value is the single
operand, and the two reference quantities are the edge's configuration. The reading that
matters is the negative one — a conversion written by hand erases its argument and mints
its result, so the input reaches nothing and the verdict refuses; written as the edge, the
same arithmetic wires. -/

/-- The other reference for `alphaK`'s kind-of-property. -/
def alphaPrimeK : KindOfProperty := { id := "incidence probe alpha (other reference)", scale := .ratio }

/-- The authored re-expression law between the two references. -/
theorem alphaRef : ReferenceKind alphaK alphaPrimeK := ReferenceKind.ofRatio _ _

/-- The conversion as the edge: one and the same quantity in both references, and the
association `(a · ref) / ref₁` the floating-point result depends on. -/
def convert (x : Quantity alphaK Float) (ref : Quantity alphaPrimeK Float)
    (ref₁ : Quantity alphaK Float) : Quantity alphaPrimeK Float :=
  Quantity.reexpress alphaRef x ref ref₁

/-- The same arithmetic written through the carrier — the spelling a model reaches for
when the calculus has no name for the conversion. -/
def convertByHand (x : Quantity alphaK Float) (ref : Quantity alphaPrimeK Float)
    (ref₁ : Quantity alphaK Float) : Quantity alphaPrimeK Float :=
  ⟨x.magnitude * ref.magnitude / ref₁.magnitude⟩

/-- The two agree definitionally — the edge is the same arithmetic, differently licensed. -/
theorem convert_eq (x : Quantity alphaK Float) (ref : Quantity alphaPrimeK Float)
    (ref₁ : Quantity alphaK Float) : convertByHand x ref ref₁ = convert x ref ref₁ := rfl

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.convert':
input x : alphaK
input ref : alphaPrimeK
input ref₁ : alphaK
output result : alphaPrimeK
reference : alphaK → alphaPrimeK ⟨x⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph convert

-- by hand: the argument leaves the calculus and the result is an anonymous mint, so
-- nothing reaches the output and the verdict refuses. Same floats, no provenance.
/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.convertByHand':
input x : alphaK
input ref : alphaPrimeK
input ref₁ : alphaK
output result : alphaPrimeK
exit x
exit ref
exit ref₁
well-formed: false
-/
#guard_msgs in #kind_graph convertByHand

/-! ### The same-kind sum — an edge with no witness to author

Family A states its law in the type: two quantities add when they share a kind index, and
the shared index is the whole of the claim. So the edge is *structural* — harvested off the
operation rather than looked for in a binder — and the two spellings a model can reach for,
the gated `Quantity.sub` and the plain `-`, read identically. Without this a model that adds
two quantities could never be well-formed, whatever else it did right. -/

/-- The difference through the gate — the witness spelled, as `Quantity.add`/`sub` ask. -/
def gappedGate (x y : Quantity alphaK Float) : Quantity alphaK Float :=
  Quantity.sub (DifferenceKind.ofScale) x y

/-- The same difference through the arithmetic instance — no witness anywhere. -/
def gappedInstance (x y : Quantity alphaK Float) : Quantity alphaK Float := x - y

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.gappedGate':
input x : alphaK
input y : alphaK
output result : alphaK
alphaK ± alphaK → alphaK ⟨x, y⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph gappedGate

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.gappedInstance':
input x : alphaK
input y : alphaK
output result : alphaK
alphaK ± alphaK → alphaK ⟨x, y⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph gappedInstance

/-! ## The nominal selection — a label that chooses

A `match` on a bespoke label set used to read as naked data steering a kinded result:
the discriminant carried no kind, so the harvest named it `unkinded` and drew a red
flow into whatever the match produced. But a radar polarization, a band designation, a
surface class *is* a property value — of a nominal kind, whose one licensed operation
is the equality a `match` performs. `@[kindNominal k]` says so once, at the type, and
three readings follow: the binder is an interface node at `k`, a caller's argument
wires into it like any other port, and the match becomes a `select` edge whose first
operand is the label and whose remaining operands are the branches, all at the result's
kind.

The edge licenses no kind equation, and that is its content: every branch already
carries the kind the result does, so what the selection adds is *which* branch — the
one thing a nominal comparison can say. -/

/-- A probe nominal kind. Nominal scale: designations, no magnitude. -/
def bandK : KindOfProperty := { id := "kind-incidence probe band", scale := .nominal }

/-- Its designation set — a bespoke finite label set, so the type determines the kind
and no wrapper is needed to state it. -/
@[kindNominal bandK]
inductive Band where
  /-- The long-wavelength designation. -/
  | L
  /-- The short-wavelength designation. -/
  | S
deriving DecidableEq

/-- The formula selected by the label: two products of the same two operands, so the
branches differ in arithmetic and agree in kind. -/
def scaledByBand (b : Band) (x : Quantity alphaK Float) (y : Quantity betaK Float) :
    Quantity deltaK Float :=
  match b with
  | .L => Quantity.mul (ProductKind.ofRatio alphaK betaK deltaK) x y
  | .S => Quantity.mul (ProductKind.ofRatio alphaK betaK deltaK) x (y + y)

/--
info: kind graph of 'PropertyKindCalculus.Tests.KindIncidence.scaledByBand':
input b : bandK
input x : alphaK
input y : betaK
output result : deltaK
derived _1 : deltaK
derived _2 : deltaK
derived _3 : betaK
alphaK · betaK → deltaK ⟨x, y⟩ ⇒ _1
alphaK · betaK → deltaK ⟨x, _3⟩ ⇒ _2
betaK ± betaK → betaK ⟨y, y⟩ ⇒ _3
select bandK : deltaK | deltaK → deltaK ⟨b, _1, _2⟩ ⇒ result
well-formed: true
-/
#guard_msgs in #kind_graph scaledByBand

/-- A caller that fixes the designation — as a *declared* constant, because a label
bound inside a call is a binding no boundary can read. -/
@[kindConst]
def deployedBand : Band := .L

/-- The deployment: one configuration port for the label, wired into the callee's
designation port like any other configured source. -/
def deployedScaled (x : Quantity alphaK Float) (y : Quantity betaK Float) :
    Quantity deltaK Float :=
  scaledByBand deployedBand x y

/--

info: kind assembly of 2 steps:
level deployedScaled: walked
level scaledByBand: walked
input deployedScaled/x : alphaK
input deployedScaled/y : betaK
config deployedScaled/PropertyKindCalculus.Tests.KindIncidence.deployedBand : bandK
output deployedScaled/result : deltaK
derived scaledByBand/b : bandK
derived scaledByBand/x : alphaK
derived scaledByBand/y : betaK
derived scaledByBand/result : deltaK
derived scaledByBand/_1 : deltaK
derived scaledByBand/_2 : deltaK
derived scaledByBand/_3 : betaK
[step scaledByBand] bandK · alphaK · betaK → deltaK ⟨deployedScaled/PropertyKindCalculus.Tests.KindIncidence.deployedBand, deployedScaled/x, deployedScaled/y⟩ ⇒ deployedScaled/result
alphaK · betaK → deltaK ⟨scaledByBand/x, scaledByBand/y⟩ ⇒ scaledByBand/_1
alphaK · betaK → deltaK ⟨scaledByBand/x, scaledByBand/_3⟩ ⇒ scaledByBand/_2
betaK ± betaK → betaK ⟨scaledByBand/y, scaledByBand/y⟩ ⇒ scaledByBand/_3
select bandK : deltaK | deltaK → deltaK ⟨scaledByBand/b, scaledByBand/_1, scaledByBand/_2⟩ ⇒ scaledByBand/result
bandK → bandK ⟨deployedScaled/PropertyKindCalculus.Tests.KindIncidence.deployedBand⟩ ⇒ scaledByBand/b
alphaK → alphaK ⟨deployedScaled/x⟩ ⇒ scaledByBand/x
betaK → betaK ⟨deployedScaled/y⟩ ⇒ scaledByBand/y
cites: deployedScaled → scaledByBand
well-formed: true
-/
#guard_msgs in #kind_assembly [deployedScaled, scaledByBand]

/--

info: kernel-accepted: the kind assembly is well-formed (theorem 'PropertyKindCalculus.Tests.KindIncidence.deployedScaled.kindAssemblyWf')
-/
#guard_msgs in #kind_assembly_decide [deployedScaled, scaledByBand]

/-! ## A configuration constant that is also a member is a wire, not a source

A deployment constant read at `c.field` declares a configuration port at that address,
which is right when `c` is somebody else's business. When `c` is a **member of this
assembly** the address names a value the assembly computes, and reading it as a source
hides the computation behind it: a geometry read as two numbers states two numbers, and
the angle they were computed from reaches no boundary at all — two deployments at
different angles then agree on every port they declare. The two probes below are the same
consumer, differing only in whether the constant is declared a member. -/

/-- A probe kind — the angle a geometry is computed from. -/
def thetaK : KindOfProperty := { id := "kind-incidence probe theta", scale := .ratio }

/-- The bundle a geometry travels as: two components computed together from one angle. -/
structure GeomQ where
  /-- The first component. -/
  a : Quantity alphaK Nat
  /-- The second. -/
  b : Quantity betaK Nat

/-- The deployed angle — the one declaration that fixes it. -/
@[kindConst] def probeAngle : Quantity thetaK Nat := ⟨40⟩

/-- The geometry producer: both components computed from the one angle, so they cannot be
assembled the wrong way round. -/
def geomOfAngle (t : Quantity thetaK Nat) : GeomQ :=
  ⟨Quantity.mul (ProductKind.ofRatio thetaK thetaK alphaK) t t,
   Quantity.mul (ProductKind.ofRatio thetaK thetaK betaK) t t⟩

/-- The deployed geometry — the producer applied to the deployed angle. -/
@[kindConst] def deployedGeom : GeomQ := geomOfAngle probeAngle

/-- The step that consumes a geometry — a container binder, so its kinds arrive as the
field paths a projection spells. -/
def usesGeom (g : GeomQ) (x : Quantity thetaK Nat) : Quantity deltaK Nat :=
  Quantity.mul (ProductKind.ofRatio alphaK betaK deltaK) g.a
    (Quantity.mul (ProductKind.ofRatio betaK thetaK betaK) g.b x)

/-- The deployment: that step at the deployed geometry. -/
def deployedUsesGeom (x : Quantity thetaK Nat) : Quantity deltaK Nat :=
  usesGeom deployedGeom x

-- Not a member: two configuration ports at their addresses, and the angle behind them
-- nowhere on the boundary.
/--

info: kind assembly of 2 steps:
level deployedUsesGeom: walked
level usesGeom: walked
input deployedUsesGeom/x : thetaK
config deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.a : alphaK
config deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.b : betaK
output deployedUsesGeom/result : deltaK
derived usesGeom/g.a : alphaK
derived usesGeom/g.b : betaK
derived usesGeom/x : thetaK
derived usesGeom/result : deltaK
derived usesGeom/_1 : betaK
[step usesGeom] alphaK · betaK · thetaK → deltaK ⟨deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.a, deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.b, deployedUsesGeom/x⟩ ⇒ deployedUsesGeom/result
alphaK · betaK → deltaK ⟨usesGeom/g.a, usesGeom/_1⟩ ⇒ usesGeom/result
betaK · thetaK → betaK ⟨usesGeom/g.b, usesGeom/x⟩ ⇒ usesGeom/_1
alphaK → alphaK ⟨deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.a⟩ ⇒ usesGeom/g.a
betaK → betaK ⟨deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.b⟩ ⇒ usesGeom/g.b
thetaK → thetaK ⟨deployedUsesGeom/x⟩ ⇒ usesGeom/x
cites: deployedUsesGeom → usesGeom
well-formed: true
-/
#guard_msgs in #kind_assembly [deployedUsesGeom, usesGeom]

-- Declared a member: the two addresses become identity wires off the member's own
-- result, both ends demote, and what surfaces in their place is the angle. The citation
-- goes with them — a reference the graph carries is not a citation — while the one to
-- `usesGeom` stays.
/--

info: kind assembly of 3 steps:
level deployedUsesGeom: walked
level usesGeom: walked
level deployedGeom: interface
input deployedUsesGeom/x : thetaK
output deployedUsesGeom/result : deltaK
config deployedGeom/PropertyKindCalculus.Tests.KindIncidence.probeAngle : thetaK
derived deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.a : alphaK
derived deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.b : betaK
derived usesGeom/g.a : alphaK
derived usesGeom/g.b : betaK
derived usesGeom/x : thetaK
derived usesGeom/result : deltaK
derived usesGeom/_1 : betaK
derived deployedGeom/result.a : alphaK
derived deployedGeom/result.b : betaK
[step usesGeom] alphaK · betaK · thetaK → deltaK ⟨deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.a, deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.b, deployedUsesGeom/x⟩ ⇒ deployedUsesGeom/result
alphaK · betaK → deltaK ⟨usesGeom/g.a, usesGeom/_1⟩ ⇒ usesGeom/result
betaK · thetaK → betaK ⟨usesGeom/g.b, usesGeom/x⟩ ⇒ usesGeom/_1
[step deployedGeom] → alphaK ⟨⟩ ⇒ deployedGeom/result.a
[step deployedGeom] → betaK ⟨⟩ ⇒ deployedGeom/result.b
alphaK → alphaK ⟨deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.a⟩ ⇒ usesGeom/g.a
betaK → betaK ⟨deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.b⟩ ⇒ usesGeom/g.b
thetaK → thetaK ⟨deployedUsesGeom/x⟩ ⇒ usesGeom/x
alphaK → alphaK ⟨deployedGeom/result.a⟩ ⇒ deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.a
betaK → betaK ⟨deployedGeom/result.b⟩ ⇒ deployedUsesGeom/PropertyKindCalculus.Tests.KindIncidence.deployedGeom.b
cites: deployedUsesGeom → usesGeom
well-formed: true
-/
#guard_msgs in #kind_assembly [deployedUsesGeom, usesGeom, deployedGeom]

end PropertyKindCalculus.Tests.KindIncidence
