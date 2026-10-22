/-
# `PkcModel` — the neutral interchange form between Lean PKC and the SysML v2 PKC DSL

A PKC model travels between the Lean libraries and a SysML v2 model as one plain record,
`PkcModel`, with a JSON encoding derived field by field. It is the *pivot* of the interchange:

* **Lean → SysML.** `Interchange.Harvest` reads the environment into a `PkcModel`;
  `Interchange.EmitSysml` prints it as a model written in the PKC DSL (`sysml/PKC.sysml`).
* **SysML → Lean.** OpenSysML converts a DSL model to the OMG API element form;
  `Interchange.ApiJson` reads that element list into a `PkcModel`; `Interchange.EmitLean`
  prints a Lean module the kernel re-checks.

The record has three layers, mirroring the libraries: the **kind layer** (kinds of property,
examination principles, specialization, the authored kind algebra, dedicated kinds, units, the
dimension vector and catalogue locators as *metadata*), the **module layer** (metrology
modules — kind-typed ports, the provenance hypergraph, relations, requirements) and the
**tape layer** (computational tape graphs and their matches against a module's hypergraph,
with the carrier rung and platform the match is claimed at).

Nothing here is a proof. Every element may carry *citations* — the Lean declaration it was
harvested from (`source`) and the kernel-checked declarations backing it (`checked`). The
importer verifies a citation names an existing declaration of the expected shape; it never
turns one into a theorem. The evidence tiers of the calculus (derived / gated / attested)
travel with the model as data for the same reason.
-/

module

public import Lean.Data.Json

@[expose] public section Blanket

namespace PropertyKindCalculus.Interchange

open Lean (ToJson FromJson)

/-- A citation of a kernel-checked declaration: its name and, optionally, the statement the
author believes it has (checked against the environment on import, never trusted). -/
structure Checked where
  decl : String
  statement : Option String := none
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-! ## The kind layer -/

/-- The operator-based scale stratification of a kind of property (Dybkær Ch. 12). -/
inductive Scale where
  | nominal | ordinal | interval | ratio
deriving Repr, BEq, DecidableEq, Inhabited, ToJson, FromJson

/-- One base-dimension exponent of a dimension vector, as a rational `num/den`. -/
structure DimExponent where
  base : String
  num : Int
  den : Nat := 1
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- An examination principle — what individuates a species within a genus. -/
structure Principle where
  name : String
  id : String
  source : Option String := none
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- A kind of property. `name` is the identifier the model declares it under (the SysML
element name / the Lean constant's last component); `id` is the kind's own identity string.
`specializes` lists the names of the kinds it directly specializes. The dimension vector and
the catalogue locators are metadata the dimension and ISO 80000 layers attach; they are not
the kind's identity. -/
structure Kind where
  name : String
  id : String
  scale : Scale
  principle : Option String := none
  specializes : List String := []
  dimension : List DimExponent := []
  standardRef : Option String := none
  catalogueItem : Option String := none
  symbol : Option String := none
  coherentUnit : Option String := none
  source : Option String := none
  checked : List Checked := []
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- The witness families of the kind algebra, as they are authored. -/
inductive EdgeKind where
  | product | quotient | reciprocal | power | transcendental | reference | difference
deriving Repr, BEq, DecidableEq, Inhabited, ToJson, FromJson

/-- One authored kind-algebra edge: the family, its operand kinds in the order the family
reads them, and the result kind (absent for `difference`, which stays at its kind). `table`
marks a `KindMul`/`KindDiv` registration as opposed to a witness `Prop`; `power` carries its
rational exponent. -/
structure Edge where
  name : String
  kind : EdgeKind
  operands : List String
  result : Option String := none
  table : Bool := false
  powerNum : Option Int := none
  powerDen : Option Nat := none
  source : Option String := none
  checked : List Checked := []
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- A kind dedicated to a component of a sort of system. -/
structure Dedicated where
  name : String
  sort : String
  component : String
  kind : String
  source : Option String := none
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- A measurement unit of a kind, by symbol. -/
structure MetrologicalUnit where
  name : String
  kind : String
  symbol : String
  source : Option String := none
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-! ## The module layer -/

/-- The role of a port in a module's signature. -/
inductive PortDir where
  | input | config | param | output | conditional
deriving Repr, BEq, DecidableEq, Inhabited, ToJson, FromJson

/-- The evidence tier that introduces a node at a kind. -/
inductive IntroTier where
  | derived | gated | attested
deriving Repr, BEq, DecidableEq, Inhabited, ToJson, FromJson

/-- The hyperedge families of the provenance hypergraph. -/
inductive EdgeFamily where
  | product | quotient | reciprocal | transcendental | power | reference
  | additive | tableMul | tableDiv | copy | step | select
deriving Repr, BEq, DecidableEq, Inhabited, ToJson, FromJson

/-- Which side of a relation a boundary is: the model computed, or its specification. -/
inductive BoundaryRole where
  | model | specification
deriving Repr, BEq, DecidableEq, Inhabited, ToJson, FromJson

/-- The declared mereology of a produced port under a carving of a batch axis. -/
inductive AggregationKind where
  | extensive | quasiExtensive | conditionallyExtensive | intensive | wholeProper | countKeyed
  | extensiveAbout | interfaceLicensed
deriving Repr, BEq, DecidableEq, Inhabited, ToJson, FromJson

/-- What a relation claims between two boundaries. -/
inductive RelationKind where
  | inverts | refines | equals | boundedBy
deriving Repr, BEq, DecidableEq, Inhabited, ToJson, FromJson

/-- How a relation's claim transfers to a rung of the carrier ladder. -/
inductive TransferKind where
  | exact | nonneg | restated
deriving Repr, BEq, DecidableEq, Inhabited, ToJson, FromJson

/-- Whether a requirement is discharged by proof or by empirical evidence. -/
inductive RequirementKind where
  | provable | empirical
deriving Repr, BEq, DecidableEq, Inhabited, ToJson, FromJson

/-- The objects a requirement quantifies over — `Provenance.RequirementScope` with its names
rendered. In the DSL it is the optional `scope` string binding: `ReqScope.render` prints it and
`ReqScope.parse` reads it back, the one place the binding's syntax lives. -/
inductive ReqScope where
  | all
  | sort (sort : String)
  | objects (objects : List String)
  | decided (decider : String)
deriving Repr, BEq, DecidableEq, Inhabited, ToJson, FromJson

/-- The `scope` binding: `sort S`, `objects A, B` or `decided D`; absent for `.all`. -/
def ReqScope.render : ReqScope → Option String
  | .all => none
  | .sort s => some s!"sort {s}"
  | .objects os => some ("objects " ++ String.intercalate ", " os)
  | .decided d => some s!"decided {d}"

/-- The scope a `scope` binding denotes: absent is `.all`; a string in none of the three forms
`render` prints is an error, never silently the widest scope. -/
def ReqScope.parse : Option String → Except String ReqScope
  | none => pure .all
  | some s =>
    let after (prefix_ : String) : Option String :=
      if s.startsWith prefix_ then some (s.drop prefix_.length).toString else none
    if let some n := after "sort " then pure (.sort n)
    else if let some d := after "decided " then pure (.decided d)
    else if let some os := after "objects " then
      pure (.objects (if os.isEmpty then [] else os.splitOn ", "))
    else throw s!"unknown scope '{s}' (expected `sort S`, `objects A, B` or `decided D`)"

/-- A kind-typed port: the node, the kind the signature states, and its role. -/
structure Port where
  name : String
  node : String
  kind : String
  dir : PortDir
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- A node introduced at a kind by an evidence tier. -/
structure Intro where
  node : String
  kind : String
  tier : IntroTier
  reason : Option String := none
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- One operand of a hyperedge occurrence. -/
structure Operand where
  node : String
  kind : String
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- One hyperedge of the provenance hypergraph, attributed to its use site. -/
structure Occurrence where
  family : EdgeFamily
  operands : List Operand
  result : String
  resultKind : String
  site : String
  op : Option String := none
  member : Option String := none
  inst : Option Nat := none
  arity : Option Nat := none
  powerNum : Option Int := none
  powerDen : Option Nat := none
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- A produced port's aggregation class, with the declaration that witnesses it. -/
structure Aggregation where
  node : String
  cls : AggregationKind
  witness : Option String := none
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- A metrology module: the declared boundary (`Provenance.Contract`) and the provenance
hypergraph the assembly computed for it. -/
structure MetrologyModule where
  name : String
  title : String
  members : List String := []
  ports : List Port := []
  exits : List String := []
  deciders : List (String × String) := []
  aggregations : List Aggregation := []
  suppliers : List (String × String) := []
  role : BoundaryRole := .model
  /-- The model states this module's hypergraph — `intros` and `occurrences` are its wiring,
  not an absence of data — and asks for the wiring verdicts (`wellFormed`, `agrees`, and
  `accepts` for a match against it). A contract whose wiring is not stated is data only. -/
  hypergraph : Bool := false
  intros : List Intro := []
  occurrences : List Occurrence := []
  source : Option String := none
  checked : List Checked := []
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- How a relation's claim holds at one rung of the carrier ladder. -/
structure License where
  rung : String
  transfer : TransferKind
  witness : String
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- The spec edge between two boundaries, with its theorem witness. -/
structure Relation where
  name : String
  left : String
  right : String
  kind : RelationKind
  witness : String
  claim : Option String := none
  tolerance : Option String := none
  hypotheses : List String := []
  licenses : List License := []
  wellPosed : Option String := none
  domain : Option String := none
  ambiguity : Option String := none
  source : Option String := none
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- What a module's quantities must satisfy, with the evidence by which it is met. -/
structure Requirement where
  name : String
  title : String
  statement : String
  kind : RequirementKind
  governs : String
  port : Option String := none
  scope : ReqScope := .all
  witness : Option String := none
  spotChecks : List String := []
  absent : Option String := none
  referents : List String := []
  source : Option String := none
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-! ## The tape layer -/

/-- A tape node once its value and backward rule are forgotten: its name and parents. -/
structure TapeVertex where
  name : Option String := none
  parents : List Nat := []
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- A computational tape graph: vertices in build order, every parent before its child. -/
structure Tape where
  name : String
  vertices : List TapeVertex
  source : Option String := none
  checked : List Checked := []
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- The tape vertices a hypergraph node is realized by. -/
structure NodeComponents where
  node : String
  vertices : List Nat
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- An occurrence realized by a tape subgraph: its index and the interior vertices. -/
structure Realized where
  occ : Nat
  interior : List Nat := []
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- The rung of the carrier ladder a module runs at, and the platform realizing it. -/
structure Carrier where
  rung : String
  platform : Option String := none
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- The component table and realized occurrences relating a module's hypergraph to a tape. -/
structure TapeMatch where
  name : String
  moduleName : String
  tape : String
  components : List NodeComponents := []
  realized : List Realized := []
  carrier : Option Carrier := none
  source : Option String := none
  checked : List Checked := []
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-! ## The model -/

/-- A PKC model in its neutral interchange form. `packageName` names the SysML package the
model is (or is emitted as); `imports` the PKC DSL packages it opens. -/
structure PkcModel where
  packageName : String
  doc : Option String := none
  principles : List Principle := []
  kinds : List Kind := []
  edges : List Edge := []
  dedicated : List Dedicated := []
  units : List MetrologicalUnit := []
  modules : List MetrologyModule := []
  relations : List Relation := []
  requirements : List Requirement := []
  tapes : List Tape := []
  tapeMatches : List TapeMatch := []
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- The model's JSON text. -/
def PkcModel.toJsonString (m : PkcModel) : String := (Lean.toJson m).pretty

/-- Parse a model from JSON text. -/
def PkcModel.ofJsonString (s : String) : Except String PkcModel := do
  let j ← Lean.Json.parse s
  Lean.fromJson? j

/-- Look a kind up by the name it is declared under. -/
def PkcModel.kind? (m : PkcModel) (name : String) : Option Kind :=
  m.kinds.find? (·.name == name)

/-- The identifiers a model declares, in declaration order, for duplicate checks. -/
def PkcModel.names (m : PkcModel) : List String :=
  m.principles.map (·.name) ++ m.kinds.map (·.name) ++ m.edges.map (·.name)
    ++ m.dedicated.map (·.name) ++ m.units.map (·.name) ++ m.modules.map (·.name)
    ++ m.relations.map (·.name) ++ m.requirements.map (·.name) ++ m.tapes.map (·.name)
    ++ m.tapeMatches.map (·.name)

end PropertyKindCalculus.Interchange

end Blanket
