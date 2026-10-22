/-
# `Harvest` — read a PKC model out of the Lean environment

The Lean → SysML half of the interchange. Given a scope (namespace prefixes), the harvester
walks the environment and reads every declaration the PKC DSL has a keyword for into a
`PkcModel`:

* **kinds** — constants of type `KindOfProperty`, `DimensionedKind` and `CataloguedKind`,
  *evaluated* for their identity, scale, examination principle, dimension vector and
  catalogue locators; constants of type `ExaminationPrinciple` as `#principle`s;
  `DedicatedKind` and `MetrologicalUnit` constants likewise;
* **specialization** — every inductive `E : KindOfProperty → KindOfProperty → Prop` is an
  authored edge relation (`Specializes E`); each constructor `E a b` makes `a` specialize `b`
  and is cited as the edge's checked declaration;
* **the kind algebra** — `KindMul`/`KindDiv` instances (table edges) and declarations whose
  type *is* a witness `Prop` (`ProductKind k₁ k₂ k`, …) with constant kinds;
* **modules** — `Provenance.Contract NodeId KindRef` constants, read by the same evaluator
  `#kind_contract` uses, with the provenance hypergraph of each member the assembly
  computes for it (`stepGraphOf`); `Provenance.Relation` and `Provenance.Requirement`
  constants as `#relation`s and `#req`s;
* **tapes** — `TapeGraph` constants.

Every element records the declaration it came from (`source`), so the SysML side can cite
it back, and a round trip can compare models by content.

Evaluation is of *values*, never of proofs: a theorem is cited by name, not run. What the
harvester cannot resolve to a declared kind (a kind bound by a binder, a tuple signature) is
rendered as text and left to the reader.

A declaration the harvester cannot *read* — a value that fails to evaluate, a contract or a
member's hypergraph the assembly refuses, a dedicated kind or unit whose kind is not in scope
— is skipped rather than failing the harvest, and the skip is reported as a warning next to
the model (as `ApiJson.read` reports the elements it cannot place), so a partial harvest is
never mistaken for a complete one.
-/

module

public import Lean
public import PropertyKindCalculus.KindEdges
public import PropertyKindCalculus.KindIncidence
public import PropertyKindCalculus.Requirement
public import PropertyKindCalculus.Paradigm.TapeGraph
public import PropertyKindCalculus.Iso80000.Catalogue
public import PropertyKindCalculus.Interchange.Model

set_option compiler.relaxedMetaCheck true

public section Interface

namespace PropertyKindCalculus.Interchange.Harvest

open Lean Meta
open PropertyKindCalculus
open PropertyKindCalculus.Interchange

/-! ## Evaluable views of the spine's records

`Meta.evalExpr` runs a closed term of a given type; these plain records are what it is asked
for, so the harvester never evaluates a PhysLib `Dimension` or a `Lean.Name` structure it
would have to interpret itself. -/

/-- A kind as read from a `KindOfProperty`, `DimensionedKind` or `CataloguedKind` constant. -/
structure KindData where
  id : String
  scale : Scale
  principle : Option String := none
  dimension : List DimExponent := []
  standardRef : Option String := none
  catalogueItem : Option String := none
  symbol : Option String := none
  coherentUnit : Option String := none
deriving Repr, Inhabited

def Scale.ofScaleType : ScaleType → Scale
  | .nominal => .nominal | .ordinal => .ordinal | .interval => .interval | .ratio => .ratio

def KindData.ofKind (k : KindOfProperty) : KindData :=
  { id := k.id, scale := Scale.ofScaleType k.scale, principle := k.examPrinciple }

/-- The dimension vector over PhysLib's `LTMCTDimensionBase`, zero exponents omitted. -/
def dimensionVector (d : Dimension LTMCTDimensionBase) : List DimExponent :=
  [("length", d.length), ("time", d.time), ("mass", d.mass), ("charge", d.charge),
   ("temperature", d.temperature)].filterMap fun (b, q) =>
    if q == 0 then none else some { base := b, num := q.num, den := q.den }

def KindData.ofDimensioned (d : DimensionedKind) : KindData :=
  { KindData.ofKind d.kind with dimension := dimensionVector d.dim }

def KindData.ofCatalogued (c : Iso80000.CataloguedKind) : KindData :=
  { KindData.ofDimensioned c.qk with
    standardRef := some c.ref.cite, catalogueItem := some c.item, symbol := some c.symbol,
    coherentUnit := some c.coherentUnit }

/-- A dedicated kind, with the `KindOfProperty` identity its `kind` is matched back by. -/
structure DedicatedData where
  sort : String
  component : String
  kindId : String
deriving Repr, Inhabited

def DedicatedData.of (d : DedicatedKind) : DedicatedData :=
  { sort := d.sort.id, component := d.component.id, kindId := d.kind.id }

/-- A unit, with the identity of the kind it measures. -/
structure UnitData where
  kindId : String
  symbol : String
deriving Repr, Inhabited

def UnitData.of (u : PropertyKindCalculus.MetrologicalUnit) : UnitData :=
  { kindId := u.kind.id, symbol := u.symbol }

/-! ## The harvester's state -/

/-- The harvester's working state: the model under construction, the table from kind
declarations to element names, and the warnings — one per declaration in scope the
harvester skipped, naming it and the reason. -/
structure State where
  model : PkcModel
  kindOf : Std.HashMap Name String := {}
  kindById : Std.HashMap String String := {}
  warnings : Array String := #[]

abbrev HarvestM := StateRefT State MetaM

/-- Record a warning — a declaration the harvester skipped — without failing. -/
def warn (msg : String) : HarvestM Unit :=
  modify fun s => { s with warnings := s.warnings.push msg }

/-- Run a reader for the declaration `c`, or `none` — with a warning naming `c`, `what` was
not read and why — when it throws: the harvester skips what it cannot read rather than
failing the harvest. -/
def attempt {α : Type} (c : Name) (what : String) (act : MetaM α) : HarvestM (Option α) :=
  try some <$> act
  catch ex => do warn s!"{c}: {what} not read: {← ex.toMessageData.toString}"; return none

unsafe def evalUnsafe (α : Type) (ty e : Expr) : MetaM α := Meta.evalExpr α ty e

/-- Evaluate a closed term at a type. Replaced at run time by the evaluator. -/
@[implemented_by evalUnsafe]
def eval (α : Type) (_ty _e : Expr) : MetaM α :=
  throwError "values cannot be read in this environment"

/-- Evaluate a term of the declaration `c`, or `none` — with a warning — when it cannot be
read (a noncomputable value, a failed compilation). -/
def eval? (α : Type) (c : Name) (ty e : Expr) : HarvestM (Option α) :=
  attempt c "value" (eval α ty e)

def evalKindData (view : Name) (c : Name) : HarvestM (Option KindData) :=
  eval? KindData c (mkConst ``KindData) (mkApp (mkConst view) (mkConst c))

def evalString (c : Name) (e : Expr) : HarvestM (Option String) :=
  eval? String c (mkConst ``String) e

/-! ## Scope and naming -/

/-- Is a declaration in scope — under one of the prefixes, and authored (not internal,
not auxiliary)? An empty scope admits every authored declaration. -/
def inScope (scope : Array Name) (n : Name) : Bool :=
  !n.isInternal && !n.isInternalDetail
    && (scope.isEmpty || scope.any fun p => p.isPrefixOf n)

/-- The constants of the environment in scope, in a stable (sorted) order. -/
def scopedConstants (env : Environment) (scope : Array Name) : Array Name :=
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if inScope scope n then acc.push n else acc
  names.qsort (toString · < toString ·)

/-- The element name of a declaration: its last component, or — when another declaration
in scope shares that last component — its last two, joined by `_`. -/
def elementName (taken : Std.HashMap String Nat) (n : Name) : String :=
  let last := n.lastComponentAsString
  if taken.getD last 0 ≤ 1 then last
  else match n with
    | .str (.str _ p) _ => s!"{p}_{last}"
    | _ => last

/-- Is the declaration's type (under no binders) headed by the constant `ty`? Arity is
not checked: `DimensionedKind` carries its basis and instance as arguments. -/
def hasTypeHead (env : Environment) (n : Name) (ty : Name) : Bool :=
  match env.find? n with
  | some ci => ci.type.getAppFn.isConstOf ty
  | none => false

/-- The kind constant an expression denotes: `c`, `c.kind` (a `DimensionedKind`'s kind) or
`c.qk.kind` (a `CataloguedKind`'s). `none` for anything else — a bound kind, a literal. -/
partial def kindConstOf? (e : Expr) : Option Name :=
  match e with
  | .const c _ => some c
  | .mdata _ b => kindConstOf? b
  | _ =>
    if e.isAppOf ``DimensionedKind.kind then kindConstOf? e.appArg!
    else if e.isAppOf ``Iso80000.CataloguedKind.qk then kindConstOf? e.appArg!
    else if e.isAppOf ``DimensionedKind.dim then none
    else match e.getAppFn with
      | .const c _ => if e.getAppNumArgs == 0 then some c else none
      | _ => none

/-! ## The harvest -/

def kindName? (n : Name) : HarvestM (Option String) := do
  return (← get).kindOf[n]?

/-- The element name of the kind an expression denotes, for the edge `what` of the declaration
`c`. `none` — with a warning — when it names a kind in scope (`consts`) the harvester skipped;
`none` silently for a kind outside the scope or no constant kind at all (a bound kind, a
literal), which leaves the edge to the reader. -/
def kindNameOfExpr? (consts : Array Name) (c : Name) (what : String) (e : Expr) :
    HarvestM (Option String) := do
  let some k := kindConstOf? e | return none
  if let some name ← kindName? k then return some name
  if consts.contains k then warn s!"{c}: {what} skipped: its kind {k} was not harvested"
  return none

def kindNameById? (id : String) : HarvestM (Option String) := do
  return (← get).kindById[id]?

def modifyModel (f : PkcModel → PkcModel) : HarvestM Unit :=
  modify fun s => { s with model := f s.model }

/-- Harvest the kinds: every `KindOfProperty`, `DimensionedKind` and `CataloguedKind`
constant, keyed by element name. A catalogued kind and the dimensioned kind it wraps are one
element — the catalogue entry enriches the kind it cites rather than duplicating it. -/
def harvestKinds (consts : Array Name) : HarvestM Unit := do
  let env ← getEnv
  let views : List (Name × Name) :=
    [(``KindOfProperty, ``KindData.ofKind), (``DimensionedKind, ``KindData.ofDimensioned),
     (``Iso80000.CataloguedKind, ``KindData.ofCatalogued)]
  let mut kindConsts : Array (Name × Name) := #[]
  for c in consts do
    for (ty, view) in views do
      if hasTypeHead env c ty then kindConsts := kindConsts.push (c, view)
  let taken : Std.HashMap String Nat := kindConsts.foldl (init := {}) fun m (c, view) =>
    if view == ``KindData.ofCatalogued then m
    else m.alter c.lastComponentAsString fun | some k => some (k + 1) | none => some 1
  for (c, view) in kindConsts do
    let some data ← evalKindData view c | continue
    if view == ``KindData.ofCatalogued then
      match (← get).kindById[data.id]? with
      | some name =>
        modify fun s => { s with kindOf := s.kindOf.insert c name }
        modifyModel fun m => { m with kinds := m.kinds.map fun k =>
          if k.name != name then k else
            { k with dimension := if k.dimension.isEmpty then data.dimension else k.dimension,
                     standardRef := data.standardRef, catalogueItem := data.catalogueItem,
                     symbol := data.symbol, coherentUnit := data.coherentUnit } }
        continue
      | none => pure ()
    let name := elementName taken c
    if (← get).kindById.contains data.id && (← get).model.kinds.any (·.name == name) then
      modify fun s => { s with kindOf := s.kindOf.insert c name }
      continue
    let k : Kind :=
      { name, id := data.id, scale := data.scale, principle := data.principle,
        dimension := data.dimension, standardRef := data.standardRef,
        catalogueItem := data.catalogueItem, symbol := data.symbol,
        coherentUnit := data.coherentUnit, source := some (toString c) }
    modify fun s => { s with kindOf := s.kindOf.insert c name,
                             kindById := s.kindById.insertIfNew data.id name,
                             model := { s.model with kinds := s.model.kinds ++ [k] } }

/-- Harvest the examination principles, and bind each kind's `examPrinciple` string to the
principle element carrying that id. -/
def harvestPrinciples (consts : Array Name) : HarvestM Unit := do
  let env ← getEnv
  let ps := consts.filter (hasTypeHead env · ``ExaminationPrinciple)
  let taken : Std.HashMap String Nat := ps.foldl (init := {}) fun m c =>
    m.alter c.lastComponentAsString fun | some k => some (k + 1) | none => some 1
  let mut byId : Std.HashMap String String := {}
  for c in ps do
    let some id ← evalString c (mkApp (mkConst ``ExaminationPrinciple.id) (mkConst c)) | continue
    let name := elementName taken c
    byId := byId.insertIfNew id name
    modifyModel fun m => { m with principles := m.principles ++
      [{ name, id, source := some (toString c) }] }
  -- a kind whose principle is declared outside the scope keeps it: the id becomes a
  -- principle element of its own (named after the id), cited to no declaration
  let mut extra : List Principle := []
  for k in (← get).model.kinds do
    if let some id := k.principle then
      unless byId.contains id do
        let name := id.map fun c => if c.isAlphanum then c else '_'
        extra := extra ++ [{ name := name, id := id }]
        byId := byId.insert id name
  modifyModel fun m => { m with
    principles := m.principles ++ extra,
    kinds := m.kinds.map fun k =>
      match k.principle with
      | some id => { k with principle := byId[id]? }
      | none => k }

/-- Harvest the dedicated kinds and units. -/
def harvestDedicatedAndUnits (consts : Array Name) : HarvestM Unit := do
  let env ← getEnv
  for c in consts do
    if hasTypeHead env c ``DedicatedKind then
      let some d ← eval? DedicatedData c (mkConst ``DedicatedData)
          (mkApp (mkConst ``DedicatedData.of) (mkConst c)) | continue
      let some kind ← kindNameById? d.kindId
        | warn s!"{c}: dedicated kind skipped: its kind '{d.kindId}' is not a harvested kind"; continue
      modifyModel fun m => { m with dedicated := m.dedicated ++
        [{ name := c.lastComponentAsString, sort := d.sort, component := d.component, kind,
           source := some (toString c) }] }
    else if hasTypeHead env c ``PropertyKindCalculus.MetrologicalUnit then
      let some u ← eval? UnitData c (mkConst ``UnitData)
          (mkApp (mkConst ``UnitData.of) (mkConst c)) | continue
      let some kind ← kindNameById? u.kindId
        | warn s!"{c}: unit skipped: its kind '{u.kindId}' is not a harvested kind"; continue
      modifyModel fun m => { m with units := m.units ++
        [{ name := c.lastComponentAsString, kind, symbol := u.symbol,
           source := some (toString c) }] }

/-- Is `n` an authored edge relation — an inductive of type
`KindOfProperty → KindOfProperty → Prop`? -/
def isEdgeRelation (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo info) =>
    match info.type with
    | .forallE _ (.const ``KindOfProperty _) (.forallE _ (.const ``KindOfProperty _) (.sort 0) _) _ => true
    | _ => false
  | _ => false

/-- Harvest specialization: each constructor `E a b` of an edge relation. -/
def harvestSpecialization (consts : Array Name) : HarvestM Unit := do
  let env ← getEnv
  for rel in consts.filter (isEdgeRelation env ·) do
    let some (.inductInfo info) := env.find? rel | continue
    for ctor in info.ctors do
      let some ci := env.find? ctor | continue
      let concl := ci.type.getForallBody
      unless concl.isAppOfArity rel 2 do continue
      let args := concl.getAppArgs
      let some a ← kindNameOfExpr? consts ctor "specialization" args[0]! | continue
      let some b ← kindNameOfExpr? consts ctor "specialization" args[1]! | continue
      modifyModel fun m => { m with kinds := m.kinds.map fun k =>
        if k.name != a then k else
          { k with specializes := if k.specializes.contains b then k.specializes else k.specializes ++ [b],
                   checked := k.checked ++ [{ decl := toString ctor }] } }

/-- The DSL family of each witness law. -/
def edgeKindOfLaw : KindEdges.EdgeLaw → EdgeKind
  | .product => .product | .quotient => .quotient | .reciprocal => .reciprocal
  | .transcendental => .transcendental | .power => .power | .reference => .reference
  | .additive => .difference

/-- The DSL family of each witness constant, with whether it is a table registration —
read off the constant's registry entry in `KindEdges.specs`. -/
def edgeFamilyOf (c : Name) : Option (EdgeKind × Bool) :=
  (KindEdges.specOf? c).map fun spec => (edgeKindOfLaw spec.law, spec.isTable)

/-- The power exponent of the witness `c`, a rational literal as an expression
`OfScientific`/`OfNat` builds it, read by evaluation; `none` — with a warning naming the
exponent, since the edge is still harvested without it — when it cannot be read. -/
def evalRat (c : Name) (e : Expr) : HarvestM (Option Rat) :=
  attempt c "power exponent" (eval Rat (mkConst ``Rat) e)

/-- Harvest the kind algebra: declarations whose type is a witness `Prop` over constant
kinds — instances of `KindMul`/`KindDiv` and authored `ProductKind …` facts. -/
def harvestAlgebra (consts : Array Name) : HarvestM Unit := do
  let env ← getEnv
  for c in consts do
    let some ci := env.find? c | continue
    let concl := ci.type.getForallBody
    let some spec := concl.getAppFn.constName?.bind KindEdges.specOf? | continue
    let fam := edgeKindOfLaw spec.law
    let table := spec.isTable
    let args := concl.getAppArgs
    let (kindArgs, exp?) ← match spec.exponent with
      | some i => pure ((args.eraseIdx! i).toList, ← evalRat c args[i]!)
      | none => pure (args.toList, none)
    let mut names : List String := []
    let mut ok := true
    for a in kindArgs do
      if ok then
        match ← kindNameOfExpr? consts c "edge" a with
        | some n => names := names ++ [n]
        | none => ok := false
    unless ok do continue
    let (operands, result) := match fam with
      | .difference => (names, none)
      | _ => (names.dropLast, names.getLast?)
    let edge : Edge :=
      { name := c.lastComponentAsString, kind := fam, operands, result, table,
        powerNum := exp?.map (·.num), powerDen := exp?.map (·.den),
        source := some (toString c) }
    modifyModel fun m => { m with edges := m.edges ++ [edge] }

/-! ## Modules, relations, requirements -/

def PortDir.ofProvenance : Provenance.PortDir → PortDir
  | .input => .input | .config => .config | .param => .param | .output => .output
  | .conditional => .conditional

def IntroTier.ofProvenance : Provenance.IntroTier → IntroTier × Option String
  | .derived => (.derived, none) | .gated => (.gated, none)
  | .attested r => (.attested, some r)

def BoundaryRole.ofProvenance : Provenance.BoundaryRole → BoundaryRole
  | .model => .model | .specification => .specification

def Aggregation.ofClass (node : String) : Provenance.AggregationClass → Aggregation
  | .extensive => { node, cls := .extensive }
  | .quasiExtensive t => { node, cls := .quasiExtensive, witness := some (toString t) }
  | .conditionallyExtensive c => { node, cls := .conditionallyExtensive, witness := some (toString c) }
  | .intensive => { node, cls := .intensive }
  | .wholeProper => { node, cls := .wholeProper }
  | .countKeyed s => { node, cls := .countKeyed, witness := some (toString s) }
  | .extensiveAbout t => { node, cls := .extensiveAbout, witness := some (toString t) }
  | .interfaceLicensed l => { node, cls := .interfaceLicensed, witness := some (toString l) }

def RelationKind.ofProvenance : Provenance.RelationKind → RelationKind
  | .inverts => .inverts | .refines => .refines | .equals => .equals | .boundedBy => .boundedBy

def License.ofProvenance (l : Provenance.RelationLicense) : License :=
  match l.transfer with
  | .exact r => { rung := l.rung, transfer := .exact, witness := toString r }
  | .nonneg r => { rung := l.rung, transfer := .nonneg, witness := toString r }
  | .restated w => { rung := l.rung, transfer := .restated, witness := toString w }

def RequirementKind.ofProvenance : Provenance.RequirementKind → RequirementKind
  | .provable => .provable | .empirical => .empirical

def ReqScope.ofProvenance : Provenance.RequirementScope → ReqScope
  | .all => .all
  | .sort s => .sort (toString s)
  | .objects os => .objects (os.map toString)
  | .decided d => .decided (toString d)

def optName (n : Name) : Option String := if n.isAnonymous then none else some (toString n)

/-- The kind element a `KindRef` names: the declared kind for `.decl`, otherwise its
rendering (a parameter, a signature, a tuple). -/
def kindOfRef (r : Provenance.KindRef) : HarvestM String := do
  match r with
  | .decl n => return (← kindName? n).getD (toString n)
  | r => return r.render

def familyOf (f : Provenance.EdgeFamily) :
    EdgeFamily × Option String × Option Nat × Option Nat × Option Int × Option Nat :=
  match f with
  | .product => (.product, none, none, none, none, none)
  | .quotient => (.quotient, none, none, none, none, none)
  | .reciprocal => (.reciprocal, none, none, none, none, none)
  | .transcendental => (.transcendental, none, none, none, none, none)
  | .power e => (.power, none, none, none, some e.num, some e.den)
  | .reference => (.reference, none, none, none, none, none)
  | .additive => (.additive, none, none, none, none, none)
  | .tableMul => (.tableMul, none, none, none, none, none)
  | .tableDiv => (.tableDiv, none, none, none, none, none)
  | .copy => (.copy, none, none, none, none, none)
  | .step m i a => (.step, some (toString m), i, some a, none, none)
  | .select n => (.select, none, none, some n, none, none)

def occurrenceOf (o : Provenance.Occurrence Provenance.NodeId Provenance.KindRef) :
    HarvestM Occurrence := do
  let (family, member, inst, arity, powerNum, powerDen) := familyOf o.family
  let operands ← o.operands.mapM fun (n, k) => do
    return ({ node := n.render, kind := ← kindOfRef k } : Operand)
  return { family, operands, result := o.result.render, resultKind := ← kindOfRef o.resultKind,
           site := o.site, op := optName o.op, member, inst, arity, powerNum, powerDen }

/-- The provenance hypergraph of a contract's members, as the assembly computes it; a
member the assembly cannot read contributes nothing (the boundary is still harvested) and
is warned about. -/
def provenanceOf (members : List Name) : HarvestM (List Intro × List Occurrence) := do
  let mut intros : List Intro := []
  let mut occs : List Occurrence := []
  for m in members do
    let some g ← attempt m "hypergraph" (KindIncidence.stepGraphOf m) | continue
    let p := g.provenance
    for i in p.intros do
      let (tier, reason) := IntroTier.ofProvenance i.tier
      intros := intros ++ [{ node := i.node.render, kind := ← kindOfRef i.kind, tier, reason }]
    for o in p.occurrences do
      occs := occs ++ [← occurrenceOf o]
  return (intros, occs)

/-- Harvest the metrology modules: every `Provenance.Contract NodeId KindRef` constant. -/
def harvestModules (consts : Array Name) : HarvestM Unit := do
  let env ← getEnv
  for c in consts do
    unless hasTypeHead env c ``Provenance.Contract do continue
    let some ci := env.find? c | continue
    unless ci.type.appFn!.appArg!.isConstOf ``Provenance.NodeId
        && ci.type.appArg!.isConstOf ``Provenance.KindRef do continue
    let some k ← attempt c "contract" (KindIncidence.contractValueOf c) | continue
    let ports ← k.ports.mapM fun p => do
      let node := p.node.render
      return ({ name := node, node, kind := ← kindOfRef p.kind, dir := PortDir.ofProvenance p.dir } : Port)
    let (intros, occurrences) ← provenanceOf k.members
    let m : MetrologyModule :=
      { name := c.lastComponentAsString, title := k.name, members := k.members.map toString, ports,
        exits := k.exits.map (·.render),
        deciders := k.deciders.map fun (n, d) => (n.render, toString d),
        aggregations := k.aggregations.map fun (n, a) => Aggregation.ofClass n.render a,
        suppliers := k.suppliers.map fun (n, d) => (n.render, toString d),
        role := BoundaryRole.ofProvenance k.role,
        -- the assembly read wiring for at least one member: the hypergraph is stated
        hypergraph := !(intros.isEmpty && occurrences.isEmpty), intros, occurrences,
        source := some (toString c) }
    modifyModel fun m' => { m' with modules := m'.modules ++ [m] }

/-- The module element a contract declaration names. -/
def moduleNameOf (n : Name) : HarvestM String := do
  return ((← get).model.modules.find? (·.source == some (toString n))).map (·.name)
    |>.getD (toString n)

def harvestRelations (consts : Array Name) : HarvestM Unit := do
  let env ← getEnv
  for c in consts do
    unless hasTypeHead env c ``Provenance.Relation do continue
    let some r ← eval? Provenance.Relation c (mkConst ``Provenance.Relation) (mkConst c) | continue
    let rel : Relation :=
      { name := c.lastComponentAsString, left := ← moduleNameOf r.left, right := ← moduleNameOf r.right,
        kind := RelationKind.ofProvenance r.kind, witness := toString r.witness,
        claim := if r.claim.isEmpty then none else some r.claim, tolerance := optName r.tolerance,
        hypotheses := r.hypotheses.map toString, licenses := r.licenses.map License.ofProvenance,
        wellPosed := optName r.wellPosed, domain := optName r.domain, ambiguity := optName r.ambiguity,
        source := some (toString c) }
    modifyModel fun m => { m with relations := m.relations ++ [rel] }

def harvestRequirements (consts : Array Name) : HarvestM Unit := do
  let env ← getEnv
  for c in consts do
    unless hasTypeHead env c ``Provenance.Requirement do continue
    let some r ← eval? Provenance.Requirement c (mkConst ``Provenance.Requirement) (mkConst c) | continue
    let req : Requirement :=
      { name := c.lastComponentAsString, title := r.name, statement := r.statement,
        kind := RequirementKind.ofProvenance r.kind, governs := ← moduleNameOf r.governs,
        port := r.port.map (·.render), scope := ReqScope.ofProvenance r.scope, witness := optName r.witness,
        spotChecks := r.spotChecks.map toString, absent := optName r.absent,
        referents := r.referents.map toString, source := some (toString c) }
    modifyModel fun m => { m with requirements := m.requirements ++ [req] }

/-! ## Tapes -/

def harvestTapes (consts : Array Name) : HarvestM Unit := do
  let env ← getEnv
  for c in consts do
    unless hasTypeHead env c ``Paradigm.TapeGraph do continue
    let some t ← eval? Paradigm.TapeGraph c (mkConst ``Paradigm.TapeGraph) (mkConst c) | continue
    let tape : Tape :=
      { name := c.lastComponentAsString,
        vertices := t.vertices.map fun v => { name := v.name, parents := v.parents },
        source := some (toString c) }
    modifyModel fun m => { m with tapes := m.tapes ++ [tape] }

/-! ## Citations -/

/-- Every `source` citation of a model, with the element citing it. -/
def sourcesOf (m : PkcModel) : List (String × String) :=
  (m.principles.filterMap fun p => p.source.map (p.name, ·))
    ++ (m.kinds.filterMap fun k => k.source.map (k.name, ·))
    ++ (m.edges.filterMap fun e => e.source.map (e.name, ·))
    ++ (m.dedicated.filterMap fun d => d.source.map (d.name, ·))
    ++ (m.units.filterMap fun u => u.source.map (u.name, ·))
    ++ (m.modules.filterMap fun b => b.source.map (b.name, ·))
    ++ (m.relations.filterMap fun r => r.source.map (r.name, ·))
    ++ (m.requirements.filterMap fun r => r.source.map (r.name, ·))
    ++ (m.tapes.filterMap fun t => t.source.map (t.name, ·))
    ++ (m.tapeMatches.filterMap fun x => x.source.map (x.name, ·))

/-- Every `checked` citation of a model, with the element citing it. -/
def checkedOf (m : PkcModel) : List (String × Checked) :=
  (m.kinds.flatMap fun k => k.checked.map (k.name, ·))
    ++ (m.edges.flatMap fun e => e.checked.map (e.name, ·))
    ++ (m.modules.flatMap fun b => b.checked.map (b.name, ·))
    ++ (m.tapes.flatMap fun t => t.checked.map (t.name, ·))
    ++ (m.tapeMatches.flatMap fun x => x.checked.map (x.name, ·))

/-- Every declaration a model cites, as `source` or `checked`, with the element citing it. -/
def citationsOf (m : PkcModel) : List (String × String) :=
  sourcesOf m ++ (checkedOf m).map fun (n, c) => (n, c.decl)

/-- The axioms a kernel-checked proof may rest on. -/
def admittedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Why a declaration is not evidence — or `none` when it is: a theorem, a constructor of a
`Prop`, or a `Prop`-typed definition or instance, whose proof rests on no axiom beyond
`admittedAxioms` (so neither an `axiom` itself, nor anything `sorry`ed or `ofReduceBool`ed). -/
def notEvidence (env : Environment) (n : Name) : MetaM (Option String) := do
  let some ci := env.find? n | return some "is not a declaration of the environment"
  let shape ← match ci with
    | .axiomInfo _ =>
      -- a `module` sees every imported theorem as an axiom (proofs are not imported); the
      -- scripts run outside the module system, where a theorem is a theorem
      if env.header.isModule then
        pure (some "is an axiom or a theorem whose proof this module cannot see; verify from a script")
      else pure (some "is an axiom, not a proof")
    | .thmInfo _ => pure none
    | .ctorInfo _ => do
      if ← Meta.isProp ci.type then pure none else pure (some "constructs data, not a proposition")
    | _ => do
      -- an instance counts only as any other definition does: by proving a proposition
      -- (`KindMul`/`KindDiv` are `Prop` classes; `Inhabited`/`DecidableEq` instances are data)
      if ← Meta.isProp ci.type then pure none
      else pure (some "is data, not evidence (cite it as a source)")
  if let some why := shape then return some why
  let axioms ← collectAxioms n
  let foreign := axioms.filter (!admittedAxioms.contains ·)
  if foreign.isEmpty then return none
  return some s!"rests on {foreign.toList} — not a kernel-checked proof"

/-- The citations the environment cannot honour: sources it does not contain, and `checked`
citations that are not evidence (see `notEvidence`) — a citation of data is a `source`, not a
check, and an axiom or a `sorry` is not a proof. -/
def unverifiedCitations (m : PkcModel) : MetaM (List String) := do
  let env ← getEnv
  let mut out : List String := []
  for (elem, decl) in sourcesOf m do
    unless env.contains decl.toName do
      out := out ++ [s!"{elem}: source '{decl}' is not a declaration of the environment"]
  for (elem, c) in checkedOf m do
    let n := c.decl.toName
    if let some why ← notEvidence env n then
      out := out ++ [s!"{elem}: '{c.decl}' {why}"]
  return out

/-! ## Entry point -/

/-- Harvest the PKC model of a scope, with the warnings — the declarations in scope the
harvester skipped, and why. `packageName` names the SysML package it becomes. -/
def harvest (scope : Array Name) (packageName : String) : MetaM (PkcModel × Array String) := do
  let consts := scopedConstants (← getEnv) scope
  let act : HarvestM Unit := do
    harvestKinds consts
    harvestPrinciples consts
    harvestDedicatedAndUnits consts
    harvestSpecialization consts
    harvestAlgebra consts
    harvestModules consts
    harvestRelations consts
    harvestRequirements consts
    harvestTapes consts
  let (_, s) ← act.run { model := { packageName } }
  return (s.model, s.warnings)

end PropertyKindCalculus.Interchange.Harvest

end Interface
