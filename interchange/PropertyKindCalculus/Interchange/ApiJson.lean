/-
# `ApiJson` — read a PKC DSL model from OpenSysML's API element form

The SysML → Lean half of the interchange begins here. `sysml -convert api-json PKC.sysml
Model.sysml` writes the model as the OMG SysML v2 API's element list — one JSON object per
element, with `@id`, `@type` and the metamodel's properties as identifier references. This
module reads that list into a `PkcModel`, by the DSL's conventions:

* a **keyworded usage** is an element owning a `MetadataUsage` whose type is one of the DSL's
  semantic-metadata definitions; the definition's short name (`kind`, `product`, `module`, …)
  is the keyword;
* a **binding** `:>> f = v` is an owned feature with a `Redefinition`; its root — the feature
  of the DSL library it ultimately redefines, found by following `redefinedFeature` until an
  element of `PKC::…` — names the field, and its `FeatureValue` holds the value;
* a **nested record** `attribute x :> list { … }` is an owned feature with a `Subsetting` of a
  DSL list feature; a `#kind`'s subsetting of another `#kind` is specialization;
* a **connection**'s `connectorEnd`s each carry a `ReferenceSubsetting` to the element they
  bind, in the order of the connection definition's ends.

Values are literals, sequences (`OperatorExpression` `,`) and feature references (an
enumeration literal, a kind). Nothing is evaluated: the reader is a pure function of the
element list, and what it cannot place is reported, not dropped.
-/

module

public import Lean.Data.Json
public import PropertyKindCalculus.Interchange.Model

@[expose] public section Blanket

namespace PropertyKindCalculus.Interchange.ApiJson

open Lean (Json)
open PropertyKindCalculus.Interchange

/-- The properties of an API element this reader uses. Identifier references are kept as
the referenced `@id`. -/
structure Element where
  id : String
  type : String
  name : Option String := none
  shortName : Option String := none
  qualifiedName : Option String := none
  owner : Option String := none
  redefinedFeature : Option String := none
  subsettedFeature : Option String := none
  referencedFeature : Option String := none
  referent : Option String := none
  typeIds : List String := []
  value : Option String := none
  connectorEnds : List String := []
  operator : Option String := none
  literalStr : Option String := none
  literalInt : Option Int := none
  literalBool : Option Bool := none
  isDefault : Bool := false
deriving Repr, Inhabited

/-- A value as the DSL binds it. -/
inductive Val where
  | str (s : String)
  | int (n : Int)
  | bool (b : Bool)
  | ref (qualifiedName : String)
  | list (vs : List Val)
deriving Repr, BEq, Inhabited

/-- The indexed element list. -/
structure Doc where
  elements : Array Element
  byId : Std.HashMap String Element
  children : Std.HashMap String (Array String)

abbrev ReadM := ExceptT String (StateM (Array String))

/-- Record a warning — an element the reader could not place — without failing. -/
def warn (msg : String) : ReadM Unit := modify (·.push msg)

/-! ## Decoding the element list -/

def getStr? (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => some s
  | _ => none

def getId? (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok o => getStr? o "@id"
  | _ => none

def getIds (j : Json) (k : String) : List String :=
  match j.getObjVal? k with
  | .ok (.arr a) => a.toList.filterMap fun o => getStr? o "@id"
  | _ => []

def decodeElement (j : Json) : Option Element := do
  let id ← getStr? j "@id"
  let type ← getStr? j "@type"
  let literalInt := match j.getObjVal? "value" with
    | .ok (.num n) => if n.exponent == 0 then some n.mantissa else none
    | _ => none
  let literalBool := match j.getObjVal? "value" with
    | .ok (.bool b) => some b
    | _ => none
  return { id, type, name := getStr? j "declaredName", shortName := getStr? j "declaredShortName",
           qualifiedName := getStr? j "qualifiedName", owner := getId? j "owner",
           redefinedFeature := getId? j "redefinedFeature", subsettedFeature := getId? j "subsettedFeature",
           referencedFeature := getId? j "referencedFeature", referent := getId? j "referent",
           typeIds := getIds j "type", value := getId? j "value", connectorEnds := getIds j "connectorEnd",
           operator := getStr? j "operator",
           literalStr := if type == "LiteralString" then getStr? j "value" else none,
           literalInt, literalBool,
           isDefault := (match j.getObjVal? "isDefault" with | .ok (.bool b) => b | _ => false) }

/-- Index an element list: by id, and each element's owned elements in file order. -/
def Doc.ofJson (j : Json) : Except String Doc := do
  let .arr arr := j | throw "expected the API element list (a JSON array)"
  let elements := arr.filterMap decodeElement
  let byId := elements.foldl (init := {}) fun m e => m.insert e.id e
  let children := elements.foldl (init := ({} : Std.HashMap String (Array String))) fun m e =>
    match e.owner with
    | some o => m.alter o fun | some cs => some (cs.push e.id) | none => some #[e.id]
    | none => m
  return { elements, byId, children }

/-! ## Navigating -/

def Doc.get? (d : Doc) (id : String) : Option Element := d.byId[id]?

def Doc.kids (d : Doc) (id : String) : List Element :=
  (d.children.getD id #[]).toList.filterMap d.get?

/-- Is the element part of the DSL library rather than the model? -/
def Element.isLibrary (e : Element) : Bool :=
  (e.qualifiedName.getD "").startsWith "PKC::"

/-- The DSL feature a model feature ultimately redefines, by name. -/
partial def Doc.rootName? (d : Doc) (e : Element) (fuel : Nat := 64) : Option String :=
  if fuel == 0 then none
  else if e.isLibrary then e.name
  else match ((d.kids e.id).find? (·.type == "Redefinition") >>= (·.redefinedFeature) >>= d.get?) with
    | some target => d.rootName? target (fuel - 1)
    | none => none

/-- The value of an expression element. -/
partial def Doc.val? (d : Doc) (e : Element) : Option Val :=
  match e.type with
  | "LiteralString" => e.literalStr.map .str
  | "LiteralInteger" => e.literalInt.map .int
  | "LiteralRational" => e.literalInt.map .int
  | "LiteralBoolean" => e.literalBool.map .bool
  | "FeatureReferenceExpression" =>
    e.referent >>= d.get? >>= fun r => some (.ref (r.qualifiedName.getD (r.name.getD r.id)))
  | "OperatorExpression" =>
    let args := (d.kids e.id).filterMap fun p =>
      if p.type != "Feature" then none else
      let v := p.value <|> ((d.kids p.id).find? (·.type == "FeatureValue") >>= (·.value))
      v >>= d.get? >>= d.val?
    match e.operator, args with
    | some ",", _ => some (.list args)
    | some "-", [.int n] => some (.int (-n))
    | some "+", [.int n] => some (.int n)
    | _, _ => none
  | "NullExpression" => some (.list [])
  | _ => none

/-- The bound value of a feature element (`:>> f = v`, or the `value` of an end). -/
def Doc.valueOf? (d : Doc) (e : Element) : Option Val :=
  e.value >>= d.get? >>= d.val?

/-- The bindings of a usage: root field name ↦ value, for each owned redefining feature. -/
def Doc.bindings (d : Doc) (e : Element) : List (String × Val) :=
  (d.kids e.id).filterMap fun f =>
    if f.type == "MetadataUsage" then none else
    match d.rootName? f, d.valueOf? f with
    | some root, some v => some (root, v)
    | _, _ => none

/-- The nested records of a usage: the DSL list feature each owned subsetting feature
subsets, with the feature. -/
def Doc.nested (d : Doc) (e : Element) : List (String × Element) :=
  (d.kids e.id).filterMap fun f =>
    let target := (d.kids f.id).find? (·.type == "Subsetting") >>= (·.subsettedFeature) >>= d.get?
    match target with
    | some t => if t.isLibrary then t.name.map (·, f) else none
    | none =>
      -- `attribute :>> carrier { … }`: a redefining feature with a body and no value
      if f.value.isNone && f.type == "AttributeUsage" then d.rootName? f |>.map (·, f) else none

/-- Is the element a relationship or annotation rather than a model element? -/
def Element.isStructural (e : Element) : Bool :=
  e.type.endsWith "Membership" || e.type.endsWith "Import" || e.type == "Documentation"
    || e.type == "Comment" || e.type == "TextualRepresentation"

/-- The model elements a usage subsets — `#kind width :> length`'s `length`. -/
def Doc.subsetsModel (d : Doc) (e : Element) : List String :=
  (d.kids e.id).filterMap fun r =>
    if r.type != "Subsetting" then none else
    r.subsettedFeature >>= d.get? >>= fun t => if t.isLibrary then none else t.name

/-- The DSL keyword of a usage, from its semantic-metadata annotation. -/
def Doc.keyword? (d : Doc) (e : Element) : Option String :=
  (d.kids e.id).findSome? fun m =>
    if m.type != "MetadataUsage" then none else
    m.typeIds.head? >>= d.get? >>= fun t =>
      if t.isLibrary then t.shortName else none

/-- The `@Source` / `@Checked` citations of a usage. -/
def Doc.citations (d : Doc) (e : Element) : Option String × List Checked :=
  (d.kids e.id).foldl (init := (none, [])) fun (src, chk) m =>
    if m.type != "MetadataUsage" then (src, chk) else
    match m.typeIds.head? >>= d.get? >>= (·.name) with
    | some "Source" =>
      match d.bindings m |>.lookup "decl" with
      | some (.str s) => (some s, chk)
      | _ => (src, chk)
    | some "Checked" =>
      let b := d.bindings m
      match b.lookup "decl" with
      | some (.str s) =>
        let st := match b.lookup "statement" with | some (.str t) => some t | _ => none
        (src, chk ++ [{ decl := s, statement := st }])
      | _ => (src, chk)
    | _ => (src, chk)

/-- The elements bound by a connection's ends, in end order. -/
def Doc.ends (d : Doc) (e : Element) : List String :=
  e.connectorEnds.filterMap fun id =>
    d.get? id >>= fun en =>
      (d.kids en.id).findSome? fun r =>
        if r.type == "ReferenceSubsetting" then r.referencedFeature >>= d.get? >>= (·.name) else none

/-! ## Reading values -/

def lastSegment (q : String) : String :=
  match q.splitOn "::" |>.getLast? with
  | some s => s
  | none => q

def asStr : Val → Option String
  | .str s => some s
  | .ref q => some (lastSegment q)
  | _ => none

def asNat : Val → Option Nat
  | .int n => if n ≥ 0 then some n.toNat else none
  | _ => none

def asInt : Val → Option Int
  | .int n => some n
  | _ => none

def asBool : Val → Option Bool
  | .bool b => some b
  | _ => none

def asStrs : Val → List String
  | .list vs => vs.filterMap asStr
  | v => (asStr v).toList

def asNats : Val → List Nat
  | .list vs => vs.filterMap asNat
  | v => (asNat v).toList

def strField (b : List (String × Val)) (k : String) : Option String := b.lookup k >>= asStr
def natField (b : List (String × Val)) (k : String) : Option Nat := b.lookup k >>= asNat
def intField (b : List (String × Val)) (k : String) : Option Int := b.lookup k >>= asInt
def strsField (b : List (String × Val)) (k : String) : List String :=
  (b.lookup k).map asStrs |>.getD []

def need (b : List (String × Val)) (k : String) (ctx : String) : ReadM String :=
  match strField b k with
  | some s => pure s
  | none => throw s!"{ctx}: missing '{k}'"

def scaleOf (s : String) : ReadM Scale :=
  match s with
  | "nominal" => pure .nominal | "ordinal" => pure .ordinal
  | "interval" => pure .interval | "ratio" => pure .ratio
  | _ => throw s!"unknown scale type '{s}'"

def portDirOf : String → Option PortDir
  | "input" => some .input | "config" => some .config | "param" => some .param
  | "output" => some .output | "conditional" => some .conditional | _ => none

def tierOf : String → Option IntroTier
  | "derived" => some .derived | "gated" => some .gated | "attested" => some .attested | _ => none

def familyOf : String → Option EdgeFamily
  | "product" => some .product | "quotient" => some .quotient | "reciprocal" => some .reciprocal
  | "transcendental" => some .transcendental | "power" => some .power | "reference" => some .reference
  | "additive" => some .additive | "tableMul" => some .tableMul | "tableDiv" => some .tableDiv
  | "copy" => some .copy | "step" => some .step | "select" => some .select | _ => none

def roleOf : String → Option BoundaryRole
  | "model" => some .model | "specification" => some .specification | _ => none

def aggregationOf : String → Option AggregationKind
  | "extensive" => some .extensive | "quasiExtensive" => some .quasiExtensive
  | "conditionallyExtensive" => some .conditionallyExtensive | "intensive" => some .intensive
  | "wholeProper" => some .wholeProper | "countKeyed" => some .countKeyed
  | "extensiveAbout" => some .extensiveAbout | "interfaceLicensed" => some .interfaceLicensed
  | _ => none

def relationOf : String → Option RelationKind
  | "inverts" => some .inverts | "refines" => some .refines | "equals" => some .equals
  | "boundedBy" => some .boundedBy | _ => none

def transferOf : String → Option TransferKind
  | "exact" => some .exact | "nonneg" => some .nonneg | "restated" => some .restated | _ => none

def requirementOf : String → Option RequirementKind
  | "provable" => some .provable | "empirical" => some .empirical | _ => none

def enumField {α : Type} (b : List (String × Val)) (k : String) (parse : String → Option α)
    (ctx : String) : ReadM α := do
  let s ← need b k ctx
  match parse s with
  | some v => pure v
  | none => throw s!"{ctx}: unknown '{k}' literal '{s}'"

/-- The optional `scope` binding, read by `ReqScope.parse`. -/
def scopeField (b : List (String × Val)) (ctx : String) : ReadM ReqScope :=
  match ReqScope.parse (strField b "scope") with
  | .ok sc => pure sc
  | .error e => throw s!"{ctx}: {e}"

/-- The keyword and connection-definition name of each kind-algebra family. -/
def edgeKindOf : String → Option EdgeKind
  | "product" => some .product | "quotient" => some .quotient | "reciprocal" => some .reciprocal
  | "power" => some .power | "transcendental" => some .transcendental
  | "reference" => some .reference | "difference" => some .difference | _ => none

/-! ## Reading elements -/

def readPrinciple (d : Doc) (e : Element) : ReadM Principle := do
  let name := e.name.getD e.id
  let b := d.bindings e
  let (source, _) := d.citations e
  return { name, id := ← need b "id" s!"#principle {name}", source }

/-- A kind as read, and whether its `scale` was written. A species that subsets a genus may
omit the scale; `inheritFromGenus` then fills in the placeholder from the genus. -/
structure ReadKind where
  kind : Kind
  scaleWritten : Bool

def readKind (d : Doc) (e : Element) : ReadM ReadKind := do
  let name := e.name.getD e.id
  let b := d.bindings e
  let (source, checked) := d.citations e
  let dimension ← (d.nested e).filterMapM fun (root, f) => do
    if root != "dimension" then return none
    let fb := d.bindings f
    let base ← need fb "base" s!"#kind {name} dimension"
    let num := (intField fb "num").getD 0
    let den := (natField fb "den").getD 1
    return some ({ base, num, den } : DimExponent)
  let (scale, scaleWritten) ← match strField b "scale" with
    | some sc => do pure (← scaleOf sc, true)
    | none =>
      if (d.subsetsModel e).isEmpty then throw s!"#kind {name}: missing 'scale'"
      else pure (.ratio, false)
  let kind : Kind :=
    { name, id := ← need b "id" s!"#kind {name}", scale,
      principle := strField b "principle", specializes := d.subsetsModel e, dimension,
      standardRef := strField b "standardRef", catalogueItem := strField b "catalogueItem",
      symbol := strField b "symbol", coherentUnit := strField b "coherentUnit", source, checked }
  return { kind, scaleWritten }

def readEdge (d : Doc) (e : Element) (kind : EdgeKind) : ReadM Edge := do
  let name := e.name.getD e.id
  let b := d.bindings e
  let (source, checked) := d.citations e
  let ends := d.ends e
  let (operands, result) := match kind with
    | .difference => (ends, none)
    | _ => (ends.dropLast, ends.getLast?)
  return { name, kind, operands, result, table := (b.lookup "table" >>= asBool).getD false,
           powerNum := if kind == .power then intField b "num" else none,
           powerDen := if kind == .power then some ((natField b "den").getD 1) else none,
           source, checked }

def readDedicated (d : Doc) (e : Element) : ReadM Dedicated := do
  let name := e.name.getD e.id
  let b := d.bindings e
  let (source, _) := d.citations e
  return { name, sort := ← need b "sort" s!"#dedicated {name}",
           component := ← need b "component" s!"#dedicated {name}",
           kind := ← need b "kind" s!"#dedicated {name}", source }

def readUnit (d : Doc) (e : Element) : ReadM MetrologicalUnit := do
  let name := e.name.getD e.id
  let b := d.bindings e
  let (source, _) := d.citations e
  return { name, kind := ← need b "kind" s!"#unit {name}", symbol := ← need b "symbol" s!"#unit {name}",
           source }

def readOccurrence (d : Doc) (f : Element) (ctx : String) : ReadM Occurrence := do
  let b := d.bindings f
  let operands ← (d.nested f).filterMapM fun (root, op) => do
    if root != "operands" then return none
    let ob := d.bindings op
    return some ({ node := ← need ob "node" s!"{ctx} operand", kind := ← need ob "kind" s!"{ctx} operand" } : Operand)
  return { family := ← enumField b "family" familyOf ctx, operands,
           result := ← need b "result" ctx, resultKind := ← need b "resultKind" ctx,
           site := ← need b "site" ctx, op := strField b "op", member := strField b "member",
           inst := natField b "instance", arity := natField b "arity",
           powerNum := intField b "powerNum", powerDen := natField b "powerDen" }

def readModule (d : Doc) (e : Element) : ReadM MetrologyModule := do
  let name := e.name.getD e.id
  let ctx := s!"#module {name}"
  let b := d.bindings e
  let (source, checked) := d.citations e
  let ports ← (d.kids e.id).filterMapM fun p => do
    if p.type != "PortUsage" then return none
    let pb := d.bindings p
    return some ({ name := p.name.getD p.id, node := ← need pb "node" s!"{ctx} port",
                   kind := ← need pb "kind" s!"{ctx} port",
                   dir := ← enumField pb "dir" portDirOf s!"{ctx} port" } : Port)
  let mut aggregations : List Aggregation := []
  let mut intros : List Intro := []
  let mut occurrences : List Occurrence := []
  for (root, f) in d.nested e do
    let fb := d.bindings f
    match root with
    | "aggregations" =>
      let node ← need fb "node" s!"{ctx} aggregation"
      let cls ← enumField fb "class" aggregationOf s!"{ctx} aggregation"
      aggregations := aggregations ++ [{ node, cls, witness := strField fb "witness" }]
    | "intros" =>
      let node ← need fb "node" s!"{ctx} intro"
      let kind ← need fb "kind" s!"{ctx} intro"
      let tier ← enumField fb "tier" tierOf s!"{ctx} intro"
      intros := intros ++ [{ node, kind, tier, reason := strField fb "reason" }]
    | "occurrences" => occurrences := occurrences ++ [← readOccurrence d f s!"{ctx} occurrence"]
    | other => warn s!"{ctx}: unplaced nested '{other}'"
  let pair (s : String) : String × String :=
    match s.splitOn " := " with
    | [a, b] => (a, b)
    | _ => (s, "")
  return { name, title := (strField b "name").getD name, members := strsField b "members", ports,
           exits := strsField b "exits", deciders := (strsField b "deciders").map pair, aggregations,
           suppliers := (strsField b "suppliers").map pair,
           role := ((strField b "role") >>= roleOf).getD .model,
           hypergraph := (b.lookup "hypergraph" >>= asBool).getD false || !intros.isEmpty || !occurrences.isEmpty,
           intros, occurrences, source, checked }

def readRelation (d : Doc) (e : Element) : ReadM Relation := do
  let name := e.name.getD e.id
  let ctx := s!"#relation {name}"
  let b := d.bindings e
  let (source, _) := d.citations e
  let [left, right] := d.ends e | throw s!"{ctx}: expected two ends"
  let licenses ← (d.nested e).filterMapM fun (root, f) => do
    if root != "licenses" then return none
    let lb := d.bindings f
    return some ({ rung := ← need lb "rung" s!"{ctx} license",
                   transfer := ← enumField lb "transfer" transferOf s!"{ctx} license",
                   witness := ← need lb "witness" s!"{ctx} license" } : License)
  return { name, left, right, kind := ← enumField b "kind" relationOf ctx, witness := ← need b "witness" ctx,
           claim := strField b "claim", tolerance := strField b "tolerance",
           hypotheses := strsField b "hypotheses", licenses, wellPosed := strField b "wellPosed",
           domain := strField b "domain", ambiguity := strField b "ambiguity", source }

def readRequirement (d : Doc) (e : Element) : ReadM Requirement := do
  let name := e.name.getD e.id
  let ctx := s!"#req {name}"
  let b := d.bindings e
  let (source, _) := d.citations e
  return { name, title := (strField b "name").getD name, statement := ← need b "statement" ctx,
           kind := ← enumField b "kind" requirementOf ctx, governs := ← need b "governs" ctx,
           port := strField b "port", scope := ← scopeField b ctx, witness := strField b "witness",
           spotChecks := strsField b "spotChecks", absent := strField b "absent",
           referents := strsField b "referents", source }

def readTape (d : Doc) (e : Element) : ReadM Tape := do
  let name := e.name.getD e.id
  let (source, checked) := d.citations e
  let vertices := (d.nested e).filterMap fun (root, f) =>
    if root != "vertices" then none else
    let vb := d.bindings f
    some ({ name := strField vb "name", parents := (vb.lookup "parents").map asNats |>.getD [] } : TapeVertex)
  return { name, vertices, source, checked }

def readMatch (d : Doc) (e : Element) : ReadM TapeMatch := do
  let name := e.name.getD e.id
  let ctx := s!"#match {name}"
  let (source, checked) := d.citations e
  let [moduleName, tape] := d.ends e | throw s!"{ctx}: expected two ends"
  let mut components : List NodeComponents := []
  let mut realized : List Realized := []
  let mut carrier : Option Carrier := none
  for (root, f) in d.nested e do
    let fb := d.bindings f
    match root with
    | "components" =>
      let node ← need fb "node" s!"{ctx} component"
      components := components ++ [{ node, vertices := ((fb.lookup "vertices").map asNats).getD [] }]
    | "realized" =>
      realized := realized ++ [{ occ := (natField fb "occ").getD 0,
                                 interior := ((fb.lookup "interior").map asNats).getD [] }]
    | "carrier" =>
      let rung ← need fb "rung" s!"{ctx} carrier"
      carrier := some { rung, platform := strField fb "platform" }
    | other => warn s!"{ctx}: unplaced nested '{other}'"
  return { name, moduleName, tape, components, realized, carrier, source, checked }

/-- A species written without a dimension vector or a scale inherits its genus's — the
subsetting carries both, and the emitter omits a vector the genus already states.
`unscaled` names the kinds whose scale was not written. -/
def inheritFromGenus (m : PkcModel) (unscaled : List String) : Except String PkcModel := do
  let step (ks : List Kind) (open_ : List String) : List Kind × List String :=
    ks.foldl (init := ([], open_)) fun (acc, open_) k =>
      let genus := k.specializes.findSome? fun g => ks.find? (·.name == g)
      -- the vector comes from the first genus that states one (the emitter omits a species'
      -- vector exactly when that genus's is the same)
      let dimGenus := k.specializes.findSome? fun g =>
        ks.find? fun x => x.name == g && !x.dimension.isEmpty
      let k := if !k.dimension.isEmpty then k else
        match dimGenus with
        | some g => { k with dimension := g.dimension }
        | none => k
      let (k, open_) := if !open_.contains k.name then (k, open_) else
        match genus with
        | some g => if open_.contains g.name then (k, open_)
                    else ({ k with scale := g.scale }, open_.erase k.name)
        | none => (k, open_)
      (acc ++ [k], open_)
  let mut ks := m.kinds
  let mut open_ := unscaled
  for _ in [:m.kinds.length + 1] do
    let (ks', open') := step ks open_
    if ks' == ks && open' == open_ then break
    ks := ks'; open_ := open'
  match open_ with
  | [] => return { m with kinds := ks }
  | n :: _ => throw s!"#kind {n}: missing 'scale', and no genus states one"

/-- Read the model package: the one top-level package outside the DSL library (or the one
named), and every keyworded usage it owns. -/
def readModel (d : Doc) (packageName : Option String := none) : ReadM PkcModel := do
  let pkgs := d.elements.toList.filter fun e => e.type == "Package" && !e.isLibrary && e.name != some "PKC"
    && (packageName.isNone || e.name == packageName)
  let some pkg := pkgs.head? | throw "no model package found in the element list"
  let mut m : PkcModel := { packageName := pkg.name.getD pkg.id }
  let mut unscaled : List String := []
  for e in d.kids pkg.id do
    match d.keyword? e with
    | some "principle" => m := { m with principles := m.principles ++ [← readPrinciple d e] }
    | some "kind" =>
      let r ← readKind d e
      m := { m with kinds := m.kinds ++ [r.kind] }
      unless r.scaleWritten do unscaled := unscaled ++ [r.kind.name]
    | some "dedicated" => m := { m with dedicated := m.dedicated ++ [← readDedicated d e] }
    | some "unit" => m := { m with units := m.units ++ [← readUnit d e] }
    | some "module" => m := { m with modules := m.modules ++ [← readModule d e] }
    | some "relation" => m := { m with relations := m.relations ++ [← readRelation d e] }
    | some "req" => m := { m with requirements := m.requirements ++ [← readRequirement d e] }
    | some "tape" => m := { m with tapes := m.tapes ++ [← readTape d e] }
    | some "match" => m := { m with tapeMatches := m.tapeMatches ++ [← readMatch d e] }
    | some kw =>
      match edgeKindOf kw with
      | some k => m := { m with edges := m.edges ++ [← readEdge d e k] }
      | none => warn s!"unknown keyword '#{kw}' on {e.name.getD e.id}"
    | none =>
      unless e.isStructural do
        warn s!"unkeyworded element {e.name.getD e.id} ({e.type}) ignored"
  match inheritFromGenus m unscaled with
  | .ok m' => return m'
  | .error e => throw e

/-- Read a `PkcModel` from the API element list's JSON text; the warnings are the elements
the reader could not place. -/
def read (text : String) (packageName : Option String := none) :
    Except String (PkcModel × Array String) := do
  let j ← Json.parse text
  let d ← Doc.ofJson j
  let (r, warnings) := (readModel d packageName).run.run #[]
  match r with
  | .ok m => return (m, warnings)
  | .error e => throw e

end PropertyKindCalculus.Interchange.ApiJson

end Blanket
