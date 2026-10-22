/-
# `EmitSysml` — print a `PkcModel` as a SysML v2 model in the PKC DSL

A pure printer from the neutral record to the textual notation of `sysml/PKC.sysml`. The
model becomes one `package` importing the DSL's three packages; every element becomes a
keyworded usage (`#kind`, `#product`, `#module`, `#tape`, …), its values bound by
redefinition. Two conventions keep the output valid and round-trippable:

* a kind's values are bound with `default =` — `#kind width :> length` *subsets* `length`
  and would otherwise inherit `length`'s fixed values;
* list-valued attributes (operands, occurrences, vertices, …) are written as subsetting
  usages, one element each, in order — the notation has no constructor expression for a
  data type, so a nested record is a usage, not a value.

Citations travel as `@Source { decl = … }` / `@Checked { decl = … }` annotations.
-/

module

public import PropertyKindCalculus.Interchange.Model

@[expose] public section Blanket

namespace PropertyKindCalculus.Interchange.EmitSysml

open PropertyKindCalculus.Interchange

/-- Is a string a plain SysML identifier (letter or underscore, then letters, digits,
underscores)? Anything else — and the notation's reserved words — is written quoted. -/
def isPlainIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun d => d.isAlphanum || d == '_')

/-- Reserved words of the SysML v2 notation: every word OpenSysML's `.sysml` parser refuses as a
bare name (`reserved-keyword-name`). KerML-only words (`type`, `feature`, `class`, …) are names
in a `.sysml` file and stay bare. -/
def reservedWords : List String :=
  ["about", "abstract", "accept", "action", "actor", "after", "alias", "all", "allocate", "allocation",
   "analysis", "and", "as", "assert", "assign", "assume", "at", "attribute", "bind", "binding",
   "by", "calc", "case", "comment", "concern", "connect", "connection", "constant", "constraint",
   "crosses", "decide", "def", "default", "defined", "dependency", "derived", "do", "doc", "else",
   "end", "entry", "enum", "event", "exhibit", "exit", "expose", "false", "filter", "first",
   "flow", "for", "fork", "frame", "from", "hastype", "if", "implies", "import", "in", "include",
   "individual", "inout", "interface", "istype", "item", "join", "language", "library", "locale",
   "loop", "merge", "message", "meta", "metadata", "new", "nonunique", "not", "null", "objective",
   "occurrence", "of", "or", "ordered", "out", "package", "parallel", "part", "perform", "port",
   "private", "protected", "public", "redefines", "ref", "references", "render", "rendering",
   "rep", "require", "requirement", "return", "satisfy", "send", "snapshot", "specializes",
   "stakeholder", "standard", "state", "subject", "subsets", "succession", "terminate", "then",
   "timeslice", "to", "transition", "true", "until", "use", "variant", "variation", "verification",
   "verify", "via", "view", "viewpoint", "when", "while", "xor"]

/-- Write a name as the notation admits it: bare when a plain non-reserved identifier,
otherwise quoted with `'…'` (escaping the quote and backslash). -/
def ident (s : String) : String :=
  if isPlainIdent s && !reservedWords.contains s then s
  else "'" ++ (s.foldl (fun acc c =>
    if c == '\'' then acc ++ "\\'" else if c == '\\' then acc ++ "\\\\" else acc.push c) "") ++ "'"

/-- A string literal of the notation. -/
def str (s : String) : String :=
  "\"" ++ (s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\"" else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n" else acc.push c) "") ++ "\""

/-- An ordered sequence expression of natural numbers: `()`, `3`, or `(0, 1)`. -/
def natSeq : List Nat → String
  | [] => "()"
  | [n] => toString n
  | ns => "(" ++ String.intercalate ", " (ns.map toString) ++ ")"

/-- An ordered sequence expression of strings. -/
def strSeq : List String → String
  | [] => "()"
  | [s] => str s
  | ss => "(" ++ String.intercalate ", " (ss.map str) ++ ")"

/-- The enumeration literal of each scale type. -/
def scaleLit : Scale → String
  | .nominal => "ScaleType::nominal" | .ordinal => "ScaleType::ordinal"
  | .interval => "ScaleType::interval" | .ratio => "ScaleType::ratio"

def portDirLit : PortDir → String
  | .input => "PortDir::input" | .config => "PortDir::config" | .param => "PortDir::param"
  | .output => "PortDir::output" | .conditional => "PortDir::conditional"

def tierLit : IntroTier → String
  | .derived => "IntroTier::'derived'" | .gated => "IntroTier::gated" | .attested => "IntroTier::attested"

def familyLit : EdgeFamily → String
  | .product => "EdgeFamily::product" | .quotient => "EdgeFamily::quotient"
  | .reciprocal => "EdgeFamily::reciprocal" | .transcendental => "EdgeFamily::transcendental"
  | .power => "EdgeFamily::power" | .reference => "EdgeFamily::reference"
  | .additive => "EdgeFamily::additive" | .tableMul => "EdgeFamily::tableMul"
  | .tableDiv => "EdgeFamily::tableDiv" | .copy => "EdgeFamily::copy"
  | .step => "EdgeFamily::step" | .select => "EdgeFamily::select"

def roleLit : BoundaryRole → String
  | .model => "BoundaryRole::model" | .specification => "BoundaryRole::specification"

def aggregationLit : AggregationKind → String
  | .extensive => "AggregationKind::extensive" | .quasiExtensive => "AggregationKind::quasiExtensive"
  | .conditionallyExtensive => "AggregationKind::conditionallyExtensive"
  | .intensive => "AggregationKind::intensive" | .wholeProper => "AggregationKind::wholeProper"
  | .countKeyed => "AggregationKind::countKeyed"
  | .extensiveAbout => "AggregationKind::extensiveAbout"
  | .interfaceLicensed => "AggregationKind::interfaceLicensed"

def relationLit : RelationKind → String
  | .inverts => "RelationKind::inverts" | .refines => "RelationKind::refines"
  | .equals => "RelationKind::equals" | .boundedBy => "RelationKind::boundedBy"

def transferLit : TransferKind → String
  | .exact => "TransferKind::exact" | .nonneg => "TransferKind::nonneg"
  | .restated => "TransferKind::restated"

def requirementLit : RequirementKind → String
  | .provable => "RequirementKind::provable" | .empirical => "RequirementKind::empirical"

/-- The keyword, connection definition and end names of each kind-algebra family. -/
def edgeSyntax : EdgeKind → String × String × List String
  | .product => ("product", "KindProduct", ["left", "right", "result"])
  | .quotient => ("quotient", "KindQuotient", ["numerator", "denominator", "result"])
  | .reciprocal => ("reciprocal", "KindReciprocal", ["base", "result"])
  | .power => ("power", "KindPower", ["base", "result"])
  | .transcendental => ("transcendental", "KindTranscendental", ["argument", "result"])
  | .reference => ("reference", "KindReference", ["base", "result"])
  | .difference => ("difference", "KindDifference", ["left", "right"])

/-- The line-oriented printer: an indentation level and the accumulated lines. -/
structure Printer where
  indent : Nat := 0
  lines : Array String := #[]

namespace Printer

def line (p : Printer) (s : String) : Printer :=
  { p with lines := p.lines.push (String.ofList (List.replicate (4 * p.indent) ' ') ++ s) }

def blank (p : Printer) : Printer := { p with lines := p.lines.push "" }

/-- Open a block, print its body, close it — `head {` … `}`. -/
def block (p : Printer) (head : String) (body : Printer → Printer) : Printer :=
  let p := p.line (head ++ " {")
  let p := body { p with indent := p.indent + 1 }
  { p with indent := p.indent - 1 }.line "}"

def render (p : Printer) : String := String.intercalate "\n" p.lines.toList ++ "\n"

end Printer

/-- The citation annotations of an element. -/
def citations (p : Printer) (source : Option String) (checked : List Checked) : Printer :=
  let p := match source with
    | some d => p.line s!"@Source \{ decl = {str d}; }"
    | none => p
  checked.foldl (init := p) fun p c =>
    match c.statement with
    | some st => p.line s!"@Checked \{ decl = {str c.decl}; statement = {str st}; }"
    | none => p.line s!"@Checked \{ decl = {str c.decl}; }"

/-- An optional string-valued binding. -/
def optBind (p : Printer) (field : String) (dflt : Bool) : Option String → Printer
  | some v => p.line s!":>> {field}{if dflt then " default" else ""} = {str v};"
  | none => p

def listBind (p : Printer) (field : String) (dflt : Bool) : List String → Printer
  | [] => p
  | vs => p.line s!":>> {field}{if dflt then " default" else ""} = {strSeq vs};"

/-- `#principle name { :>> id = "…"; }` -/
def principle (p : Printer) (pr : Principle) : Printer :=
  p.block s!"#principle {ident pr.name}" fun p =>
    (p.line s!":>> id = {str pr.id};") |> (citations · pr.source [])

/-- `#kind name :> genus { … }` — every value a `default`, so a species may rebind it. A
species whose dimension vector is its genus's inherits it through the subsetting and
writes none (a restated one would be a second member of the same name). -/
def kind (p : Printer) (m : PkcModel) (k : Kind) : Printer :=
  let head := s!"#kind {ident k.name}" ++
    (if k.specializes.isEmpty then ""
     else " :> " ++ String.intercalate ", " (k.specializes.map ident))
  -- the reader inherits from the first genus that states a vector; omit only when that
  -- genus's vector is this kind's
  let inherited := match k.specializes.findSome? fun g =>
      (m.kind? g).bind fun g => if g.dimension.isEmpty then none else some g.dimension with
    | some d => d == k.dimension
    | none => false
  p.block head fun p =>
    let p := p.line s!":>> id default = {str k.id}; :>> scale default = {scaleLit k.scale};"
    let p := match k.principle with
      | some pr => p.line s!":>> principle default = {ident pr};"
      | none => p
    let p := (if inherited then [] else k.dimension).foldl (init := p) fun p d =>
      p.line s!"attribute dim_{ident d.base} :> dimension \{ :>> base default = {str d.base}; :>> num default = {d.num}; :>> den default = {d.den}; }"
    let p := optBind p "standardRef" true k.standardRef
    let p := optBind p "catalogueItem" true k.catalogueItem
    let p := optBind p "symbol" true k.symbol
    let p := optBind p "coherentUnit" true k.coherentUnit
    citations p k.source k.checked

/-- `#product connection name : KindProduct connect (left ::> a, right ::> b, result ::> c) { … }` -/
def edge (p : Printer) (e : Edge) : Printer :=
  let (kw, defn, ends) := edgeSyntax e.kind
  let kinds := e.operands ++ (e.result.map ([·])).getD []
  let binds := String.intercalate ", " ((ends.zip kinds).map fun (en, k) => s!"{en} ::> {ident k}")
  p.block s!"#{kw} connection {ident e.name} : {defn} connect ({binds})" fun p =>
    let p := if e.table then p.line ":>> table = true;" else p
    let p := match e.kind, e.powerNum, e.powerDen with
      | .power, some n, d => p.line s!":>> num = {n}; :>> den = {d.getD 1};"
      | _, _, _ => p
    citations p e.source e.checked

def dedicated (p : Printer) (d : Dedicated) : Printer :=
  p.block s!"#dedicated {ident d.name}" fun p =>
    let p := p.line s!":>> sort = {str d.sort}; :>> component = {str d.component}; :>> kind = {ident d.kind};"
    citations p d.source []

def unit (p : Printer) (u : MetrologicalUnit) : Printer :=
  p.block s!"#unit {ident u.name}" fun p =>
    let p := p.line s!":>> kind = {ident u.kind}; :>> symbol = {str u.symbol};"
    citations p u.source []

def occurrence (p : Printer) (i : Nat) (o : Occurrence) : Printer :=
  p.block s!"attribute occ{i} :> occurrences" fun p =>
    let p := p.line s!":>> family = {familyLit o.family};"
    let p := o.operands.foldl (init := (p, 0)) (fun (p, j) op =>
      (p.line s!"attribute op{j} :> operands \{ :>> node = {str op.node}; :>> kind = {ident op.kind}; }", j + 1)) |>.1
    let p := p.line s!":>> result = {str o.result}; :>> resultKind = {ident o.resultKind};"
    let p := p.line s!":>> site = {str o.site};"
    let p := optBind p "op" false o.op
    let p := optBind p "member" false o.member
    let p := match o.inst with | some n => p.line s!":>> instance = {n};" | none => p
    let p := match o.arity with | some n => p.line s!":>> arity = {n};" | none => p
    match o.powerNum with
    | some n => p.line s!":>> powerNum = {n}; :>> powerDen = {o.powerDen.getD 1};"
    | none => p

/-- `#module name : Module { … }` -/
def module (p : Printer) (m : MetrologyModule) : Printer :=
  p.block s!"#module {ident m.name} : Module" fun p =>
    let p := p.line s!":>> name = {str m.title};"
    let p := listBind p "members" false m.members
    let p := m.ports.foldl (init := p) fun p pt =>
      p.line s!"port {ident pt.name} : KindPort \{ :>> node = {str pt.node}; :>> kind = {ident pt.kind}; :>> dir = {portDirLit pt.dir}; }"
    let p := listBind p "exits" false m.exits
    let p := listBind p "deciders" false (m.deciders.map fun (n, d) => s!"{n} := {d}")
    let p := m.aggregations.foldl (init := (p, 0)) (fun (p, j) a =>
      let w := match a.witness with | some w => s!" :>> witness = {str w};" | none => ""
      (p.line s!"attribute agg{j} :> aggregations \{ :>> node = {str a.node}; :>> class = {aggregationLit a.cls};{w} }", j + 1)) |>.1
    let p := listBind p "suppliers" false (m.suppliers.map fun (n, d) => s!"{n} := {d}")
    let p := if m.role == .model then p else p.line s!":>> role = {roleLit m.role};"
    let p := if m.hypergraph then p.line ":>> hypergraph = true;" else p
    let p := m.intros.foldl (init := (p, 0)) (fun (p, j) i =>
      let r := match i.reason with | some r => s!" :>> reason = {str r};" | none => ""
      (p.line s!"attribute intro{j} :> intros \{ :>> node = {str i.node}; :>> kind = {ident i.kind}; :>> tier = {tierLit i.tier};{r} }", j + 1)) |>.1
    let p := m.occurrences.foldl (init := (p, 0)) (fun (p, j) o => (occurrence p j o, j + 1)) |>.1
    citations p m.source m.checked

def relation (p : Printer) (r : Relation) : Printer :=
  p.block s!"#relation connection {ident r.name} : Relation connect (left ::> {ident r.left}, right ::> {ident r.right})" fun p =>
    let p := p.line s!":>> kind = {relationLit r.kind}; :>> witness = {str r.witness};"
    let p := optBind p "claim" false r.claim
    let p := optBind p "tolerance" false r.tolerance
    let p := listBind p "hypotheses" false r.hypotheses
    let p := r.licenses.foldl (init := (p, 0)) (fun (p, j) l =>
      (p.line s!"attribute license{j} :> licenses \{ :>> rung = {str l.rung}; :>> transfer = {transferLit l.transfer}; :>> witness = {str l.witness}; }", j + 1)) |>.1
    let p := optBind p "wellPosed" false r.wellPosed
    let p := optBind p "domain" false r.domain
    let p := optBind p "ambiguity" false r.ambiguity
    citations p r.source []

def requirement (p : Printer) (r : Requirement) : Printer :=
  p.block s!"#req requirement {ident r.name} : PkcRequirement" fun p =>
    let p := p.line s!":>> name = {str r.title}; :>> statement = {str r.statement};"
    let p := p.line s!":>> kind = {requirementLit r.kind}; :>> governs = {str r.governs};"
    let p := optBind p "'port'" false r.port
    let p := optBind p "scope" false r.scope.render
    let p := optBind p "witness" false r.witness
    let p := listBind p "spotChecks" false r.spotChecks
    let p := optBind p "absent" false r.absent
    let p := listBind p "referents" false r.referents
    citations p r.source []

def tape (p : Printer) (t : Tape) : Printer :=
  p.block s!"#tape {ident t.name} : TapeGraph" fun p =>
    let p := t.vertices.foldl (init := (p, 0)) (fun (p, j) v =>
      let nm := match v.name with | some n => s!" :>> name = {str n};" | none => ""
      let ps := if v.parents.isEmpty then "" else s!" :>> parents = {natSeq v.parents};"
      (p.line s!"attribute v{j} :> vertices \{{nm}{ps} }", j + 1)) |>.1
    citations p t.source t.checked

def tapeMatch (p : Printer) (m : TapeMatch) : Printer :=
  p.block s!"#match connection {ident m.name} : Match connect (module ::> {ident m.moduleName}, tape ::> {ident m.tape})" fun p =>
    let p := m.components.foldl (init := (p, 0)) (fun (p, j) c =>
      (p.line s!"attribute c{j} :> components \{ :>> node = {str c.node}; :>> vertices = {natSeq c.vertices}; }", j + 1)) |>.1
    let p := m.realized.foldl (init := (p, 0)) (fun (p, j) r =>
      let int := if r.interior.isEmpty then "" else s!" :>> interior = {natSeq r.interior};"
      (p.line s!"attribute r{j} :> realized \{ :>> occ = {r.occ};{int} }", j + 1)) |>.1
    let p := match m.carrier with
      | some c =>
        let pl := match c.platform with | some pl => s!" :>> platform = {str pl};" | none => ""
        p.line s!"attribute :>> carrier \{ :>> rung = {str c.rung};{pl} }"
      | none => p
    citations p m.source m.checked

/-- The whole model as one package in the PKC DSL. -/
def emit (m : PkcModel) : String :=
  let p : Printer := {}
  let p := p.block s!"package {ident m.packageName}" fun p =>
    let p := match m.doc with
      | some d => p.line s!"doc /* {d} */"
      | none => p
    let p := p.line "private import PKC::*;"
    let p := p.line "private import PKC::Kinds::*;"
    let p := p.line "private import PKC::Modules::*;"
    let p := p.line "private import PKC::Tape::*;"
    let p := m.principles.foldl (init := p) fun p x => principle p.blank x
    let p := m.kinds.foldl (init := p) fun p x => kind p.blank m x
    let p := m.edges.foldl (init := p) fun p x => edge p.blank x
    let p := m.dedicated.foldl (init := p) fun p x => dedicated p.blank x
    let p := m.units.foldl (init := p) fun p x => unit p.blank x
    let p := m.modules.foldl (init := p) fun p x => module p.blank x
    let p := m.relations.foldl (init := p) fun p x => relation p.blank x
    let p := m.requirements.foldl (init := p) fun p x => requirement p.blank x
    let p := m.tapes.foldl (init := p) fun p x => tape p.blank x
    m.tapeMatches.foldl (init := p) fun p x => tapeMatch p.blank x
  p.render

end PropertyKindCalculus.Interchange.EmitSysml

end Blanket
