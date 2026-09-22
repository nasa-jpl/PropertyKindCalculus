/-
# KindLedger — the unkinded inventory of a declared scope, as reviewable data

`KindIncidence`'s unkinded reading answers, per declaration, "what crosses this interface
without a kind". Read one graph at a time it is a remark; read across a declared boundary
and its members it is a **worklist**, and a worklist is only useful if it is one list, in
one order, deduplicated by cause. That is this module: the same reading, gathered over an
assembly, rendered for a `#guard_msgs` pin and emitted as JSON for whatever reviews it.

Two properties make it a ledger rather than a report.

**It dedupes by member, not by instance.** A call site is a level (`KindIncidence`, "the
assembly"), so a helper called three times is three levels — and its one naked binder would
otherwise be counted three times. Dissecting a call would then *raise* the debt while
strictly improving the reading, which would teach exactly the wrong lesson. The row is
keyed by the member and the local node, so three instances of one silence are one row.

**Its authority is the pin, not the file.** `#kind_unkinded c` prints the ledger with its
count, so a `#guard_msgs` pin fails in *both* directions: a new naked position fails the
build, and so does a fixed one until the ledger is edited to say so. `#kind_unkinded_clean c`
is the separate gate for a scope that has reached zero — a pin that can express a violation
cannot also be the check that no violation exists. The JSON is the triage artifact: it is
written by whatever writes the figure, from the same value, so it cannot disagree with the
figure; but a file on disk is only as current as its last regeneration, so nothing rests on
it that the pins do not already carry.

## The three verdicts a position can get

A signature position is *ported* (a carrier or a carrier field path — an interface node at
its kind), *unkinded* (no kind information at all — a ledger row), or **kind-bearing and
unported**: a function over quantities, a list of kinded records, a sum over them. The third
is not debt. `List (Sample R)` is a plural of a kinded thing and there is nothing there to
fix; counting it would make the ledger un-driveable to zero. Only the second is a row.

## The denominator

A ledger driven to zero is a document with no rows in it, and a document with no rows says
nothing about how much was read to get there. So the JSON carries the assembly's interface
tally beside the rows: one entry per *level*, its ports by role and the size of its interior.
Per level, not per member — the dedupe rule above is about a debt, which belongs to the
declaration that states it, whereas an interface belongs to the call site that has one, and
three instances of a helper really do present three interfaces. The tallies are
`KindIncidence.tallyOf`, the same values the overview figure draws, so the two cannot
disagree about the size of what they show.
-/

module

public import PropertyKindCalculus.KindIncidence
public meta import PropertyKindCalculus.KindIncidence

-- Same-module helpers serve both the command elaborators below and runtime callers, so the
-- phase check is relaxed for this file (the module system's mixed-use escape; imports are
-- still checked and take `public meta import`).
set_option compiler.relaxedMetaCheck true

public section -- pkc-blanket

namespace PropertyKindCalculus.KindLedger

open Lean
open PropertyKindCalculus.Provenance (PortDir)
open PropertyKindCalculus.KindIncidence
  (Assembly AssemblyLevel UnkindedSlot LevelTally tallyOf assembleContract contractValueOf)

/-- What a ledger row records about one interface position or one flow. -/
inductive Silence where
  /-- A signature position carrying no kind information: the direction and the type the
  signature states instead of a kind. -/
  | position (dir : PortDir) (type : String)
  /-- An unkinded argument reaching a kinded node — minting it, or steering it outside
  the kinded algebra. The target node is local to the member. -/
  | flow (target : String)
deriving Repr, Inhabited, BEq

/-- One row: the scope it was read in, the member it belongs to, the node inside that
member, and what is missing there. The member is the *declaration*, not the call site, so
a helper called three times contributes one row per silence rather than three. -/
structure Row where
  /-- The declared boundary's name — the scope the ledger was taken over. -/
  scope : String
  /-- The member's step name, with any instance suffix removed. -/
  member : String
  /-- The node inside that member, with the level namespace stripped. -/
  node : String
  /-- What is missing. -/
  silence : Silence
deriving Repr, Inhabited, BEq

/-- The member behind a level: the declaration's last component — the ledger counts the
member, however many call-site instances it has. -/
def memberOf (l : AssemblyLevel) : String :=
  PropertyKindCalculus.Provenance.lastComponent l.decl

/-- Strip a level's node namespace from a rendered name: `rOfSmQ#2/polarization` inside
level `rOfSmQ#2` is the member's `polarization` (the red inventory keeps rendered
names). -/
def stripLevel (l : AssemblyLevel) (n : String) : String :=
  if n.startsWith (l.name ++ "/") then (n.drop (l.name.length + 1)).toString else n

/-- A node identifier without its level — the member-local rendering the ledger keys
rows by. -/
def stripNode (n : PropertyKindCalculus.Provenance.NodeId) : String :=
  PropertyKindCalculus.Provenance.NodeId.render { n with level := none }

/-- **The ledger of a scope** — every unkinded position and every unkinded flow its
members state, deduplicated by `(member, node, silence)` and kept in level order so the
list reads down the pipeline. -/
def ledgerOf (scope : String) (a : Assembly) : Array Row := Id.run do
  let mut out : Array Row := #[]
  for l in a.levels do
    let m := memberOf l
    for u in l.unkinded do
      let r : Row := ⟨scope, m, stripLevel l u.node, .position u.dir u.type⟩
      unless out.contains r do out := out.push r
    for (s, t) in l.leaks do
      let r : Row := ⟨scope, m, stripLevel l s, .flow (stripNode t)⟩
      unless out.contains r do out := out.push r
  return out

/-- Is this row a *position* (a naked signature slot) rather than a flow? -/
def Row.isPosition (r : Row) : Bool :=
  match r.silence with
  | .position _ _ => true
  | .flow _ => false

/-- One ledger line, in the reading's own grammar. -/
def renderRow (r : Row) : String :=
  match r.silence with
  | .position d t => s!"unkinded {d.label} {r.member}/{r.node} : {t}"
  | .flow t => s!"unkinded flow: {r.member}/{r.node} ⇒ {r.member}/{t}"

/-- The count line — a count is a predicate, so it is stated with its number and with what
the number is a count *of*. -/
def renderCount (rows : Array Row) : String :=
  let ps := (rows.filter (·.isPosition)).size
  let fs := rows.size - ps
  if rows.isEmpty then "unkinded: none — every position carries a kind"
  else s!"unkinded: {ps} position(s), {fs} flow(s)"

/-- The full ledger rendering: the count, then one line per row. -/
def renderLines (rows : Array Row) : List String :=
  renderCount rows :: rows.toList.map renderRow

/-- JSON-escape a string for the emitter below (no dependency on a JSON library: the
values here are declaration names, node names and pretty-printed types). -/
def esc (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ (match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\t' => "\\t"
      | c => if c.toNat < 0x20 then "" else c.toString)

/-- One row as a JSON object. -/
def rowJson (r : Row) : String :=
  match r.silence with
  | .position d t =>
    "{\"member\": \"" ++ esc r.member ++ "\", \"node\": \"" ++ esc r.node ++
      "\", \"silence\": \"position\", \"dir\": \"" ++ esc d.label ++
      "\", \"type\": \"" ++ esc t ++ "\"}"
  | .flow t =>
    "{\"member\": \"" ++ esc r.member ++ "\", \"node\": \"" ++ esc r.node ++
      "\", \"silence\": \"flow\", \"target\": \"" ++ esc t ++ "\"}"

/-- One level's interface, as the JSON reports it (module section, "The denominator"):
the level, the member it instantiates, whether the walk read its body, and its tally. -/
structure MemberRow where
  /-- The level's name — a call site, so `rOfSmQ#2` when the member has more than one. -/
  level : String
  /-- The declaration behind it. -/
  member : String
  /-- `walked` when the walk read the body, `interface` when it entered at the signature. -/
  mode : String
  /-- Its ports by role, and the size of the interior the walk introduced. -/
  tally : LevelTally
deriving Repr, Inhabited

/-- The interface tallies of an assembly, one per level, in level order. -/
def membersOf (a : Assembly) : Array MemberRow :=
  a.levels.map fun l =>
    ⟨l.name, memberOf l, if l.walked then "walked" else "interface", tallyOf l⟩

/-- One member's interface as a JSON object. -/
def memberJson (m : MemberRow) : String :=
  "{\"level\": \"" ++ esc m.level ++ "\", \"member\": \"" ++ esc m.member ++
    "\", \"mode\": \"" ++ esc m.mode ++
    "\", \"in\": " ++ toString m.tally.ins ++
    ", \"config\": " ++ toString m.tally.cfgs ++
    ", \"out\": " ++ toString m.tally.outs ++
    ", \"interior\": " ++ toString m.tally.interior ++
    ", \"unkinded\": " ++ toString m.tally.unkinded ++ "}"

/-- **The ledger as JSON** — the triage artifact. The scope, the two counts, the interface
each level presents, and the rows. Emitted from the same assembled value the figure and the
pins are read off, so a reviewer comparing the three is comparing three renderings of one
object. The `members` array is the denominator the counts are a numerator of: a scope driven
to zero still says how much interface was read to get there. -/
def toJson (scope : String) (ms : Array MemberRow) (rows : Array Row) : String :=
  let ps := (rows.filter (·.isPosition)).size
  let body := String.intercalate ",\n    " (rows.toList.map rowJson)
  let mbody := String.intercalate ",\n    " (ms.toList.map memberJson)
  "{\n  \"scope\": \"" ++ esc scope ++ "\",\n" ++
    "  \"positions\": " ++ toString ps ++ ",\n" ++
    "  \"flows\": " ++ toString (rows.size - ps) ++ ",\n" ++
    "  \"members\": [" ++ (if ms.isEmpty then "]" else "\n    " ++ mbody ++ "\n  ]") ++
    ",\n" ++
    "  \"rows\": [" ++ (if rows.isEmpty then "]" else "\n    " ++ body ++ "\n  ]") ++
    "\n}\n"

open Elab Command in
/-- `#kind_unkinded c` prints the unkinded ledger of the scope the contract `c` declares:
the count, then one line per naked position and per unkinded flow, deduplicated by member.
Pin it with `#guard_msgs` — the pin then fails when a silence appears *and* when one is
fixed, which is what keeps the ledger honest about which direction it moved. -/
elab "#kind_unkinded " c:ident : command => liftTermElabM do
  let ctr ← contractValueOf (← realizeGlobalConstNoOverload c)
  let a ← assembleContract ctr
  logInfo m!"unkinded ledger of '{ctr.name}':\n\
    {String.intercalate "\n" (renderLines (ledgerOf ctr.name a))}"

open Elab Command in
/-- `#kind_unkinded_clean c` is the gate: it errors unless the scope's ledger is empty.
Separate from the pin above for the reason every violation-capable pin needs a separate
gate — a `#guard_msgs` docstring that can *express* a violation cannot also be the check
that none exists, because pinning the violation is how it stops being noticed. -/
elab "#kind_unkinded_clean " c:ident : command => liftTermElabM do
  let ctr ← contractValueOf (← realizeGlobalConstNoOverload c)
  let a ← assembleContract ctr
  let rows := ledgerOf ctr.name a
  unless rows.isEmpty do
    throwError "'{ctr.name}' has unkinded positions:\n{String.intercalate "\n"
      (renderLines rows)}"
  logInfo m!"unkinded-clean: every position of '{ctr.name}' carries a kind"

end PropertyKindCalculus.KindLedger

end -- pkc-blanket
