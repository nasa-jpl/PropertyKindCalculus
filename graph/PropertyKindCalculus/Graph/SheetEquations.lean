/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette

# SheetEquations — a boundary's value equations, from the checked assembly

The equations a module sheet shows are not authored: they are the assembled provenance
graph — the same checked object the dissection figure draws — rendered as TeX, one
block per walked member, one line per occurrence. The granularity is therefore the
author's own: a line's left-hand side is a named `let` or a result, its right-hand
side applies the occurrence's operation to named nodes, and a member the walk entered
at the signature renders on its caller's block as one application. Nothing here can
state an operation the walk did not read out of the member's body.

The occurrence's `op` field is what makes the rendering *value*-honest where the edge
family alone is not: `additive` covers sum and difference alike (the kind algebra
cannot tell them apart, deliberately), so a sum renders `+` and a difference `-` only
because the walk recorded the scalar head; a `transcendental` renders the discharging
declaration's name as its operator, linked, rather than guessing a function. An
occurrence whose `op` is `.anonymous` renders its family's name — stated ignorance,
never an invented sign.

Lines are emitted in dependency order (a node is defined before it is used), which the
walk's occurrence order does not guarantee.
-/

module

public import PropertyKindCalculus.Graph.Footprint
public import PropertyKindCalculus.KindLedger

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.SheetEquations

open Lean Meta
open PropertyKindCalculus.Provenance (Contract NodeId KindRef NodeRef EdgeFamily
  Occurrence lastComponent)
open PropertyKindCalculus.KindIncidence (Assembly AssemblyLevel contractValueOf
  assembleContract)

/-- One rendered equation: TeX for both sides, and the discharging operation as a link
target (`.anonymous` where the line has none — a wire). -/
structure EquationLine where
  /-- The defined node, as TeX. -/
  lhs : String
  /-- The operation applied to named nodes, as TeX. -/
  rhs : String
  /-- The discharging operation, for the rendering document to link. -/
  op : Lean.Name := .anonymous
deriving Repr, Inhabited, BEq

/-- One walked member's equations: the computing declaration (the block's link), the
level's display name (instance-qualified where the member has several call sites), and
the lines in dependency order. -/
structure EquationBlock where
  /-- The computing declaration. -/
  member : Lean.Name
  /-- The level's display name. -/
  level : String
  /-- The equations, in dependency order. -/
  lines : List EquationLine
deriving Repr, Inhabited, BEq

/-- Escape a name for TeX: underscores only — node names carry no other TeX-active
characters (they are Lean identifiers and field paths). -/
def escapeTex (s : String) : String :=
  String.intercalate "\\_" (s.splitOn "_")

/-- A node as TeX, member-locally: a synthesized node as `t_{k}` (its projection path
kept, so `_1.fst` and `_1.snd` stay distinct), a constant address by its last component
in upright type, every named node in italic type with its field path. -/
def texOfNode (n : NodeId) : String :=
  let path := n.path.foldl (fun acc seg => acc ++ "." ++ seg) ""
  match n.root with
  | .fresh k =>
    if path.isEmpty then s!"t_\{{k}}" else s!"t_\{{k}}\\mathrm\{{escapeTex path}}"
  | .const c => s!"\\mathrm\{{escapeTex (lastComponent c)}{escapeTex path}}"
  | _ => s!"\\mathit\{{escapeTex (PropertyKindCalculus.KindLedger.stripNode n)}}"

/-- An operator application `\operatorname{name}(a, b, …)`, eliding the operand list
past six — the interface tables carry the full port detail, and a twenty-operand
application is a tally, not an equation. -/
def texApp (name : String) (args : List String) : String :=
  let inner := if args.length ≤ 6 then String.intercalate ", " args else "\\ldots"
  s!"\\operatorname\{{escapeTex name}}({inner})"

/-- One occurrence's right-hand side as TeX. Operands are nodes, so every argument is
atomic and nothing needs parenthesizing. An `.anonymous` op renders the family's own
name as the operator — stated ignorance, never an invented sign. -/
def texOfOccurrence (o : Occurrence NodeId KindRef) : String :=
  let a := (o.operands.map (texOfNode ·.1)).toArray
  let arg (i : Nat) : String := a.getD i "\\_"
  let named (fallback : String) (args : List String) : String :=
    if o.op.isAnonymous then texApp fallback args
    else texApp (lastComponent o.op) args
  match o.family with
  | .product => s!"{arg 0} \\cdot {arg 1}"
  | .quotient => s!"\\frac\{{arg 0}}\{{arg 1}}"
  | .reciprocal => s!"\\frac\{1}\{{arg 0}}"
  | .power p => s!"{arg 0}^\{{EdgeFamily.renderExp p}}"
  | .additive =>
    if o.op == ``HAdd.hAdd then s!"{arg 0} + {arg 1}"
    else if o.op == ``HSub.hSub then s!"{arg 0} - {arg 1}"
    else named "additive" [arg 0, arg 1]
  | .transcendental => named "transcendental" [arg 0]
  | .reference => named "reexpress" [arg 0]
  | .tableMul => s!"{arg 0} \\cdot {arg 1}"
  | .tableDiv => s!"\\frac\{{arg 0}}\{{arg 1}}"
  | .copy => arg 0
  | .step m _ _ =>
    -- Operands sharing a root are that root's fields, spread by the call-site
    -- dissection — a configuration record, a produced pair — and render as the root,
    -- once: the call consumed the thing, and the interface tables name its fields.
    -- A solitary projected operand keeps its path.
    let rootOf (n : NodeId) : NodeId := { n with path := [] }
    let roots := o.operands.map fun (n, _) => rootOf n
    let disp := o.operands.map fun (n, _) =>
      if (roots.filter (· == rootOf n)).length ≥ 2 then texOfNode (rootOf n)
      else texOfNode n
    texApp (lastComponent m) disp.eraseDups
  | .select _ => named "select" a.toList

/-- The line's link target: the recorded operation, or the callee of a `step`. -/
def opOfOccurrence (o : Occurrence NodeId KindRef) : Lean.Name :=
  if !o.op.isAnonymous then o.op
  else match o.family with
    | .step m _ _ => m
    | _ => .anonymous

/-- Occurrences in dependency order: a line lands only after every line defining one of
its operands. The walk's emission order does not guarantee this (a synthesized operand's
defining occurrence can follow its use), and an equation list that uses a name before
defining it reads as a mistake. Kahn over the defines-relation; any residue (a cycle
cannot occur in a well-formed graph, but this function does not assume one) is appended
in original order. -/
def dependencyOrder (occs : List (Occurrence NodeId KindRef)) :
    List (Occurrence NodeId KindRef) := Id.run do
  let mut pending := occs
  let mut out : List (Occurrence NodeId KindRef) := []
  let mut defined : List NodeId := []
  let producers := occs.map (·.result)
  let ready (o : Occurrence NodeId KindRef) (defined : List NodeId) : Bool :=
    o.operands.all fun (n, _) => !producers.contains n || defined.contains n
  let mut progress := true
  while progress do
    progress := false
    let mut still : List (Occurrence NodeId KindRef) := []
    for o in pending do
      if ready o defined then
        out := out ++ [o]
        defined := defined ++ [o.result]
        progress := true
      else
        still := still ++ [o]
    pending := still
  return out ++ pending

/-- **The equation blocks of an assembly**: one block per walked level, in level order —
an interface-mode level contributes no block of its own because its application renders
on its caller's. Pure over the assembled value, like every sheet emitter.

Three readings keep a block an equation list rather than a trace: a bare copy of a
synthesized node nothing in the block defines is dropped (it says only "the result is
an unnamed interior expression", which the caller's application line already says
better); a step application's operands that share a root — a record's fields, spread
by the call-site dissection — render as the root, once; and consecutive lines with one
right-hand side — a multi-output application, one occurrence per produced component —
merge into a single line with the tupled left-hand side. -/
def equationBlocks (a : Assembly) : Array EquationBlock := Id.run do
  let mut blocks : Array EquationBlock := #[]
  for l in a.levels do
    unless l.walked do continue
    let occs := dependencyOrder l.graph.occurrences
    let definedHere := occs.map (·.result)
    let occs := occs.filter fun o =>
      match o.family, o.operands with
      | .copy, [(n, _)] =>
        (match n.root with
         | .fresh _ => definedHere.contains n
         | _ => true)
      | _, _ => true
    let mut groups : List (List String × String × Lean.Name) := []
    for o in occs do
      let lhs := texOfNode o.result
      let rhs := texOfOccurrence o
      let op := opOfOccurrence o
      -- an elided operand list can hide two different calls behind one rendering,
      -- so an rhs carrying an ellipsis never merges
      let mergeable := (rhs.splitOn "\\ldots").length == 1
      match groups.getLast? with
      | some (ls, r, p) =>
        if mergeable && r == rhs && p == op then
          groups := groups.dropLast ++ [(ls ++ [lhs], r, p)]
        else groups := groups ++ [([lhs], rhs, op)]
      | none => groups := [([lhs], rhs, op)]
    let lines := groups.map fun (ls, r, p) =>
      { lhs := match ls with
          | [only] => only
          | _ => "\\left(" ++ String.intercalate ", " ls ++ "\\right)"
        rhs := r, op := p : EquationLine }
    unless lines.isEmpty do
      blocks := blocks.push { member := l.decl, level := l.name, lines }
  return blocks

/-- The equation blocks of one **declared** boundary: the contract's assembly, checked
well-formed exactly as the figure generator checks it, then `equationBlocks`. -/
def sheetEquations (decl : Name) : MetaM (Array EquationBlock) := do
  let c ← contractValueOf decl
  let a ← assembleContract c
  unless a.graph.wellFormed do
    throwError "the assembly of '{c.name}' is not well-formed — render it with \
      #kind_assembly and fix"
  return equationBlocks a

end PropertyKindCalculus.SheetEquations

end -- pkc-blanket-expose
end -- pkc-blanket
