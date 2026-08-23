/-
# `#kind_occurrences` / `#kind_ports` — the incidence and port harvests

Where `#kind_edges` enumerates a kind's authored *licenses*, this command reads the
**occurrences**: the consuming applications inside one definition — each site where a
witness argument is discharged against actual operand quantities — printed with their
operands (`alphaK · betaK → gammaK ⟨x, y⟩`), in body order, with multiplicity: two uses
of one witness are two occurrences. This is the provenance hypergraph's occurrence
relation read off elaborated values, incidence included — *which* values met at the
edge, the datum the edge enumeration alone does not carry.

    #kind_occurrences myStep

The collector itself (`KindEdges.collectOccurrences`) reads the edge off the consumer's
instantiated *binder type*, so a pinned occurrence is stable across the elaborator's
witness spellings — inline constructor, lifted or shared `._proof_N` reference,
`let`-bound witness. Operands render as a binder name or an application's head constant.
A hypothesis witness contributes no occurrence: the occurrence sits at the caller that
discharges the license.

The second command reads the **ports**: a step is a declaration, and its kind-typed
signature is its node list —

    #kind_ports myStep

prints the telescope's carrier-typed binders as *input* ports, the result type's
carrier-typed product components as *output* ports, and the `@[kindConst]` constants the
value reads as *configuration* ports, each with the kind the signature states
(`input x : alphaK`). Roles are `Provenance.PortDir`, so the harvest already speaks the
graph structure's port vocabulary. A port is an interface node, not a use: a constant
read twice is one configuration port, while the occurrence reading keeps both incidence
positions. A binder or component at a bare carrier type states no kind and is no port —
output positions count *components*, so a skipped component leaves its gap visible.

This module, not `KindEdges`, holds the user surface because operand positions and ports
are identified by the boundary audit's **carrier registry** (`kindCarrierNames`), and
importing the audit puts its meta-heavy bodies into `producerModules`' walk set — a cost
every `#kind_edges` consumer would pay. Per-declaration reading walks one signature and
one value, so it is cheap here; files that pin both readings keep them in separate
modules.
-/
import PropertyKindCalculus.KindEdges
import PropertyKindCalculus.IndividualQuantity
import PropertyKindCalculus.BoundaryAudit
import PropertyKindCalculus.Provenance

namespace PropertyKindCalculus.KindIncidence

open Lean
open PropertyKindCalculus.KindEdges (KindOccurrence collectOccurrences)

/-- The carrier heads an operand position is recognized by: the audit's registry
(`Quantity`, `CertifiedQuantity`, `NominalValue`, plus every downstream `@[kindCarrier]`
registration), and `IndividualQuantity` — not a boundary-audit carrier (registering it
would put its constructor and projection on the mint/erase report), but its
kind-licensed operations consume the same witnesses. A carrier-*generic* telescope
(operands at a variable type) contributes its occurrences at the monomorphic call
sites, the same places its witnesses are discharged. -/
def operandCarriers (env : Environment) : Array Name :=
  BoundaryAudit.kindCarrierNames env ++ #[``PropertyKindCalculus.IndividualQuantity]

/-- Every inline occurrence in `decl`'s value, in body order, multiplicity kept — two
uses of one witness are two occurrences. Signature binders are opened first, so operand
names print as the signature spells them. A declaration without a value has none. -/
def occurrencesIn (decl : Name) : MetaM (Array KindOccurrence) := do
  let env ← getEnv
  let some info := env.find? decl
    | throwError "unknown declaration '{decl}'"
  let some v := info.value? | return #[]
  Meta.lambdaTelescope v fun _ body =>
    collectOccurrences env (operandCarriers env) body

open Elab Command in
/-- `#kind_occurrences d` prints every inline occurrence in `d`'s value — each consuming
application's edge with the operand quantities that met there, in body order, with
multiplicity — as a single `info` message suitable for `#guard_msgs` pinning. -/
elab "#kind_occurrences " id:ident : command => liftTermElabM do
  let decl ← realizeGlobalConstNoOverload id
  let occs ← occurrencesIn decl
  if occs.isEmpty then
    logInfo m!"no inline kind occurrences in '{decl}'"
  else
    let lines := occs.toList.map (·.render)
    logInfo m!"inline kind occurrences in '{decl}':\n{String.intercalate "\n" lines}"

/-! ## The port harvest — the kind-typed signature as nodes

A step is a declaration; its ports are read off what it *states*, not what it does: the
telescope's carrier-typed binders (inputs), the result type's carrier-typed product
components (outputs), and the `@[kindConst]` constants its value reads (configuration —
the one port class that needs the value, because a configuration read is a reference,
not a binder). The kind position inside a carrier application is found generically — the
argument whose instantiated binder type is `KindOfProperty` — so a downstream
`@[kindCarrier]` registration ports correctly wherever its kind parameter sits. -/

/-- A harvested port: the node name the signature spells (a binder name, a configuration
constant, or `result`/`result.i` for the result type's components), the kind it is
stated at, and its `Provenance.PortDir` role. -/
structure KindPort where
  /-- The port's node name, as the signature spells it. -/
  node : String
  /-- The kind the signature states, rendered. -/
  kind : String
  /-- The port's role: input, configuration, or output. -/
  dir : Provenance.PortDir
deriving Repr, Inhabited, BEq

/-- One report line: `input x : alphaK`. -/
def KindPort.render (p : KindPort) : String :=
  s!"{p.dir.label} {p.node} : {p.kind}"

/-- The declared constant mints — every `@[kindConst]`-tagged declaration in scope. -/
def configConstants (env : Environment) : NameSet :=
  (BoundaryAudit.boundaryTags env).foldl (init := .empty) fun s t =>
    if t.tier == .kindConst then s.insert t.decl else s

/-- The kind a carrier-headed type states, or `none` if `ty` is not headed by a
registered carrier: the argument(s) whose instantiated binder type is `KindOfProperty`,
rendered. Positional generic — `Quantity k R` and `IndividualQuantity o k R` both
resolve to `k`. -/
def carrierKind? (env : Environment) (carriers : Array Name) (ty : Expr) :
    MetaM (Option String) := do
  let .const c _ := ty.getAppFn | return none
  unless carriers.contains c do return none
  let some ci := env.find? c | return none
  let args := ty.getAppArgs
  let some btys := KindEdges.instantiatedBinderTypes ci.type args | return none
  let kindIdxs := (Array.range args.size).filter fun i =>
    btys[i]!.isConstOf ``KindOfProperty
  if kindIdxs.isEmpty then return none
  let ks ← kindIdxs.mapM fun i => return toString (← Meta.ppExpr args[i]!)
  return some (String.intercalate ", " ks.toList)

/-- The result type's right-spine product components — `A × B × C` is three output
positions. A parenthesized left factor stays one component: positions follow what the
signature spells. -/
partial def prodComponents (ty : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if ty.isAppOfArity ``Prod 2 then
    let args := ty.getAppArgs
    prodComponents args[1]! (acc.push args[0]!)
  else
    acc.push ty

/-- The `@[kindConst]` constants `e` references, in body order, deduplicated — a port is
an interface node, so a constant read twice is one port (the occurrence reading keeps
the two incidence positions). -/
partial def configReads (consts : NameSet) (e : Expr) (acc : Array Name := #[]) :
    Array Name :=
  match e with
  | .const n _ =>
    if consts.contains n && !acc.contains n then acc.push n else acc
  | .app f a => configReads consts a (configReads consts f acc)
  | .lam _ t b _ | .forallE _ t b _ => configReads consts b (configReads consts t acc)
  | .letE _ t v b _ =>
    configReads consts b (configReads consts v (configReads consts t acc))
  | .mdata _ b | .proj _ _ b => configReads consts b acc
  | _ => acc

/-- Every port `decl`'s kind-typed signature states: inputs in signature order, then
configuration reads in body order, then outputs in component order. A binder or
component at a non-carrier type is no port; output node names keep component positions
(`result.1`, `result.3`), so a skipped component leaves its gap visible. -/
def portsOf (decl : Name) : MetaM (Array KindPort) := do
  let env ← getEnv
  let some info := env.find? decl
    | throwError "unknown declaration '{decl}'"
  let carriers := operandCarriers env
  Meta.forallTelescope info.type fun fvars resultTy => do
    let mut ports : Array KindPort := #[]
    for fv in fvars do
      let ty := (← fv.fvarId!.getType).consumeTypeAnnotations
      if let some k ← carrierKind? env carriers ty then
        ports := ports.push
          { node := toString (← fv.fvarId!.getUserName), kind := k, dir := .input }
    if let some v := info.value? then
      for c in configReads (configConstants env) v do
        let some ci := env.find? c | continue
        let node := toString (← Meta.ppExpr (mkConst c (ci.levelParams.map mkLevelParam)))
        let kind ← Meta.forallTelescope ci.type fun _ resTy =>
          return (← carrierKind? env carriers resTy).getD "_"
        ports := ports.push { node := node, kind := kind, dir := .config }
    let comps := prodComponents resultTy
    for i in [0:comps.size] do
      if let some k ← carrierKind? env carriers comps[i]! then
        let node := if comps.size == 1 then "result" else s!"result.{i + 1}"
        ports := ports.push { node := node, kind := k, dir := .output }
    return ports

open Elab Command in
/-- `#kind_ports d` prints every port `d`'s kind-typed signature states — inputs,
configuration reads, outputs, each with its stated kind — as a single `info` message
suitable for `#guard_msgs` pinning. -/
elab "#kind_ports " id:ident : command => liftTermElabM do
  let decl ← realizeGlobalConstNoOverload id
  let ports ← portsOf decl
  if ports.isEmpty then
    logInfo m!"no kind ports in '{decl}'"
  else
    let lines := ports.toList.map (·.render)
    logInfo m!"kind ports of '{decl}':\n{String.intercalate "\n" lines}"

end PropertyKindCalculus.KindIncidence
