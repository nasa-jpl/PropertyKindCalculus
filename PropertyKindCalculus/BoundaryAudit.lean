/-
# BoundaryAudit — the Lean-aware boundary audit (invariants 6 & 7)

A grep cannot see through `⟨…⟩` constructor sugar, structure-eta `Expr.proj` projections, or
the `match_N`/`_proof_N` auxiliaries Lean lifts out of a definition, and it cannot tell a
parity *theorem about* `.magnitude` (legitimate — a statement in `Prop`) from a compute body
that *exits* the calculus (a defect). So compliance with the two ingress/interior invariants —
"no anonymous mints at the boundary" (6) and "kinds to the bottom, no interior boundaries" (7)
— cannot be checked by text. It is checked here, by an environment-walking elaborator command,
the sibling of `#kind_edges` (which enumerates the kind-algebra's *edges*; this enumerates its
*boundaries*).

The paradigm's guarantee is *machine-enumerable*, exactly as `#print axioms` is the audit for
sorry-freeness and `#kind_edges` is the audit for edge-soundness: every boundary site is either
tagged with the tier that sanctions it, or it is a violation the build fails on.

## The sanctioned-site registry — three tier attributes

  * `@[kindCrossing]` — an authored *crossing*: a named `def` whose body is the one
    carrier-level place two kinds genuinely meet (`nkToEps`, `clayPctOfMassFraction`,
    `fresnelGeomOfAngleQ`, the dedicated ↔ generic re-typings). The kinds are stated in its
    signature; the mint/erasure inside is the crossing's mechanism, reviewed once.
  * `@[carrierVocab]` — a registered *carrier-vocabulary exception*: representation plumbing
    that legitimately drops to the carrier for an operation the kind algebra does not name
    (`complexSqrtPos`, `qMin`, `qRelu`, a `map` over a coefficient table), kind-preserving by
    construction.
  * `@[kindEmission]` — a genuine *emission boundary* (invariant 4): the grandfathered naked
    erasure layer (until it is retired), the deploy drivers, the tape recorders — where a
    kinded value legitimately becomes a naked one for a consumer outside the calculus.

## The carrier registry — `@[kindCarrier]`

The audit detects a boundary as an application of a *carrier structure*'s constructor (a mint)
or first-field projection (an erasure). `Quantity` is the universal carrier; `CertifiedQuantity`
is its certified sibling; downstream layers add their own (the soil-moisture model's
`DedicatedQuantity`). `@[kindCarrier]` registers a single-field quantity-like structure so the
audit recognizes its mints and erasures — the same open-registry discipline as the kind
declarations themselves.

## The commands

  * `#kind_boundary_audit ns …` — walks every compute `def` in the namespaces, reporting each
    declaration that mints (constructs) or erases (projects) a carrier, with the kinds it mints;
    a boundary-active declaration that carries no tier attribute is a **violation**. Pinned by
    `#guard_msgs` in an indexed probe, a new interior boundary then fails the build the way a new
    axiom fails the profile guard.
  * `#kind_crossings [ns …]` — enumerates the tagged registry with each site's docstring, the
    invariant-5-style enumeration for boundaries.

Like `KindEdges`, this module imports `Lean` and is built by the package glob but kept out of
the prelude-only `import PropertyKindCalculus` spine.
-/

import Lean
import PropertyKindCalculus.Quantity
import PropertyKindCalculus.CertifiedIngest

namespace PropertyKindCalculus.BoundaryAudit

open Lean

/-! ## The tier registry -/

/-- The three sanctioned boundary tiers, strongest (most-constrained) first. -/
inductive BoundaryTier where
  /-- An authored crossing where two kinds genuinely meet (`@[kindCrossing]`). -/
  | kindCrossing
  /-- A carrier-vocabulary exception — representation plumbing (`@[carrierVocab]`). -/
  | carrierVocab
  /-- A genuine emission boundary — a naked value leaves the calculus (`@[kindEmission]`). -/
  | kindEmission
deriving DecidableEq, Repr, Inhabited

/-- How a tier prints in the audit report. -/
def BoundaryTier.label : BoundaryTier → String
  | .kindCrossing => "kindCrossing"
  | .carrierVocab => "carrierVocab"
  | .kindEmission => "kindEmission"

/-- One tagged boundary site: the declaration and the tier that sanctions it. -/
structure BoundaryTag where
  /-- The tagged declaration. -/
  decl : Name
  /-- The tier sanctioning the boundary. -/
  tier : BoundaryTier
deriving Repr, Inhabited

/-- The environment extension collecting every `@[kindCrossing]`/`@[carrierVocab]`/
`@[kindEmission]`-tagged declaration. -/
initialize boundaryExt :
    SimplePersistentEnvExtension BoundaryTag (Array BoundaryTag) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

syntax (name := kindCrossingAttr) "kindCrossing" : attr
syntax (name := carrierVocabAttr) "carrierVocab" : attr
syntax (name := kindEmissionAttr) "kindEmission" : attr

initialize registerBuiltinAttribute {
  name  := `kindCrossingAttr
  descr := "An authored kind crossing — the one carrier-level place two kinds meet (invariant 7)."
  add   := fun decl _stx _kind =>
    modifyEnv fun env => boundaryExt.addEntry env { decl := decl, tier := .kindCrossing }
}

initialize registerBuiltinAttribute {
  name  := `carrierVocabAttr
  descr := "A carrier-vocabulary exception — kind-preserving representation plumbing (invariant 7)."
  add   := fun decl _stx _kind =>
    modifyEnv fun env => boundaryExt.addEntry env { decl := decl, tier := .carrierVocab }
}

initialize registerBuiltinAttribute {
  name  := `kindEmissionAttr
  descr := "A genuine emission boundary — a kinded value becomes naked for a consumer (invariant 4)."
  add   := fun decl _stx _kind =>
    modifyEnv fun env => boundaryExt.addEntry env { decl := decl, tier := .kindEmission }
}

/-- Every boundary tag harvested into `env`. -/
def boundaryTags (env : Environment) : Array BoundaryTag := boundaryExt.getState env

/-! ## The carrier registry -/

/-- The environment extension collecting every `@[kindCarrier]`-registered structure. -/
initialize kindCarrierExt :
    SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

syntax (name := kindCarrierAttr) "kindCarrier" : attr

initialize registerBuiltinAttribute {
  name  := `kindCarrierAttr
  descr := "Register a single-field quantity-like carrier structure for the boundary audit."
  add   := fun decl _stx _kind => do
    unless isStructure (← getEnv) decl do
      throwError "`@[kindCarrier]` expects a structure; '{decl}' is not one"
    modifyEnv fun env => kindCarrierExt.addEntry env decl
}

/-- Every carrier structure the audit recognizes: the two universal PKC carriers `Quantity` and
`CertifiedQuantity` (built in, since a `registerBuiltinAttribute` attribute is not active in its
own defining module), plus every `@[kindCarrier]`-registered structure from downstream layers
(e.g. the model's `DedicatedQuantity`). -/
def kindCarrierNames (env : Environment) : Array Name :=
  #[``PropertyKindCalculus.Quantity, ``PropertyKindCalculus.CertifiedQuantity]
    ++ kindCarrierExt.getState env

/-! ## The environment walk -/

/-- A registered carrier's detection footprint: its constructor (a mint) and its first-field
projection (an erasure), with the arities that fully-applied occurrences carry. -/
structure CarrierSpec where
  /-- The carrier structure's name (for `Expr.proj` matching). -/
  structName : Name
  /-- The constructor name (a mint is a fully-applied `structName.mk`). -/
  ctorName : Name
  /-- The constructor's full application arity (`numParams + numFields`). -/
  ctorArity : Nat
  /-- The first-field projection function (an erasure is a fully-applied `structName.field₀`). -/
  projName : Name
  /-- The projection's full application arity (`numParams + 1`). -/
  projArity : Nat
deriving Inhabited

/-- Build a `CarrierSpec` for a registered carrier structure, or `none` if it is not a
single-field-or-more structure with a resolvable constructor. -/
def mkCarrierSpec (env : Environment) (cn : Name) : Option CarrierSpec := do
  let .inductInfo iv ← env.find? cn | none
  let [ctorName] := iv.ctors | none
  let .ctorInfo cv ← env.find? ctorName | none
  let fields := getStructureFields env cn
  let field₀ ← fields[0]?
  return {
    structName := cn
    ctorName   := ctorName
    ctorArity  := cv.numParams + cv.numFields
    projName   := cn ++ field₀
    projArity  := cv.numParams + 1
  }

/-- Walk an expression, collecting every carrier *mint* (the kind argument of a fully-applied
constructor) and recording whether any carrier *erasure* (a first-field projection, in either
`Expr.proj` or projection-application form) occurs. Mirrors `KindEdges.collectEdges`'s recursion
over the reducible `Expr` shapes. -/
partial def collectBoundary (specs : Array CarrierSpec) (e : Expr)
    (mints : Array Expr) (erases : Bool) : Array Expr × Bool :=
  let (mints, erases) := Id.run do
    let mut ms := mints
    let mut er := erases
    for s in specs do
      if e.isAppOfArity s.ctorName s.ctorArity then
        if let some a := (e.getAppArgs)[0]? then ms := ms.push a
      if e.isAppOfArity s.projName s.projArity then
        er := true
    match e with
    | .proj sn _ _ => if specs.any (·.structName == sn) then er := true
    | _ => pure ()
    return (ms, er)
  match e with
  | .app f a =>
      let (m₁, e₁) := collectBoundary specs f mints erases
      collectBoundary specs a m₁ e₁
  | .lam _ t b _ =>
      let (m₁, e₁) := collectBoundary specs t mints erases
      collectBoundary specs b m₁ e₁
  | .forallE _ t b _ =>
      let (m₁, e₁) := collectBoundary specs t mints erases
      collectBoundary specs b m₁ e₁
  | .letE _ t v b _ =>
      let (m₁, e₁) := collectBoundary specs t mints erases
      let (m₂, e₂) := collectBoundary specs v m₁ e₁
      collectBoundary specs b m₂ e₂
  | .mdata _ b => collectBoundary specs b mints erases
  | .proj _ _ b => collectBoundary specs b mints erases
  | _ => (mints, erases)

/-- Strip internal name components (`._proof_N`, `.match_N`, numeric suffixes) so a lifted
call-site mint is attributed to the definition that authored it — the `KindEdges.parentOf`
precedent, widened to the matcher/equation auxiliaries a compute body generates. -/
def parentOf (n : Name) : Name :=
  match n with
  | .str p s =>
      if s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_"
          || s.startsWith "eq_" || s.startsWith "unsafe_" then parentOf p else n
  | .num p _ => parentOf p
  | _ => n

/-- The final-component names of the machinery a structure/inductive declaration generates —
constructors, recursors, projections' companions, `noConfusion`, `injEq`, `sizeOf`. These are
never *authored* compute, so the audit skips them (a carrier's own `.mk`/`.magnitude` is the
mint/erase *mechanism*, not a boundary site that could be mis-authored). -/
def generatedSuffixes : List String :=
  ["rec", "recOn", "casesOn", "brecOn", "below", "ibelow", "binductionOn",
   "noConfusion", "noConfusionType", "injEq", "sizeOf", "mk", "ofNat", "toCtorIdx"]

/-- Is `name` compiler-generated machinery the audit should skip — an auxiliary recursor, or a
declaration whose final component is a generated suffix, or a registered carrier's own
constructor/projection function? -/
def isGeneratedMachinery (env : Environment) (specs : Array CarrierSpec) (name : Name) : Bool :=
  isAuxRecursor env name
  || (match name with
      | .str _ s => generatedSuffixes.contains s
      | _ => false)
  || specs.any (fun s => s.projName == name || s.ctorName == name)

/-! ## `#kind_boundary_audit` -/

open Elab Command in
/-- `#kind_boundary_audit ns …` walks every compute `def` under the given namespaces, reports
each declaration that mints or erases a registered carrier (with the kinds it mints), and marks
a boundary-active declaration that carries no tier attribute as a **violation**. One sorted
`info` message, suitable for `#guard_msgs` pinning; a new untagged interior boundary then fails
the build. Theorems and `Prop`-valued declarations are skipped — a parity statement is legitimately
*about* `.magnitude`. -/
elab "#kind_boundary_audit" nss:ident+ : command => liftTermElabM do
  let env ← getEnv
  let targets := nss.map (·.getId)
  let specs := (kindCarrierNames env).filterMap (mkCarrierSpec env)
  let tags := boundaryTags env
  let mut mintMap : Std.HashMap Name (Array String) := {}
  let mut eraseSet : Std.HashSet Name := {}
  let mut parents : Std.HashSet Name := {}
  for (name, info) in env.constants.toList do
    let parent := parentOf name
    unless targets.any (fun ns => ns.isPrefixOf parent) do continue
    if info matches .thmInfo _ then continue
    if isGeneratedMachinery env specs parent then continue
    let some body := info.value? | continue
    if ← Meta.isProp info.type then continue
    let (mints, erases) := collectBoundary specs body #[] false
    if mints.isEmpty && !erases then continue
    let mintStrs ← mints.mapM fun a => return toString (← Meta.ppExpr a)
    parents := parents.insert parent
    if !mintStrs.isEmpty then
      mintMap := mintMap.insert parent ((mintMap.getD parent #[]) ++ mintStrs)
    if erases then eraseSet := eraseSet.insert parent
  -- Assemble one line per boundary-active declaration.
  let tierOf : Name → Option BoundaryTier := fun p => (tags.find? (·.decl == p)).map (·.tier)
  let mut lines : Array String := #[]
  let mut nSanctioned := 0
  let mut nViolations := 0
  for parent in parents.toList do
    let mints := (mintMap.getD parent #[]).toList.eraseDups.toArray.qsort (· < ·)
    let descr :=
      if mints.isEmpty then "erases (emission-only)"
      else s!"mints: {String.intercalate ", " mints.toList}"
    let tag : String :=
      match tierOf parent with
      | some t => s!"[{t.label}]"
      | none   => "⚠ UNTAGGED"
    match tierOf parent with
    | some _ => nSanctioned := nSanctioned + 1
    | none   => nViolations := nViolations + 1
    lines := lines.push s!"{tag} {parent} — {descr}"
  let sorted := lines.qsort (· < ·)
  if sorted.isEmpty then
    logInfo m!"boundary audit — no boundary sites in the given namespaces"
  else
    let summary :=
      if nViolations == 0 then
        s!"{nSanctioned} boundary site(s), all tagged — clean"
      else
        s!"{nSanctioned + nViolations} boundary site(s): {nSanctioned} tagged, {nViolations} UNTAGGED — invariant 6/7 violation"
    logInfo m!"boundary audit:\n{String.intercalate "\n" sorted.toList}\n{summary}"

/-! ## `#kind_crossings` -/

open Elab Command in
/-- `#kind_crossings [ns …]` enumerates the tagged boundary registry — every
`@[kindCrossing]`/`@[carrierVocab]`/`@[kindEmission]` site with the first line of its docstring —
grouped by tier and sorted, optionally filtered to the given namespaces. The invariant-5-style
enumeration for boundaries: a reviewer reads the sanctioned sites the way `#kind_edges` reads the
sanctioned edges. -/
elab "#kind_crossings" nss:ident* : command => liftTermElabM do
  let env ← getEnv
  let targets := nss.map (·.getId)
  let inScope : Name → Bool := fun d =>
    targets.isEmpty || targets.any (fun ns => ns.isPrefixOf d)
  let tags := (boundaryTags env).filter (fun t => inScope t.decl)
  if tags.isEmpty then
    logInfo m!"no tagged boundary crossings in scope"
    return
  let mut lines : Array String := #[]
  for t in tags do
    let doc := (← findDocString? env t.decl).getD ""
    let firstLine := ((doc.splitOn "\n").headD "").trimAscii.toString
    lines := lines.push s!"[{t.tier.label}] {t.decl} — {firstLine}"
  let sorted := lines.qsort (· < ·)
  logInfo m!"tagged boundary crossings:\n{String.intercalate "\n" sorted.toList}"

end PropertyKindCalculus.BoundaryAudit
