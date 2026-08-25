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

## The sanctioned-site registry — five tier attributes

  * `@[kindCrossing]` — an authored *crossing*: a named `def` whose body is the one
    carrier-level place two kinds genuinely meet (`nkToEps`, `clayPctOfMassFraction`,
    `fresnelGeomOfAngleQ`, the dedicated ↔ generic re-typings). The kinds are stated in its
    signature, on the ARGUMENT side as much as the result — enforced, not just documented:
    `add` rejects a `@[kindCrossing]` declaration none of whose arguments carries a registered
    carrier, because a crossing by definition goes FROM an already-kinded value, and a
    declaration with no kinded argument at all has nothing to cross from (invariant 6, tier (i)
    — "by construction," where the *whole* evidence is that the inputs were already kinded).
  * `@[kindIngest]` — an authored *checked ingest mint* (invariant 6, evidence tier (ii)): raw,
    external/host data — a raw npy column, a JSON blob, an env-var's text, an inline geometric
    bounds check — enters the calculus for the first time and is admitted through SOME check (a
    `KindAdmissible`/`BatchAdmissible` instance, an ad hoc range test, or a fallible parse). No
    argument carries a kind, because none has been established yet — that is the entire point
    of an ingest boundary; the check performed is this declaration's evidence, reviewed once.
    The dual of `@[kindCrossing]`: a crossing REQUIRES a kinded argument, an ingest requires
    that NONE be presupposed.
  * `@[carrierVocab]` — a registered *carrier-vocabulary exception*: representation plumbing
    that legitimately drops to the carrier for an operation the kind algebra does not name
    (`complexSqrtPos`, `qMin`, `qRelu`, a `map` over a coefficient table), kind-preserving by
    construction.
  * `@[kindConst]` — a declared *constant mint* (invariant 6, evidence tier (iii)): a
    declaration whose boundary activity is minting adjudicated values — a cited coefficient
    table, a configuration bound or box, a seed, a threshold, or a structural constant of the
    model (a zero accumulator, the vacuum index `1`, a literal exponent). The mint's value is
    data, not dataflow; its provenance is the declaration's docstring. A NULLARY
    `@[kindCrossing]` candidate — one with no argument at all — is definitionally this tier and
    not tier (i): a fixed literal has nothing to cross from either.
  * `@[kindEmission]` — a genuine *emission boundary* (invariant 4): the deploy drivers, the
    tape recorders, and the parity apparatus — the kinded ↔ bare re-typings the erasure
    theorems are stated over — where a kinded value legitimately becomes a naked one for a
    consumer outside the calculus.

## The carrier registry — `@[kindCarrier]`

The audit detects a boundary as an application of a *carrier structure*'s constructor (a mint)
or first-field projection (an erasure). `Quantity` is the universal ratio/interval/ordinal
carrier, `CertifiedQuantity` its certified sibling, and `NominalValue` the nominal-scale
carrier (§13.2.1 — a magnitude-free designation, ingest and erasure mirroring `Quantity`'s own
story point for point); downstream layers add their own (the soil-moisture model's
`DedicatedQuantity`). `@[kindCarrier]` registers a single-field quantity-like structure so the
audit recognizes its mints and erasures — the same open-registry discipline as the kind
declarations themselves.

## The attestor registry — `@[kindAttest]`

An *attested* mint is an authored `⟨…⟩` written through a registered attestor
(`Quantity.attest` is built in) that names its reason at the call site. The walk cannot see
through ANY named wrapper — a helper's body is walked once, under the helper's own name, so a
declaration that mints through a wrapper shows nothing at its own site. Registration is what
turns that hiding into accountability: the audit recognizes a registered attestor's
applications, reports each site with the reason string it harvests from the argument, and
*skips the attestor's own body* — its one raw mint is the sanctioned mechanism, reviewed at
registration, the same reason a carrier's own `.mk` is not a site. An unregistered wrapper
remains what it always was — invisible — which is why attestors are registered, never ad hoc.

The discipline the split serves: raw mints are the *suspect* column (a declaration-level tier
tag covers however many its body holds, multiplicity unseen), attested mints the *reviewed*
one — each surviving site carries its own one-line justification into the pinned report. An
attestation is a claim with no machine-checkable evidence; where evidence exists, the licensed
route (a `CertifiedIngest`/`KindAdmissible` check, a `ProductKind`/`QuotientKind` witness edge,
`castCarrier`, `Quantity.get!`, the empty-array `default`) is the answer, not `attest`.

## The commands

  * `#kind_boundary_audit ns …` — walks every compute `def` in the namespaces, reporting each
    declaration that mints (constructs) or erases (projects) a carrier, with the kinds it mints
    and each attested mint's kind and harvested reason;
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
import PropertyKindCalculus.NominalValue
import PropertyKindCalculus.CertifiedIngest

namespace PropertyKindCalculus.BoundaryAudit

open Lean

/-! ## The tier registry -/

/-- The five sanctioned boundary tiers. -/
inductive BoundaryTier where
  /-- An authored crossing where two kinds genuinely meet (`@[kindCrossing]`). -/
  | kindCrossing
  /-- A checked ingest mint — raw/host data enters through some check (`@[kindIngest]`). -/
  | kindIngest
  /-- A carrier-vocabulary exception — representation plumbing (`@[carrierVocab]`). -/
  | carrierVocab
  /-- A declared constant mint — an adjudicated value enters the calculus (`@[kindConst]`). -/
  | kindConst
  /-- A genuine emission boundary — a naked value leaves the calculus (`@[kindEmission]`). -/
  | kindEmission
deriving DecidableEq, Repr, Inhabited

/-- How a tier prints in the audit report. -/
def BoundaryTier.label : BoundaryTier → String
  | .kindCrossing => "kindCrossing"
  | .kindIngest   => "kindIngest"
  | .carrierVocab => "carrierVocab"
  | .kindConst   => "kindConst"
  | .kindEmission => "kindEmission"

/-- One tagged boundary site: the declaration and the tier that sanctions it. -/
structure BoundaryTag where
  /-- The tagged declaration. -/
  decl : Name
  /-- The tier sanctioning the boundary. -/
  tier : BoundaryTier
deriving Repr, Inhabited

/-- The environment extension collecting every `@[kindCrossing]`/`@[kindIngest]`/
`@[carrierVocab]`/`@[kindConst]`/`@[kindEmission]`-tagged declaration. -/
initialize boundaryExt :
    SimplePersistentEnvExtension BoundaryTag (Array BoundaryTag) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-! ## The carrier registry

Moved ahead of the tier attributes below: `@[kindCrossing]`'s own `add` callback needs
`kindCarrierNames`/`mkCarrierSpec` to check an argument for a carrier, so the registry they
belong to must already be in scope. -/

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

/-- Every carrier structure the audit recognizes: the three built-in PKC carriers `Quantity`
(ratio/interval/ordinal, magnitude-bearing), `CertifiedQuantity` (its certified sibling), and
`NominalValue` (the nominal-scale designation carrier — built in for the same reason
`Quantity`/`CertifiedQuantity` are: a `registerBuiltinAttribute` attribute is not active in its
own defining module, and none of the three is defined here), plus every `@[kindCarrier]`-
registered structure from downstream layers (e.g. the model's `DedicatedQuantity`). -/
def kindCarrierNames (env : Environment) : Array Name :=
  #[``PropertyKindCalculus.Quantity, ``PropertyKindCalculus.CertifiedQuantity,
    ``PropertyKindCalculus.NominalValue]
    ++ kindCarrierExt.getState env

/-! ## The nominal designation registry — `@[kindNominal k]`

A **nominal** kind-of-property (§13.2.1) has designations, not magnitudes, and there are two
honest ways to carry one. When the designations ride a *shared* representation — a `String`
path, a `UInt32` code — the type says nothing about which kind is meant, and `NominalValue k R`
is what closes the argument-swap hole: a `/proc/meminfo` dump and the field key to look up in
it are both `String`s. When the designations are a *bespoke finite label set*, the type already
identifies the kind uniquely, and wrapping it re-states at every binder what the declaration
said once. `@[kindNominal k]` is the declaration: **this inductive is the designation set of the
nominal kind `k`**, registered once, so the harvest reads a `Polarization` binder as an
interface node at its kind instead of as naked data.

The registration is checked, because each condition is part of the claim:

  * `k` must be a `KindOfProperty` whose `scale` reduces to `.nominal` — a designation set for a
    ratio kind would be a magnitude wearing a label's clothes;
  * the tagged declaration must be an inductive whose constructors are all **nullary** — a
    designation is a label, and a constructor with an argument is a container, which is what
    `NominalValue`'s `R` parameter is for;
  * a designation type registers at exactly ONE kind — the whole reason the bespoke form needs
    no wrapper is that its type determines its kind, and a second registration would take that
    back. -/

/-- The environment extension mapping each `@[kindNominal]`-registered designation type to the
nominal kind it designates. -/
initialize kindNominalExt :
    SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-- The nominal kind a type designates, or `none` if it is not a registered designation set. -/
def nominalKindOf? (env : Environment) (typeName : Name) : Option Name :=
  (kindNominalExt.getState env).findSome? fun (t, k) => if t == typeName then some k else none

syntax (name := kindNominalAttr) "kindNominal" ident : attr

initialize registerBuiltinAttribute {
  name  := `kindNominalAttr
  descr := "Register a bespoke finite label set as the designation set of a nominal kind."
  add   := fun decl stx _kind => do
    let kindName ← realizeGlobalConstNoOverload stx[1]
    let env ← getEnv
    let some ki := env.find? kindName
      | throwError "`@[kindNominal]` could not find '{kindName}' in the environment"
    unless ki.type.isConstOf ``PropertyKindCalculus.KindOfProperty do
      throwError "`@[kindNominal]` expects a `KindOfProperty`; '{kindName}' is not one"
    let scale ← Meta.MetaM.run' <| Meta.whnf <|
      mkApp (mkConst ``PropertyKindCalculus.KindOfProperty.scale) (mkConst kindName)
    unless scale.isConstOf ``PropertyKindCalculus.ScaleType.nominal do
      throwError "`@[kindNominal]` expects a kind of NOMINAL scale; '{kindName}' is         '{scale}'. A designation set for a kind that has magnitudes would license equality         on something the calculus already gives richer operations to."
    let some (.inductInfo ii) := env.find? decl
      | throwError "`@[kindNominal]` expects an inductive type; '{decl}' is not one"
    for c in ii.ctors do
      let some ci := env.find? c | continue
      unless ci.type.getForallBinderNames.length == ii.numParams do
        throwError "`@[kindNominal]` expects every constructor to be nullary; '{c}' takes           arguments. A designation is a label — a constructor carrying data is a container,           which is what `NominalValue`'s representation parameter is for."
    if let some prior := nominalKindOf? env decl then
      unless prior == kindName do
        throwError "'{decl}' already designates '{prior}'. A bespoke designation set needs no           wrapper precisely because its type determines its kind; registering it at a second           kind takes that back."
    modifyEnv fun env => kindNominalExt.addEntry env (decl, kindName)
}

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

/-! ## The `@[kindCrossing]` argument check

A crossing's whole claim is that two kinds meet — so its signature must actually SHOW a kind on
the way in, not just on the way out. `mentionsCarrier` decides that, structurally, at the point
`@[kindCrossing]` is applied (so a miscategorized ingest fails the build where it is written,
not three imports later at `#kind_boundary_audit`). -/

/-- The domain types of a Pi-type's leading binder chain, in declaration order — every
explicit, implicit, and instance-implicit argument a signature states, before its return type.
Binder info is not inspected: an instance argument can no more be a carrier than an implicit
type can, so a filter would only be something to remember, never something to gain. -/
def piArgTypes : Expr → List Expr
  | .forallE _ d b _ => d :: piArgTypes b
  | _ => []

/-- Bounded structural search: does `ty` mention a registered carrier's structure name, either
directly, through one of the container formers a real signature here actually uses (`List`/
`Array`/`Option`/`Prod`/`Except`/`Sum`), or through the field types of a single-constructor,
non-carrier structure — so a plain data record built OVER kinded fields (`Marker`, `SizingLine`,
or a PARAMETRIC one like `CholQ α`, four `Quantity _ α` fields at four different kinds) reads as
kinded even though the record itself is not a registered carrier, while a plain data record
over bare `Float`s (an affine transform's six coefficients) correctly does not? The constructor's
own (unapplied, generic) type is walked directly — a structure's leading parameter binders
(`α : Type`) are included in that walk along with its fields, but they simply never match a
carrier, so there is nothing to gain by singling monomorphic structures out and something to
lose (`CholQ`'s own crossing, rejected until this was widened). `fuel` bounds the unwrap depth:
every shape the check actually needs to see through is shallow (a record of quantities, a
product, a list of records), so a small fixed fuel is enough, and a type that would need more
is, correctly, treated as opaque rather than risking a loop on a self-referential type. -/
partial def mentionsCarrier (env : Environment) (specs : Array CarrierSpec) (fuel : Nat)
    (ty : Expr) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    match ty.getAppFn with
    | .const n _ =>
        if specs.any (·.structName == n) then true
        else
          let args := ty.getAppArgs
          if (n == ``List || n == ``Array || n == ``Option) && args.size == 1 then
            mentionsCarrier env specs fuel args[0]!
          else if (n == ``Prod || n == ``Except || n == ``Sum) && args.size == 2 then
            mentionsCarrier env specs fuel args[0]! || mentionsCarrier env specs fuel args[1]!
          else match env.find? n with
            | some (.inductInfo iv) =>
                (match iv.ctors with
                 | [ctorName] =>
                     match env.find? ctorName with
                     | some (.ctorInfo cv) =>
                         (piArgTypes cv.type).any (mentionsCarrier env specs fuel)
                     | _ => false
                 | _ => false)
            | _ => false
    | _ => false

/-! ## The attestor registry — `@[kindAttest]`

Header doctrine: an attested mint is an authored `⟨…⟩` written through a *registered* wrapper
that names its reason at the call site. Registration closes the wrapper loophole (a named
helper hides its mint from the walk) by turning the wrapper into a recognized, enumerated
site class. -/

/-- The environment extension collecting every `@[kindAttest]`-registered attestor. -/
initialize kindAttestExt :
    SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-- A registered attestor's detection footprint, derived from its signature: the full
application arity, the position of the `KindOfProperty` argument (the attested kind), and the
position of the `String` argument (the reason). -/
structure AttestSpec where
  /-- The attestor declaration (a mint through it is a fully-applied occurrence). -/
  declName : Name
  /-- The attestor's full application arity (its whole binder telescope). -/
  arity : Nat
  /-- The index of the first `KindOfProperty` argument — the attested kind. -/
  kindIdx : Nat
  /-- The index of the first `String` argument — the reason. -/
  reasonIdx : Nat
deriving Inhabited

/-- Build an `AttestSpec` from an attestor's signature, or `none` if the signature does not
carry both a `KindOfProperty` argument and a `String` argument — the shape the harvest needs. -/
def mkAttestSpec (env : Environment) (n : Name) : Option AttestSpec := do
  let info ← env.find? n
  let args := piArgTypes info.type
  let kindIdx ← args.findIdx? (·.isConstOf ``KindOfProperty)
  let reasonIdx ← args.findIdx? (·.isConstOf ``String)
  return { declName := n, arity := args.length, kindIdx, reasonIdx }

syntax (name := kindAttestAttr) "kindAttest" : attr

initialize registerBuiltinAttribute {
  name  := `kindAttestAttr
  descr := "Register an authored-mint attestor: the audit reports each call site with its harvested reason and skips the attestor's own body."
  add   := fun decl _stx _kind => do
    let env ← getEnv
    unless (mkAttestSpec env decl).isSome do
      throwError "`@[kindAttest]` expects a declaration taking a `KindOfProperty` argument \
        (the attested kind) and a `String` argument (the reason) — '{decl}' has neither or \
        only one. Without both, attested sites could not be harvested, and the wrapper would \
        HIDE its mint from the walk instead of putting it on the record."
    modifyEnv fun env => kindAttestExt.addEntry env decl
}

/-- Every attestor the audit recognizes: the built-in `Quantity.attest` (built in for the same
reason the three carriers are — an attribute is not active in its own defining module), plus
every `@[kindAttest]`-registered attestor from downstream layers. -/
def kindAttestNames (env : Environment) : Array Name :=
  #[``PropertyKindCalculus.Quantity.attest] ++ kindAttestExt.getState env

/-! ## The tier attributes -/

syntax (name := kindCrossingAttr) "kindCrossing" : attr
syntax (name := kindIngestAttr) "kindIngest" : attr
syntax (name := carrierVocabAttr) "carrierVocab" : attr
syntax (name := kindConstAttr) "kindConst" : attr
syntax (name := kindEmissionAttr) "kindEmission" : attr

initialize registerBuiltinAttribute {
  name  := `kindCrossingAttr
  descr := "An authored kind crossing — the one carrier-level place two kinds meet (invariant 7)."
  add   := fun decl _stx _kind => do
    let env ← getEnv
    let some info := env.find? decl
      | throwError "`@[kindCrossing]` could not find '{decl}' in the environment"
    let specs := (kindCarrierNames env).filterMap (mkCarrierSpec env)
    unless (piArgTypes info.type).any (mentionsCarrier env specs 6) do
      throwError "`@[kindCrossing]` requires at least one argument whose type is (or contains) \
        a registered carrier (`Quantity`, `NominalValue`, or a `@[kindCarrier]`-registered \
        structure) — '{decl}' takes none. A crossing is where an ALREADY-KINDED value meets its \
        target kind; a declaration with no kinded argument is a boundary MINT, not a crossing. \
        Tag a checked ingest (raw/host data admitted through some check) `@[kindIngest]`, or a \
        fixed literal/adjudicated constant `@[kindConst]`, instead."
    modifyEnv fun env => boundaryExt.addEntry env { decl := decl, tier := .kindCrossing }
}

initialize registerBuiltinAttribute {
  name  := `kindIngestAttr
  descr := "An authored checked ingest mint — raw/host data enters the calculus through some check (invariant 6, tier ii)."
  add   := fun decl _stx _kind =>
    modifyEnv fun env => boundaryExt.addEntry env { decl := decl, tier := .kindIngest }
}

initialize registerBuiltinAttribute {
  name  := `carrierVocabAttr
  descr := "A carrier-vocabulary exception — kind-preserving representation plumbing (invariant 7)."
  add   := fun decl _stx _kind =>
    modifyEnv fun env => boundaryExt.addEntry env { decl := decl, tier := .carrierVocab }
}

initialize registerBuiltinAttribute {
  name  := `kindConstAttr
  descr := "A declared constant mint — a cited table, config bound, seed, threshold, or structural constant (invariant 6, tier iii)."
  add   := fun decl _stx _kind =>
    modifyEnv fun env => boundaryExt.addEntry env { decl := decl, tier := .kindConst }
}

initialize registerBuiltinAttribute {
  name  := `kindEmissionAttr
  descr := "A genuine emission boundary — a kinded value becomes naked for a consumer (invariant 4)."
  add   := fun decl _stx _kind =>
    modifyEnv fun env => boundaryExt.addEntry env { decl := decl, tier := .kindEmission }
}

/-- Every boundary tag harvested into `env`. -/
def boundaryTags (env : Environment) : Array BoundaryTag := boundaryExt.getState env

/-! ## The environment walk -/

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

/-- Walk an expression, collecting every *attested* mint — a fully-applied registered attestor —
as the pair (attested-kind argument, reason if the reason argument is a string literal; `none`
marks a dynamically-built reason). Multiplicity is kept: each application is one site. -/
partial def collectAttests (specs : Array AttestSpec) (e : Expr)
    (acc : Array (Expr × Option String)) : Array (Expr × Option String) :=
  let acc := Id.run do
    let mut a := acc
    for s in specs do
      if e.isAppOfArity s.declName s.arity then
        let args := e.getAppArgs
        if let some kindArg := args[s.kindIdx]? then
          let reason := match args[s.reasonIdx]? with
            | some (.lit (.strVal str)) => some str
            | _ => none
          a := a.push (kindArg, reason)
    return a
  match e with
  | .app f a =>
      collectAttests specs a (collectAttests specs f acc)
  | .lam _ t b _ =>
      collectAttests specs b (collectAttests specs t acc)
  | .forallE _ t b _ =>
      collectAttests specs b (collectAttests specs t acc)
  | .letE _ t v b _ =>
      collectAttests specs b (collectAttests specs v (collectAttests specs t acc))
  | .mdata _ b => collectAttests specs b acc
  | .proj _ _ b => collectAttests specs b acc
  | _ => acc

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

/-! ## The harvest

`#kind_boundary_audit` below is a *renderer* over `boundarySites`. The split exists because the
audit's result is wanted in two forms: as the `info` message an author reads in the InfoView (and a
probe pins with `#guard_msgs`), and as table rows a document renders — the blueprint's kind-crossing
index and the doc-gen4 page both need "which kinds does this crossing mint", which is exactly what
the walk already computes and used to format away into a string. `PropertyKindCalculus.Index`
consumes the structured form; nothing else changed, and the pinned report is byte-identical. -/

/-- One boundary-active declaration: what the walk found, before any formatting. `tier` is `none`
for an untagged site — the violation the audit reports. -/
structure BoundarySite where
  /-- The authoring declaration (lifted auxiliaries attributed to their parent). -/
  decl : Name
  /-- The tier sanctioning this site, or `none` if it carries no tier attribute. -/
  tier : Option BoundaryTier
  /-- The kinds minted here, pretty-printed, deduplicated and sorted. -/
  mints : Array String
  /-- The attested mints: each registered-attestor application, rendered as the attested kind
  followed by the harvested reason (`‹…›`, or `(dynamic reason)` for a non-literal), identical
  renderings grouped with an explicit `(×n)` count — multiplicity is the point. -/
  attests : Array String
  /-- Whether the body erases a carrier (projects its first field). -/
  erases : Bool
deriving Repr, Inhabited

/-- Walk every compute `def` under `scope` (empty = unrestricted) and return each declaration that
mints or erases a registered carrier, with the kinds it mints and the tier that sanctions it.

Theorems and `Prop`-valued declarations are skipped: a parity statement is legitimately *about*
`.magnitude`, so it is not a boundary. Results are sorted by declaration name. -/
def boundarySites (scope : Array Name) : MetaM (Array BoundarySite) := do
  let env ← getEnv
  let specs := (kindCarrierNames env).filterMap (mkCarrierSpec env)
  let attNames := kindAttestNames env
  let attSpecs := attNames.filterMap (mkAttestSpec env)
  let tags := boundaryTags env
  let inScope : Name → Bool := fun d => scope.isEmpty || scope.any (fun ns => ns.isPrefixOf d)
  let mut mintMap : Std.HashMap Name (Array String) := {}
  let mut attMap : Std.HashMap Name (Array String) := {}
  let mut eraseSet : Std.HashSet Name := {}
  let mut parents : Std.HashSet Name := {}
  for (name, info) in env.constants.toList do
    let parent := parentOf name
    unless inScope parent do continue
    if info matches .thmInfo _ then continue
    if isGeneratedMachinery env specs parent then continue
    -- A registered attestor's own body is the sanctioned mint *mechanism*, reviewed at
    -- registration — not a site (the same reason a carrier's own `.mk` is skipped).
    if attNames.any (fun a => a == name || a == parent) then continue
    let some body := info.value? | continue
    if ← Meta.isProp info.type then continue
    -- A Prop-former (`def P … : Prop`) is a specification, not compute: like a theorem, it is
    -- legitimately *about* `.magnitude`, so it is not a boundary site.
    if ← Meta.forallTelescopeReducing info.type fun _ resTy => return resTy.isProp then continue
    let (mints, erases) := collectBoundary specs body #[] false
    let atts := collectAttests attSpecs body #[]
    if mints.isEmpty && !erases && atts.isEmpty then continue
    -- A mint under a binder carries loose bvars (`collectBoundary` does not abstract), so its
    -- kind argument is a *variable* of the site, not a nameable kind: render it as one stable
    -- word rather than a de Bruijn index or a pretty-printer failure. Two cases, two DISTINCT
    -- tokens — neither a substring of the other, so a reader (or a grep) can never mistake one
    -- for the other: a wholly-parametric kind renders `(kind-parametric)`; a named kind
    -- *family* applied to the site's variables (`famK s`) keeps its head — the family is real
    -- information, only the argument is unnameable — and renders `famK (parametric)`.
    -- `eraseDups` below then collapses however many same-rendering parametric mints a site
    -- has into one entry.
    let mintStrs ← mints.mapM fun a =>
      if a.hasLooseBVars then
        match a.getAppFn with
        | .const n _ => return s!"{n} (parametric)"
        | _ => return "(kind-parametric)"
      else return toString (← Meta.ppExpr a)
    -- An attested site renders as its kind (the same parametric-token rules as a raw mint)
    -- followed by the harvested reason.
    let attStrs ← atts.mapM fun (kArg, reason) => do
      -- NOT `return` in the else-branch: inside this do-lambda a `return` would exit the
      -- whole per-site rendering, dropping the reason suffix (the do-early-exit footgun).
      let kStr ←
        if kArg.hasLooseBVars then
          match kArg.getAppFn with
          | .const n _ => pure s!"{n} (parametric)"
          | _ => pure "(kind-parametric)"
        else toString <$> Meta.ppExpr kArg
      match reason with
      | some r => pure s!"{kStr} ‹{r}›"
      | none   => pure s!"{kStr} (dynamic reason)"
    parents := parents.insert parent
    if !mintStrs.isEmpty then
      mintMap := mintMap.insert parent ((mintMap.getD parent #[]) ++ mintStrs)
    if !attStrs.isEmpty then
      attMap := attMap.insert parent ((attMap.getD parent #[]) ++ attStrs)
    if erases then eraseSet := eraseSet.insert parent
  let tierOf : Name → Option BoundaryTier := fun p => (tags.find? (·.decl == p)).map (·.tier)
  let mut sites : Array BoundarySite := #[]
  for parent in parents.toList do
    -- Attested mints keep their multiplicity (dedup would hide exactly what the split exists
    -- to show); identical renderings are grouped with an explicit count instead.
    let rawAtts := attMap.getD parent #[]
    let groupedAtts := rawAtts.toList.eraseDups.map fun s =>
      let n := (rawAtts.filter (· == s)).size
      if n > 1 then s!"{s} (×{n})" else s
    sites := sites.push {
      decl    := parent
      tier    := tierOf parent
      mints   := (mintMap.getD parent #[]).toList.eraseDups.toArray.qsort (· < ·)
      attests := groupedAtts.toArray.qsort (· < ·)
      erases  := eraseSet.contains parent }
  return sites.qsort (fun a b => toString a.decl < toString b.decl)

/-- How a site reads in the audit report: the kinds it mints raw, then its attested mints with
their reasons, or emission-only if it merely erases. The two columns are the split the attestor
registry exists for — raw is the suspect column, attested the reviewed one. -/
def BoundarySite.description (s : BoundarySite) : String :=
  let parts : List String :=
    (if s.mints.isEmpty then [] else [s!"mints: {String.intercalate ", " s.mints.toList}"])
    ++ (if s.attests.isEmpty then [] else [s!"attests: {String.intercalate ", " s.attests.toList}"])
  if parts.isEmpty then "erases (emission-only)"
  else String.intercalate "; " parts

/-! ## `#kind_boundary_audit` -/

open Elab Command in
/-- `#kind_boundary_audit ns …` walks every compute `def` under the given namespaces, reports
each declaration that mints or erases a registered carrier (with the kinds it mints), and marks
a boundary-active declaration that carries no tier attribute as a **violation**. One sorted
`info` message, suitable for `#guard_msgs` pinning; a new untagged interior boundary then fails
the build. Theorems and `Prop`-valued declarations are skipped — a parity statement is legitimately
*about* `.magnitude`. -/
elab "#kind_boundary_audit" nss:ident+ : command => liftTermElabM do
  let sites ← boundarySites (nss.map (·.getId))
  -- Lines are sorted *as rendered*, so the report groups by tier tag (`[carrierVocab]` <
  -- `[kindConst]` < `[kindCrossing]` < `[kindEmission]` < `[kindIngest]` < `⚠ UNTAGGED`) and
  -- only then by name.
  let mut lines : Array String := #[]
  let mut nSanctioned := 0
  let mut nViolations := 0
  for s in sites do
    let tag : String :=
      match s.tier with
      | some t => s!"[{t.label}]"
      | none   => "⚠ UNTAGGED"
    match s.tier with
    | some _ => nSanctioned := nSanctioned + 1
    | none   => nViolations := nViolations + 1
    lines := lines.push s!"{tag} {s.decl} — {s.description}"
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

/-! ## `#kind_boundary_clean` -/

open Elab Command in
/-- `#kind_boundary_clean ns …` — **the invariant, stated separately from the inventory.**

`#kind_boundary_audit` above logs its findings as one `info` message, which is pinned with
`#guard_msgs` so that the boundary's whole contents are reviewable in the diff. That pin is a
*record*, and a record can be re-blessed: re-pinning a message whose summary reads
`… UNTAGGED — invariant 6/7 violation` leaves the build green with the invariant dead, and
nothing about the pin itself distinguishes the two cases. The mechanism that makes the
inventory reviewable is exactly the mechanism that lets the invariant be signed away.

So this command carries no message and pins nothing: it throws when any boundary-active
declaration in scope carries no tier attribute. The audit says what the boundary IS; this says
that every one of its sites has been adjudicated. Re-blessing the first cannot silence the
second, because there is nothing here to re-bless.

Put it next to the `#guard_msgs`-pinned audit in the same module, over the same namespaces. -/
elab "#kind_boundary_clean" nss:ident+ : command => liftTermElabM do
  let sites ← boundarySites (nss.map (·.getId))
  let untagged := sites.filter (fun s => s.tier.isNone)
  unless untagged.isEmpty do
    let rendered :=
      (untagged.map (fun s => s!"  ⚠ {s.decl} — {s.description}")).qsort (· < ·)
    throwError "boundary audit: {untagged.size} UNTAGGED boundary site(s) \
      — invariant 6/7 violation\n{String.intercalate "\n" rendered.toList}\n\n\
      Every declaration that mints or erases a registered carrier must carry the tier that \
      sanctions it (`@[kindCrossing]`/`@[kindIngest]`/`@[carrierVocab]`/`@[kindConst]`/\
      `@[kindEmission]`), with the reason in its docstring. Tag each site at the tier it \
      actually is — do NOT re-pin a `#kind_boundary_audit` message whose summary says \
      `violation`, which turns the build green and the invariant off."

/-! ## `#kind_mint_ratchet` -/

open Elab Command in
/-- `#kind_mint_ratchet ns …` — **the phase-2 mint discipline, stated as a gate.**

The tier attributes adjudicate at the *declaration*: one tag sanctions a whole body, and the
audit collapses a body's raw mints to a deduplicated kind list, so multiplicity is invisible —
def-level sanction can launder however many interior `⟨…⟩` a body holds. The two-column split
(`mints:` raw / `attests:` reviewed) makes the raw column *visible*; this command makes it
**empty** where the calculus claims to be authored:

* `[kindCrossing]`/`[carrierVocab]`: a raw `⟨…⟩` here is a violation. Every mint must be a
  *licensed derivation* (`castCarrier`, `Quantity.get!`, a `mul`/`div` witness edge, `zero` —
  which never appear in the raw column at all) or a `Quantity.attest why m` whose reason is
  harvested into the reviewed column. What the gate buys: at these tiers the raw column stays
  empty, so a new anonymous mint *fails the build* instead of joining a list nobody re-reads.
* `[kindConst]`/`[kindIngest]` keep raw `⟨…⟩` legal at the def granularity — a declared
  constant's value **is** the data (the docstring carries the adjudication), and an ingest
  mint is sanctioned by the check it discharges.
* `[kindEmission]` likewise stays at def granularity: an emission body's residual mints are
  the deployment boundary's own re-entries, adjudicated by the tier tag; ratcheting them is a
  per-repo campaign, and a repo that has cleared its emission tail can state so by keeping
  those bodies mint-free — this gate will not regress the tiers it covers either way.

Like `#kind_boundary_clean`, this carries no message and pins nothing: it throws, so there is
nothing to re-bless. Put it beside the pinned audit, over the same namespaces. -/
elab "#kind_mint_ratchet" nss:ident+ : command => liftTermElabM do
  let sites ← boundarySites (nss.map (·.getId))
  let offending := sites.filter fun s =>
    (s.tier == some .kindCrossing || s.tier == some .carrierVocab) && !s.mints.isEmpty
  unless offending.isEmpty do
    let rendered :=
      (offending.map (fun s =>
        let tag := match s.tier with | some t => t.label | none => "?"
        s!"  ⚠ [{tag}] {s.decl} — {s.description}")).qsort (· < ·)
    let body := String.intercalate "\n" rendered.toList
    throwError "mint ratchet: {offending.size} `[kindCrossing]`/`[carrierVocab]` site(s) \
      with raw mints\n{body}\n\n\
      At these tiers every mint must be a licensed derivation (`castCarrier`, \
      `Quantity.get!`, a witness edge) or a `Quantity.attest why m` whose reason is \
      harvested — a raw `⟨…⟩` is an anonymous claim the reviewed column never sees."

/-! ## `#kind_crossings` -/

open Elab Command in
/-- `#kind_crossings [ns …]` enumerates the tagged boundary registry — every
`@[kindCrossing]`/`@[kindIngest]`/`@[carrierVocab]`/`@[kindConst]`/`@[kindEmission]` site with
the first line of its docstring — grouped by tier and sorted, optionally filtered to the given
namespaces. The invariant-5-style enumeration for boundaries: a reviewer reads the sanctioned
sites the way `#kind_edges` reads the sanctioned edges. -/
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
