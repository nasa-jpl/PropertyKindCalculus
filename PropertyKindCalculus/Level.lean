/-
# Level quantities — a logarithmic presentation of a ratio kind, not a fifth scale type

The decibel question (ISO 80000-8's sound pressure level, IEC 60027-3's dB, EM's dBm) is
where a metrology layer either grows a new scale type or recognizes a construction. This
module takes the second road, for reasons surveyed against both the literature and
PhysLib's own architecture:

  * **Stevens/Dybkær.** `ScaleType` is Dybkær Ch. 12's four types verbatim, with a linear
    rank and a proved monotonicity theorem. A level is Stevens' log-interval type — but its
    operational content in this calculus is not a new comparability structure: it is a
    *nonlinear chart* on an existing ratio-scale kind, anchored at a conventional
    reference. The root kind keeps its scale; the presentation changes.
  * **The gate profile is a torsor, not a scale.** What acoustics licenses: ordering
    levels; *level differences* — which land in a **different kind** (a gain, in dB, where
    the reference cancels); shifting a level by a gain (an amplifier); and the energetic
    combination. What it forbids: `L₁ + L₂`. Difference-allowed-but-heterogeneous,
    sum-forbidden is exactly position/extent — levels are *positions* on a logarithmic
    axis and gains are its *extents* — so the licensed operations are the torsor pair
    `sub`/`shift` below, and the level kind itself is **ordinal as a kind**: its only
    *same-kind* operation is order. `DifferenceKind lk.toKind` is unprovable, so the
    certified `Quantity.add` is structurally unavailable at a level kind — the compile
    error the domain wants — while the gain kind is ratio-scale, so gains compose by the
    ordinary certified addition (a 20 dB stage after a 20 dB stage is 40 dB).
  * **The reference is kind identity.** dBm and dBW differ *only* by reference (1 mW vs
    1 W) and are not interchangeable; SPL is "re 20 µPa" by convention. So the reference
    names part of the kind (`LevelKind.ref`), two level kinds with different references
    are distinct kinds, and — because differences cancel the reference —
    `gainKind_ref_irrelevant` proves the gain kind does not depend on it.
  * **Root-power vs power is kind information.** ISO 80000-1 distinguishes root-power
    quantities (pressure, field strength — `20·lg`) from power quantities (intensity,
    power — `10·lg`). Which factor applies is determined by the *kind*, not the number:
    the same dB figure means a ×10 field ratio or a ×10 power ratio depending on the role,
    which is `PowerRole` below. The energetic combination, by contrast, is
    role-*independent* — incoherent sources add in power, and `10^(L/10)` is the power
    ratio of *any* level (that is what the 20 buys) — so `combineEnergetic` uses 10 for
    both roles, and 94 dB ⊕ 94 dB ≈ 97 dB whether the level is a field or a power level.
  * **Why the kind layer, and not the unit layer.** PhysLib's units are, by construction,
    translationally-invariant metrics on a quantity manifold — a pure `ℝ>0` scaling action
    (`UnitDependent.scaleUnit`); even the affine °C is inexpressible there, and a
    logarithmic chart with a reference is two steps further out. A level therefore cannot
    be delegated to a unit system of that shape; it lives here, beside the kind. This is
    the R13 groundwork: the decibel as the nonlinear extreme of the scale-spanning-unit
    family whose linear member is the kelvin.

The numeric boundary — actually taking `lg` — is carrier business (`LogCarrier` below):
`Float` realizes it computably in this module; a lawful carrier realizes it wherever its
mathematics lives. The kind-level structure (`toKind`, `gainKind`, `sub`, `shift`, the
certificates) is carrier-generic and needs no logarithm at all: the torsor is exact.

Deferred, deliberately: the neper (base e, factor 1 — a second chart on the same root;
add a base field when the first consumer lands) and the cross-role comparability of gains
(a field gain and a power gain of one device agree in dB by design; when needed, that is
an application-registered `Specializes`/`KindJoin` family over a general gain kind — the
lattice machinery, not new level machinery).
-/

module

public import PropertyKindCalculus.Quantity

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus

/-! ## The kind-level structure -/

/-- **ISO 80000-1's dichotomy of level-bearing quantities.** A *power* quantity (power,
intensity, energy density) takes `10·lg`; a *root-power* quantity (pressure, voltage,
field strength — anything whose square is proportional to power) takes `20·lg`, exactly so
that `10^(L/10)` is the associated **power** ratio for both. Which applies is a fact about
the root kind's physics, carried here as data. -/
inductive PowerRole
  /-- A power quantity: `L = 10·lg(x/x₀)`. -/
  | power
  /-- A root-power quantity: `L = 20·lg(x/x₀)`, so the *power* ratio is still `10^(L/10)`. -/
  | rootPower
deriving DecidableEq, Repr

/-- The level factor: 10 for a power quantity, 20 for a root-power quantity. -/
def PowerRole.factor : PowerRole → Nat
  | .power     => 10
  | .rootPower => 20

/-- Rendered tag, used to individuate the constructed kinds. -/
def PowerRole.tag : PowerRole → String
  | .power     => "10lg"
  | .rootPower => "20lg"

/-- **A level kind, as a construction** — the logarithmic presentation of a ratio-scale
root kind against a named reference. `root` should be ratio-scale (only ratio quantities
have the ratios a logarithm takes — Dybkær §13.3.5); the claim is the author's, exactly as
`ProductKind.ofRatio`'s is. The reference is *named* here because it is kind identity
(dBm ≠ dBW); its numeric value is supplied where a level is realized (`ofRoot`), the same
place-of-use discipline every witness in this calculus follows. -/
structure LevelKind where
  /-- The ratio-scale kind the level presents (sound pressure, power, field strength). -/
  root : KindOfProperty
  /-- Power or root-power: fixes the factor (10 or 20). -/
  role : PowerRole
  /-- The conventional reference, by name: "20 µPa", "1 mW", "1 W". Part of the kind. -/
  ref : String
deriving DecidableEq, Repr

namespace LevelKind

/-- **The level kind** — *ordinal as a kind*: its only same-kind operation is order.
Differences of levels are heterogeneous (they land in `gainKind`), so `DifferenceKind` is
deliberately unprovable here and the certified `Quantity.add`/`mulK` are unavailable —
`L₁ + L₂` and `L₁ × L₂` are the domain errors this construction exists to reject. The
defining chart is recorded as the examination principle: kinds are individuated by *how
they are examined*, and a level is examined by taking the chart. -/
def toKind (lk : LevelKind) : KindOfProperty :=
  { id := "level[" ++ lk.role.tag ++ "] of " ++ lk.root.id ++ " re " ++ lk.ref
    scale := .ordinal
    examPrinciple := some (lk.role.tag ++ "(" ++ lk.root.id ++ " / " ++ lk.ref ++ ")") }

/-- **The gain kind** — the *extent* of the level axis: what a difference of levels is,
and what an amplifier contributes. Ratio-scale: 0 dB is the canonical identity, gains
compose by the ordinary certified addition, and attenuation is negation at a signed
carrier. Note what is absent: `ref`. The reference cancels in every difference, and
`gainKind_ref_irrelevant` below makes that a theorem rather than a remark. -/
def gainKind (lk : LevelKind) : KindOfProperty :=
  { id := "gain[" ++ lk.role.tag ++ "] of " ++ lk.root.id
    scale := .ratio
    examPrinciple := some ("difference of level[" ++ lk.role.tag ++ "] of " ++ lk.root.id) }

/-! ### The gate profile, as theorems -/

/-- A level kind allows order — the one same-kind operation the domain licenses. -/
theorem toKind_allowsOrder (lk : LevelKind) : lk.toKind.scale.AllowsOrder := trivial

/-- A level kind allows no same-kind differences: `DifferenceKind lk.toKind` is
unprovable, so the certified addition is structurally unavailable at a level kind. -/
theorem toKind_not_allowsDifference (lk : LevelKind) :
    ¬ lk.toKind.scale.AllowsDifference := fun h => h

/-- A level kind is not ratio-scale: no certified product or quotient forms at it. -/
theorem toKind_not_isRational (lk : LevelKind) : ¬ lk.toKind.IsRational :=
  fun h => nomatch h

/-- The gain kind is ratio-scale: gains compose by the certified addition. -/
theorem gainKind_isRational (lk : LevelKind) : lk.gainKind.IsRational := rfl

/-- **The reference cancels in differences** — the gain kind does not depend on `ref`, by
construction: two level kinds differing only in reference share their gain kind. -/
theorem gainKind_ref_irrelevant (root : KindOfProperty) (role : PowerRole)
    (ref₁ ref₂ : String) :
    (LevelKind.mk root role ref₁).gainKind = (LevelKind.mk root role ref₂).gainKind := rfl

/-! ## The torsor — the licensed heterogeneous operations

Levels are positions on the logarithmic axis, gains its extents. The two operations below
are the *whole* additive vocabulary of a level; both are heterogeneous, which is why
neither is a `ScaleType` question. -/

variable {R : Type} {lk : LevelKind}

/-- **The difference of two levels is a gain** — `L₁ − L₂` lands in `gainKind`, never in
the level kind: the reference cancels, and what remains is `f·lg(x₁/x₂)`. This is the
torsor difference, and the only subtraction a level has. -/
def sub [Sub R] (lk : LevelKind) (x y : Quantity lk.toKind R) : Quantity lk.gainKind R :=
  ⟨x.magnitude - y.magnitude⟩

/-- **Shifting a level by a gain is a level** — what an amplifier does. The torsor
action, and the only addition a level participates in. -/
def shift [Carrier R] (lk : LevelKind) (x : Quantity lk.toKind R)
    (g : Quantity lk.gainKind R) : Quantity lk.toKind R :=
  ⟨Carrier.add x.magnitude g.magnitude⟩

@[simp] theorem sub_magnitude [Sub R] (x y : Quantity lk.toKind R) :
    (lk.sub x y).magnitude = x.magnitude - y.magnitude := rfl

@[simp] theorem shift_magnitude [Carrier R] (x : Quantity lk.toKind R)
    (g : Quantity lk.gainKind R) :
    (lk.shift x g).magnitude = Carrier.add x.magnitude g.magnitude := rfl

/-- **The certificate.** `g` is the gain from `y` up to `x`: its magnitude is the
difference of theirs. Separate `Prop`, carried when needed — uniform with
`Quantity.IsProduct` and `Quantity.IsWidening`. -/
def IsGainOf [Sub R] (lk : LevelKind) (g : Quantity lk.gainKind R)
    (x y : Quantity lk.toKind R) : Prop :=
  g.magnitude = x.magnitude - y.magnitude

/-- The torsor difference satisfies the certificate by construction. -/
theorem sub_isGainOf [Sub R] (x y : Quantity lk.toKind R) :
    lk.IsGainOf (lk.sub x y) x y := rfl

end LevelKind

/-! ## The numeric boundary — `LogCarrier`

The torsor above is exact and carrier-generic. Taking the chart itself — `lg`, and its
inverse — is carrier business, bundled the way `Carrier` bundles additivity: `Float`
realizes it computably below; a lawful carrier realizes it wherever its mathematics lives
(for `ℝ`, in the Mathlib-backed layers, with the algebraic laws stated there). -/

/-- The operations a carrier needs to realize a level numerically: the base-10 chart in
both directions, and the embedding of the small natural factors (10, 20). Laws are
deliberately not bundled here, exactly as `Carrier` carries no laws: `Float` must be an
instance, and `Float.log10` obeys no exact algebra. -/
class LogCarrier (R : Type) extends Carrier R where
  /-- `10^x`. -/
  exp10 : R → R
  /-- `lg x`. -/
  log10 : R → R
  /-- Embed a natural factor (the level factors 10 and 20). -/
  ofNat : Nat → R

/-- `Float` realizes the chart computably — the executable carrier for level arithmetic,
with IEEE semantics and no exact laws, as for `Carrier Float`. -/
instance : LogCarrier Float where
  exp10 x := Float.pow 10.0 x
  log10 := Float.log10
  ofNat := Nat.toFloat

namespace LevelKind

variable {R : Type} {lk : LevelKind}

/-- **Realize a level from its root quantity** — the chart, taken at the point of use:
`L = f·lg(x/ref)`, with the reference's *numeric value* supplied here, at the same kind as
`x`. The kind pinned the reference's identity; the call site supplies its magnitude — the
witness-where-used discipline, at the numeric boundary. -/
def ofRoot [LogCarrier R] [Mul R] [Div R] (lk : LevelKind)
    (ref x : Quantity lk.root R) : Quantity lk.toKind R :=
  ⟨LogCarrier.ofNat lk.role.factor * LogCarrier.log10 (x.magnitude / ref.magnitude)⟩

/-- **The power ratio of a level** — `10^(L/10)`, *role-independent*: for a root-power
level the 20 in the chart is exactly what makes `L/10` the power exponent. This is the
quantity the energetic combination adds. -/
def powerRatio [LogCarrier R] [Div R] (lk : LevelKind)
    (x : Quantity lk.toKind R) : R :=
  LogCarrier.exp10 (x.magnitude / LogCarrier.ofNat 10)

/-- **The energetic combination** — the domain's real "sum" of two levels: incoherent
sources add in *power*, so `L = 10·lg(10^(L₁/10) + 10^(L₂/10))`, for **both** roles
(`powerRatio` is role-independent). Two equal sources sit ≈3 dB above one, never double:
94 dB ⊕ 94 dB ≈ 97 dB. This licensed combinator, next to the unprovability of
`DifferenceKind` at the level kind, is the whole point: `+` is forbidden *and* the
legitimate combination is provided, so rejecting the error costs no expressiveness. -/
def combineEnergetic [LogCarrier R] [Mul R] [Div R] (lk : LevelKind)
    (x y : Quantity lk.toKind R) : Quantity lk.toKind R :=
  ⟨LogCarrier.ofNat 10 *
    LogCarrier.log10 (Carrier.add (lk.powerRatio x) (lk.powerRatio y))⟩

end LevelKind

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
