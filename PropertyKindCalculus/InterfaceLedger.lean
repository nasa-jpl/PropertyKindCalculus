/-
# The interface ledger — what parts exert across a carving's cuts

`Extensivity.lean` classifies kinds by what a value does under composition, and every one of
its measurements reads a *node* of a carving. This module is about the quantities that read no
node at all: what one part exerts on another — a drive torque on a hub, a contact force at a
joint, the heat crossing a wall — is indexed by an ordered *pair* of parts, an interface, and
`Measurement O` has no slot for a pair. The ledger is that missing slot, and its one law is
the reason such quantities nonetheless aggregate: the two readings of one interface cancel,
`act p q + act q p = 0` — for mechanical actions, Newton's third law, carried once as a field
rather than assumed system by system.

Two statements answer each other, in the pattern of `Recarving.lean`'s two halves:

  * **The exact price of additivity** (`netTotal_union`, no law in scope): summing per-part
    nets over a union overshoots the two halves' own totals by exactly the uncancelled
    cross-flow over the cut. The identity holds for *any* pairwise action, so a ledger that
    drops a reaction does not fail additivity vaguely — it fails it by this number.
  * **The rollup** (`InterfaceLedger.netTotal_eq_extTotal`, law in scope): under antisymmetry
    the price is zero at every cut, so the sum of per-part nets is the exogenous total alone —
    the interior ledger vanishes from the whole while remaining real part by part.
    `netMeasurement_extensive` restates this against `Extensive`: the net *is* additive, but
    where mass's additivity is the model's free choice, this one is purchased by the
    cancellation law. One predicate, two different licenses — the sense in which the scope of
    extensivity is kind-specific.

What a re-carving does to a ledger sharpens `Recarving.lean`'s count story. A count at least
exists on every carving; an interface does not survive the merge of its two ends — both ends
of a drive torque land on one part, and `act_self` (forced by the law, not by bookkeeping)
reads the merged entry as zero. Internal-versus-external is thereby the carving's fact rather
than the system's, which is Dybkær's observer clause (§3.3 Note 5) with a proof attached; the
worked witness, coarsening included, is `RoverExtensivity.lean` (examples).

One caution the formalization makes explicit: the ledger carries *one* signed component per
interface, and cancellation is stated for that component. Reading it as torque about a shared
point requires the pair's torques to cancel — the strong (central-force) form of the third
law — which is a modeling obligation the `antisymm` field states rather than discharges.
-/

module

public import PropertyKindCalculus.Extensivity
-- Private scope only: the proofs below reduce through bodies sealed in `PropertyKindCalculus.Mereology`; `import all`
-- gives this module the reduction without exposing them to every consumer.
import all PropertyKindCalculus.Extensivity

public section -- pkc-blanket

namespace PropertyKindCalculus

universe u

/-! ## The raw layer — a pairwise action, and what summing it costs

Stated for an arbitrary `act : O → O → Int` first, because the price identity is sharpest
with no law in scope: it is the identity a violated law is *measured* against. -/

/-- **The fold is linear in the leaf function** — the one arithmetic fact every statement
below routes through. -/
theorem partTotal_add_fun {O : Type u} (f g : O → Int) :
    ∀ d : Decomposition O,
      partTotal (fun p => f p + g p) d = partTotal f d + partTotal g d
  | .atom _ => rfl
  | .union a b => by
      show partTotal (fun p => f p + g p) a + partTotal (fun p => f p + g p) b
        = (partTotal f a + partTotal f b) + (partTotal g a + partTotal g b)
      rw [partTotal_add_fun f g a, partTotal_add_fun f g b]
      omega

/-- **What a carving exerts on one part**: the total of `act · p` over the leaves of `d`. -/
def actionOn {O : Type u} (act : O → O → Int) (d : Decomposition O) (p : O) : Int :=
  partTotal (fun q => act q p) d

/-- **What one carving exerts on another, in total** — the flow across the cut between them:
every `a`-leaf-to-`b`-leaf entry, read once. -/
def mutualTotal {O : Type u} (act : O → O → Int) (a b : Decomposition O) : Int :=
  partTotal (actionOn act a) b

/-- **The net on one part, as carved by `d`**: its exogenous contribution `ext p` plus
everything `d`'s parts exert on it. "Exogenous" is relative to the ledger, not to the world:
whatever is not carried as an interface is carried here. -/
def netOn {O : Type u} (act : O → O → Int) (ext : O → Int) (d : Decomposition O)
    (p : O) : Int :=
  ext p + actionOn act d p

/-- **The rollup total**: the per-part nets, summed over the same carving that defined
them. -/
def netTotal {O : Type u} (act : O → O → Int) (ext : O → Int) (d : Decomposition O) : Int :=
  partTotal (netOn act ext d) d

/-- `mutualTotal` splits on the left the way it splits (definitionally) on the right. -/
theorem mutualTotal_union_left {O : Type u} (act : O → O → Int)
    (a₁ a₂ b : Decomposition O) :
    mutualTotal act (.union a₁ a₂) b = mutualTotal act a₁ b + mutualTotal act a₂ b :=
  partTotal_add_fun (actionOn act a₁) (actionOn act a₂) b

/-- Summing per-part nets taken against `d₀` splits into the exogenous total and the flow
from `d₀` — the bridge every statement below rests on. -/
theorem partTotal_netOn {O : Type u} (act : O → O → Int) (ext : O → Int)
    (d₀ d : Decomposition O) :
    partTotal (netOn act ext d₀) d = partTotal ext d + mutualTotal act d₀ d :=
  partTotal_add_fun ext (actionOn act d₀) d

/-- **The exact price of additivity** — for *any* pairwise action, lawful or not. Rolling up
per-part nets over a union overshoots the two halves' own rollups by precisely the two
cross-flows over the cut. Everything the antisymmetric layer proves is this identity with the
price argued to zero; everything a lawless table gets wrong is this identity with the price
left standing. -/
theorem netTotal_union {O : Type u} (act : O → O → Int) (ext : O → Int)
    (a b : Decomposition O) :
    netTotal act ext (.union a b)
      = (netTotal act ext a + netTotal act ext b)
        + (mutualTotal act a b + mutualTotal act b a) := by
  have hUa := partTotal_netOn act ext (.union a b) a
  have hUb := partTotal_netOn act ext (.union a b) b
  have hla := mutualTotal_union_left act a b a
  have hlb := mutualTotal_union_left act a b b
  have haa := partTotal_netOn act ext a a
  have hbb := partTotal_netOn act ext b b
  show partTotal (netOn act ext (.union a b)) a + partTotal (netOn act ext (.union a b)) b
    = (partTotal (netOn act ext a) a + partTotal (netOn act ext b) b)
      + (mutualTotal act a b + mutualTotal act b a)
  omega

/-! ## The ledger — the law that makes the price zero -/

/-- **An interface ledger**: a pairwise action between parts, carrying its cancellation law
as a field — for mechanical actions, Newton's third law. A pair of readings that does not
cancel is not two readings of one interface and should not be a term of this type; the
obligation is a field for the reason `Recarving.preserves` is. A ledger is conveniently
*entered* one direction at a time: `fun p q => raw p q - raw q p` antisymmetrizes any raw
table, and its law is `omega`. -/
structure InterfaceLedger (O : Type u) where
  /-- What `p` exerts on `q` — signed, one fixed component of the action. -/
  act : O → O → Int
  /-- **The cancellation law**: the two readings of one interface sum to zero. -/
  antisymm : ∀ p q, act p q + act q p = 0

namespace InterfaceLedger

variable {O : Type u}

/-- **A self-interface reads zero — forced, not conventional**: `act p p = −act p p` leaves
only zero. This is the atom of the erasure story: a carving that merges the two ends of an
interface into one part hands both ends one name, and the law itself annihilates the entry —
which is why an interior torque is not recoverable from any carving that does not separate
its ends. -/
theorem act_self (L : InterfaceLedger O) (p : O) : L.act p p = 0 := by
  have h := L.antisymm p p
  omega

/-- What one part exerts on a carving and what the carving exerts back cancel, leaf by
leaf. -/
theorem actionOn_pair_cancel (L : InterfaceLedger O) (p : O) :
    ∀ d : Decomposition O, partTotal (fun q => L.act p q) d + actionOn L.act d p = 0
  | .atom r => L.antisymm p r
  | .union a b => by
      have ha := L.actionOn_pair_cancel p a
      have hb := L.actionOn_pair_cancel p b
      show (partTotal (fun q => L.act p q) a + partTotal (fun q => L.act p q) b)
          + (actionOn L.act a p + actionOn L.act b p) = 0
      omega

/-- **The two flows across any cut cancel** — the union-level form of the field: whatever `a`
exerts on `b` in total, `b` exerts back. -/
theorem mutualTotal_cancel (L : InterfaceLedger O) :
    ∀ a b : Decomposition O, mutualTotal L.act a b + mutualTotal L.act b a = 0
  | .atom p, b => L.actionOn_pair_cancel p b
  | .union a₁ a₂, b => by
      have h₁ := L.mutualTotal_cancel a₁ b
      have h₂ := L.mutualTotal_cancel a₂ b
      have hl := mutualTotal_union_left L.act a₁ a₂ b
      have hr : mutualTotal L.act b (.union a₁ a₂)
          = mutualTotal L.act b a₁ + mutualTotal L.act b a₂ := rfl
      omega

/-- The interior of one carving cancels outright: the flow of a carving into itself is
zero. -/
theorem interior_eq_zero (L : InterfaceLedger O) (d : Decomposition O) :
    mutualTotal L.act d d = 0 := by
  have h := L.mutualTotal_cancel d d
  omega

/-- **The rollup.** The sum over the parts of the per-part nets is the exogenous total alone:
every interior interface is read once in each direction, and the law cancels the pair. The
reaction a motor induces on the body is real in `netOn` — it loads a bearing — and absent
from the whole; both facts are this theorem, read at a part and at the carving. -/
theorem netTotal_eq_extTotal (L : InterfaceLedger O) (ext : O → Int)
    (d : Decomposition O) :
    netTotal L.act ext d = partTotal ext d := by
  show partTotal (netOn L.act ext d) d = partTotal ext d
  rw [partTotal_netOn L.act ext d d, L.interior_eq_zero d]
  omega

/-- The rollup as a `Measurement`, so the §13.5 vocabulary can classify it. -/
def netMeasurement (L : InterfaceLedger O) (k : KindOfProperty) (ref : String)
    (ext : O → Int) : Measurement O := fun d =>
  { kind := k, numeral := netTotal L.act ext d, reference := ref }

/-- **Additivity, purchased.** The net over a ledger is extensive — but where mass's
`additive` field is the model's free choice, this one is a theorem with a hypothesis: delete
the `antisymm` field and `netTotal_union` prices exactly what remains. One predicate,
`Extensive`, two different licenses — which is what makes the scope of extensivity
kind-specific rather than a single yes-or-no. -/
theorem netMeasurement_extensive (L : InterfaceLedger O) (k : KindOfProperty) (ref : String)
    (ext : O → Int) : Extensive k (L.netMeasurement k ref ext) := by
  refine ⟨fun _ => rfl, fun a b => ?_⟩
  show netTotal L.act ext (.union a b) = netTotal L.act ext a + netTotal L.act ext b
  rw [L.netTotal_eq_extTotal ext (.union a b), L.netTotal_eq_extTotal ext a,
    L.netTotal_eq_extTotal ext b]
  rfl

end InterfaceLedger

end PropertyKindCalculus

end -- pkc-blanket
