/-
# Mereology — the carving, as pure structure

The part–whole vocabulary of the calculus, with no imports: a carving knows nothing about
values, kinds, or carriers, and the modules that read one (`Extensivity.lean`,
`Recarving.lean`, `Composite.lean`) import this one rather than housing it. The blueprint's
foundations chapter documents this vocabulary; the extensivity chapter documents the laws
over it.

A `Decomposition` is a **carving**, and deliberately not a census: nothing here fixes how
many parts a system has, and every law over carvings is quantified over all of them rather
than stated for one. That is Marmodoro's point about physical structure — it unites without
bringing a count principle, so "[i]t is an open question how many entities a physical
structure is" (*Whole, but not One*, 2018, §3) — and it is Dybkær's own reading of a
system's structure: ⟨system⟩ was adopted "to accommodate any partition into components"
(§3.2), and "the extent and structure of a system is essentially defined by the observer
for some purpose" (§3.3 Note 5). What a carving cannot supply is the *whole*; that arrives
with a sort of system and the license to aggregate at it (`Composite.lean`).
-/

module

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus

universe u

/-- A **decomposition** of a system into parts (Dybkær §3.3's demarcated arrangement, the
carving of the foundations chapter): an atomic part, or the union of two sub-carvings. The
leaves are the atomic parts; each node stands for the whole they compose. Disjointness and
exhaustiveness of the parts are the model's reading, not the type's claim — which is what
lets the laws quantify over all carvings and lets the refutations (`Recarving.lean`) build
the carvings a census would forbid.

Parameterized over the **part type** `O` for the reason `IndividualQuantity` is
parameterized over its object type: the mereology of a host library's own objects — the
particles of a mechanical system, the cells of a mesh — is the same mereology, and
nothing here reads a part except to hand it to the measurement. `Decomposition System`
is the nominal reading and the one the mixing counterexample (`Extensivity.lean`) uses. -/
inductive Decomposition (O : Type u) where
  /-- An atomic, indivisible part. -/
  | atom : O → Decomposition O
  /-- The union of two parts. -/
  | union : Decomposition O → Decomposition O → Decomposition O
deriving Repr

/-- **The fold over a decomposition**: a value per leaf, combined at every union. The one
recursion this module has over the mereology, so `leafSum` (`Extensivity.lean`) and the
quantity-level `assemble` (`Composite.lean`) are the *same* traversal at two carriers
rather than two traversals that happen to agree. -/
def Decomposition.fold {O : Type u} {R : Type} (leaf : O → R) (op : R → R → R) :
    Decomposition O → R
  | .atom s => leaf s
  | .union a b => op (Decomposition.fold leaf op a) (Decomposition.fold leaf op b)

/-- **A decomposition from a nonempty list of parts** — the head and the rest, so
nonemptiness is in the signature rather than a side condition. The shape a host library
hands over (a `List`, a `Multiset`'s elements, a `Fintype`'s enumeration) reaching the
mereology without an empty case to invent a value for. -/
def Decomposition.ofParts {O : Type u} (p : O) (ps : List O) : Decomposition O :=
  ps.foldl (fun d q => .union d (.atom q)) (.atom p)

/-- **The number of joins of a carving** — its `union` nodes. The one number this module reads
off the *shape* of a decomposition rather than off a measured value, and it is read for two
reasons: it bounds how far a per-join tolerance can accumulate (§13.5.2, `Uncertainty.QuasiExtensive`),
and it is precisely what a re-carving is free to change while the whole stays put
(`Recarving.lean`). -/
def Decomposition.joins {O : Type u} : Decomposition O → Nat
  | .atom _ => 0
  | .union a b => Decomposition.joins a + Decomposition.joins b + 1

/-- **A property of every atomic part of a carving.** The leaf-wise quantifier the intensive
law needs: `Extensive` reaches its leaves through arithmetic (`leafSum`), and intensivity
has no arithmetic to reach them with. -/
def Decomposition.Forall {O : Type u} (p : O → Prop) : Decomposition O → Prop
  | .atom s => p s
  | .union a b => Decomposition.Forall p a ∧ Decomposition.Forall p b

/-- **A count over a carving**: how many atomic parts fall under a sortal predicate. The
predicate is the argument that makes this a count *of* something — "a count of a specified
elementary entity", in the SI's phrasing of amount of substance. -/
def Decomposition.count {O : Type u} (p : O → Bool) : Decomposition O → Int :=
  Decomposition.fold (fun s => if p s then 1 else 0) (· + ·)

/-- **The count and the join count are the same number.** A carving with `n` joins exhibits
`n + 1` parts, so "how many entities" is a fact about the tree and about nothing else. -/
theorem count_true_eq_joins_succ {O : Type u} (d : Decomposition O) :
    Decomposition.count (fun _ => true) d = (d.joins : Int) + 1 := by
  induction d with
  | atom _ => rfl
  | union a b ha hb =>
      show Decomposition.count (fun _ => true) a + Decomposition.count (fun _ => true) b = _
      rw [ha, hb]
      show _ = ((a.joins + b.joins + 1 : Nat) : Int) + 1
      push_cast
      omega

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
