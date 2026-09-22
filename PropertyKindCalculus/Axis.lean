/-
# Axis — extent and position as roles on one kind

An axis kind (a table's row axis, a tile's row/column axis, a reduction grid's) is a
*role*, not a measurand: kinding it is what turns "nothing about a bare `Nat` stops a
height and a row index from being swapped at a call site" into a type error. But one axis
kind serves three readings at once — how far the axis runs (an **extent**), where on it a
value sits (a **position**), and how far along it a value moves (a displacement, at a
signed carrier) — so the kind split that separates *different* axes leaves the roles
*within* one axis undistinguished. `f (n i : Quantity rowAxis Nat)` type-checks with its
arguments the wrong way round, exactly as `Icc hi lo` does for a pair of naked endpoints.

This module fixes that the way `Bounds` fixes the endpoint swap: by putting the role into
the type.

  * `Extent k R` / `Position k R` — one-field role wrappers over `Quantity k R`, the
    extent/position counterparts of `LowerBound`/`UpperBound`. Their field is `q` in both,
    as it is in every role wrapper here: a role is a wrapper *around* a quantity, and the
    projection is spelled the same way wherever one is opened.
  * The relation between them is **directional-only**: `Position.Within` ("this position
    lies on that axis") is the sole former, and because its two arguments have different
    types there is no way to write it with the extent in the position's slot. A count
    handed to a position argument is a type error, not a plausible number.
  * An axis that is a **loop** is an extent too, and `Extent.iterate` is its
    position-blind walk: a trip count carried at the loop's own kind, so one loop's budget
    cannot be handed to another. `positions` is the same walk where the index is read.

**Roles, not new kinds.** The alternative — one kind for the extent and another for the
position — was rejected on two counts. It doubles the pairwise-distinctness obligation
that every axis vocabulary discharges (a kind is certified apart from every other kind it
could be confused with, and splitting each axis in two squares the matrix for no new
confusion), and it breaks the representation-parametric bridge an axis relies on, where
the *same* kind carries the extent at `Nat` and a displacement at `Int`
(`Quantity.castCarrier`). `Bounds` faced the identical fork for lower/upper and chose the
wrapper; a role is not a kind, and neither an upper bound on lengths nor a position on a
row axis is a new property to be measured.

**The convention is half-open, because indexing is.** `Position.Within` is `i < n` — the
0-based reading `[0:n]` loops and array indexing already have. `Extent.span?` offers the
same set closed, as `[0, n−1]`, so the interval vocabulary (`IccQ.Mem`, `IccQ.memb`)
applies verbatim; `within_iff_mem_span` is the proof that the two readings agree, and it
is the sense in which "the range obligation" is *derived from* the extent rather than
spelled out beside it.

**An empty axis has no positions**, and this module says so rather than fabricating one:
`lastPos?`, `posOf?`, `clampPos?` and `span?` return `Option`, `positions` is empty, and
the `ForIn` instance runs zero iterations. This is `QuantityVector`'s rule about default
magnitudes, one level up — a position on an axis with no positions would be a fabricated
index the way a default scalar would be a fabricated magnitude.

**Where the obligation is discharged.** `Extent.posOf?` is the gate: a raw `Nat` becomes a
`Position` only by being checked against the extent that bounds it (`posOf?_within` is that
check, kept as a theorem). `Extent.positions` and the `ForIn` instance are the same
guarantee without a check, by construction — every position they yield is `Within` the
extent it came from, so a loop over an axis cannot leave it. That is `CertifiedIngest`'s
discipline applied to index space: evidence is discharged where the value is born, and
downstream code consumes a plain role-typed value.

**What this module deliberately does not provide** is a dependent index — a
`{i : Nat // i < n}` carried through the kernels. Three reasons, none of them ergonomic.
The obligation is not, at most sites, a safety property: a node formula evaluated off the
end of its axis extrapolates, it does not read foreign memory. The sites that *do* index
memory reach it through the documented `.magnitude`/`GetElem` erasure boundary, which is
where the deployment carriers (a recorded tape, a device kernel, a texture fetch) take
over and cannot carry a proof across. And the calculus's own ingest doctrine is
gate-and-drop: threading evidence through every consumer is interval analysis, a separate
discipline from kind tracking. A range fact that must be a theorem belongs in the analysis
layer, over a lawful carrier, where it is already at home.
-/

module

public import PropertyKindCalculus.Bounds

public section -- pkc-blanket

namespace PropertyKindCalculus

/-- **An axis extent, as a role** — how far the axis runs, measured at the axis's own
kind: a table's row count, a tile's height, a probe grid's size. Distinct in *type* from a
position on the same axis, which is what stops the two from being swapped at a call site;
the only relation between them is `Position.Within`, and it takes the extent on the right.
Carrier-generic, as `LowerBound` is: an extent is a `Nat` count on a discrete axis and a
`Float` span on the continuous reading of the same axis. -/
structure Extent (k : KindOfProperty) (R : Type) where
  /-- The extent quantity. -/
  q : Quantity k R

/-- **An axis position, as a role** — where on the axis a value sits: a walk index, a
fetch row, a resampling node, a clamped grid coordinate. The dual of `Extent`, and its
own type for the same reason `LowerBound` is not `UpperBound`: the pair is exactly what a
call site can get backwards. -/
structure Position (k : KindOfProperty) (R : Type) where
  /-- The position quantity. -/
  q : Quantity k R

namespace Position

variable {k : KindOfProperty} {R : Type}

/-- **A role survives a representation cast** — the counterpart of `Quantity.castCarrier`
for this role, and what makes the carrier-parametric reading of an axis usable: a fetch row
narrowed from a continuous coordinate, or a discrete index read back at `Float` for the
arithmetic that spaces it, is the same position on the same axis. -/
@[expose] def castCarrier {S : Type} (f : R → S) (i : Position k R) : Position k S :=
  ⟨i.q.castCarrier f⟩

@[simp] theorem castCarrier_magnitude {S : Type} (f : R → S) (i : Position k R) :
    (i.castCarrier f).q.magnitude = f i.q.magnitude := rfl

/-- **The directional Prop former**: this position lies on the axis of that extent —
`i < n`, the half-open reading indexing already uses. It is the *only* relation statable
between the two roles, and the extent can only appear on the right of it: there is no
former putting a count where a position goes, so the swap this module exists to exclude
is unwritable rather than unlikely. -/
def Within [LT R] (i : Position k R) (n : Extent k R) : Prop :=
  i.q.magnitude < n.q.magnitude

/-- **Executable membership on the axis** — the `Bool` counterpart of `Within`, gated on
the carrier having decidable order (host scalars have it; batched deployment carriers do
not, so the branch-free law of `Bounds` survives here by the same instance absence). -/
def within [LT R] [∀ x y : R, Decidable (x < y)] (i : Position k R) (n : Extent k R) :
    Bool :=
  decide (i.q.magnitude < n.q.magnitude)

@[simp] theorem within_eq_true [LT R] [∀ x y : R, Decidable (x < y)]
    (i : Position k R) (n : Extent k R) : i.within n = true ↔ i.Within n := by
  simp [within, Within]

end Position

namespace Extent

variable {k : KindOfProperty}

/-- **A role survives a representation cast** — `Position.castCarrier`'s dual. This is the
bridge the module's own argument for roles-over-kinds rests on: one axis kind carries the
extent as a `Nat` count and the same axis continuously, and a per-role *kind* would have
had to duplicate itself along the carrier as well. -/
@[expose] def castCarrier {R S : Type} (f : R → S) (n : Extent k R) : Extent k S :=
  ⟨n.q.castCarrier f⟩

@[simp] theorem castCarrier_magnitude {R S : Type} (f : R → S) (n : Extent k R) :
    (n.castCarrier f).q.magnitude = f n.q.magnitude := rfl

/-- **Has the axis no positions at all?** The one degenerate case this vocabulary carries,
and the reason the position-producing operations below return `Option`. -/
def isEmpty (n : Extent k Nat) : Bool :=
  n.q.magnitude == 0

/-- **The last position on the axis** — `n − 1`, and `none` when the axis is empty: an
axis with no positions has no last one, and returning `0` there would be an index
fabricated out of an absence. -/
def lastPos? (n : Extent k Nat) : Option (Position k Nat) :=
  if n.q.magnitude = 0 then none else some ⟨⟨n.q.magnitude - 1⟩⟩

/-- **The gate**: a raw index becomes a `Position` only by being checked against the
extent that bounds it. This is where the range obligation is discharged — once, where the
number is born — so that every consumer downstream can take the role-typed value and ask
no further questions (`posOf?_within` is the guarantee it hands over). -/
def posOf? (n : Extent k Nat) (i : Nat) : Option (Position k Nat) :=
  if i < n.q.magnitude then some ⟨⟨i⟩⟩ else none

/-- **The clamping eliminator** — the axis counterpart of `IccQ.clamp`: an out-of-range
index is pulled onto the axis rather than rejected, which is what a fetch row or a
neighbour-of-the-last-row does. `none` on the empty axis, for `lastPos?`'s reason. -/
def clampPos? (n : Extent k Nat) (i : Nat) : Option (Position k Nat) :=
  if n.q.magnitude = 0 then none else some ⟨⟨min i (n.q.magnitude - 1)⟩⟩

/-- **Every position of the axis, materialized** — built over `Fin`, so that each element
is in range *by construction* rather than by a check that could be forgotten
(`positions_within`). Empty exactly when the axis is. -/
def positions (n : Extent k Nat) : Array (Position k Nat) :=
  Array.ofFn (n := n.q.magnitude) fun i => ⟨⟨i.val⟩⟩

/-- **The position-blind walk** — apply `f` once per position of the axis, starting from
`init`. The eliminator for an axis that is a *loop* whose body does not read its index: an
iteration budget, a fixed number of refinement sweeps, an unrolled trip count. Where the
index *is* read, `positions` (or the `ForIn` instance) hands it over role-typed instead.

Definitionally the `List.range` fold a counted loop spells out (`iterate_eq` is `rfl`), so
a budgeted body authored over the extent erases op-for-op to its naked twin — which is
what lets a kinded loop and the code generated from it be the same computation rather than
two that agree.

An extent is the right home for a budget for the reason the module exists: a naked `Nat`
trip count is exactly the argument one loop's budget can be handed to another loop, and
`Extent k Nat` at the loop's own kind makes that a type error. -/
@[inline, expose] def iterate {β : Type _} (n : Extent k Nat) (f : β → β) (init : β) : β :=
  (List.range n.q.magnitude).foldl (fun acc _ => f acc) init

@[simp] theorem iterate_eq {β : Type _} (n : Extent k Nat) (f : β → β) (init : β) :
    n.iterate f init = (List.range n.q.magnitude).foldl (fun acc _ => f acc) init := rfl

/-- **The axis as a closed interval of positions** — `[0, n−1]`, so that the interval
vocabulary applies to an axis without anyone spelling the endpoints: `IccQ.memb` is the
range test, `IccQ.Mem` the range fact, and both are *derived* from the extent, which is
what makes "`i` must lie within `n`" a statement about the one number that defines the
range rather than a pair of literals beside it. Scale-gated like every interval
(`OrderKind`, discharged by autoParam for a concrete non-nominal kind); `none` on the
empty axis, which has no closed interval of positions to offer. -/
def span? (n : Extent k Nat) (_ord : OrderKind k := by exact OrderKind.ofScale) :
    Option (IccQ k Nat) :=
  if n.q.magnitude = 0 then none else some (IccQ.of ⟨0⟩ ⟨n.q.magnitude - 1⟩ _ord)

/-! ### The guarantees — what each producer of a `Position` hands over -/

/-- **The gate's guarantee**: a position admitted by `posOf?` lies on the axis it was
checked against. -/
theorem posOf?_within {n : Extent k Nat} {i : Nat} {p : Position k Nat}
    (h : n.posOf? i = some p) : p.Within n := by
  unfold posOf? at h
  split at h
  · rename_i hlt
    cases h
    exact hlt
  · exact absurd h (by simp)

/-- The last position lies on its axis — the boundary case of the gate's guarantee. -/
theorem lastPos?_within {n : Extent k Nat} {p : Position k Nat}
    (h : n.lastPos? = some p) : p.Within n := by
  unfold lastPos? at h
  split at h
  · exact absurd h (by simp)
  · rename_i hne
    cases h
    show n.q.magnitude - 1 < n.q.magnitude
    omega

/-- A clamped index lands on the axis: the eliminator cannot produce an off-axis
position. -/
theorem clampPos?_within {n : Extent k Nat} {i : Nat} {p : Position k Nat}
    (h : n.clampPos? i = some p) : p.Within n := by
  unfold clampPos? at h
  split at h
  · exact absurd h (by simp)
  · rename_i hne
    cases h
    show min i (n.q.magnitude - 1) < n.q.magnitude
    omega

/-- **The loop's guarantee**: every position the axis enumerates is on it. A walk built
from `positions` (or from the `ForIn` instance below, which yields the same values) cannot
step off its axis, so the in-range obligation is met by construction and never restated at
a use site. -/
theorem positions_within {n : Extent k Nat} {i : Nat} (h : i < n.positions.size) :
    (n.positions[i]).Within n := by
  have hsize : n.positions.size = n.q.magnitude := by simp [positions]
  have : n.positions[i] = (⟨⟨i⟩⟩ : Position k Nat) := by simp [positions]
  rw [this]
  show i < n.q.magnitude
  omega

/-- **The two readings agree**: lying on the axis (half-open, `i < n`) is membership of the
axis's own closed interval `[0, n−1]`. This is what licenses stating a range obligation in
either vocabulary — the loop's `<` or the interval's `∈` — without maintaining two
independent facts. -/
theorem within_iff_mem_span {n : Extent k Nat} {ord : OrderKind k} {I : IccQ k Nat}
    (hI : n.span? ord = some I) (i : Position k Nat) : i.Within n ↔ I.Mem i.q := by
  unfold span? at hI
  split at hI
  · exact absurd hI (by simp)
  · rename_i hne
    cases hI
    constructor
    · intro h
      exact ⟨show 0 ≤ i.q.magnitude by omega, show i.q.magnitude ≤ n.q.magnitude - 1 by
        have : i.q.magnitude < n.q.magnitude := h
        omega⟩
    · intro h
      have := h.2
      show i.q.magnitude < n.q.magnitude
      have : i.q.magnitude ≤ n.q.magnitude - 1 := this
      omega

universe u v

/-- **Walking an axis directly**: `for i in n do …` yields each `Position` of the extent
`n`, in order, allocating nothing. The in-range guarantee is `positions_within` — the
instance enumerates exactly `positions` — so the loop counter arrives already bound to its
axis *and* already known to be on it, and neither fact has to be asserted in the body. -/
instance {m : Type u → Type v} [Monad m] {k : KindOfProperty} :
    ForIn m (Extent k Nat) (Position k Nat) where
  forIn n init f := forIn [0:n.q.magnitude] init fun i acc => f ⟨⟨i⟩⟩ acc

end Extent

end PropertyKindCalculus

end -- pkc-blanket
