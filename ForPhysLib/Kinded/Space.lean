/-
# Stage 2 — kinded re-authoring of `Physlib/SpaceAndTime/Space`, with definitional erasure

The third rung of [the adoption ladder](../PLAN.md#stage-2-kinded-re-authoring-with-definitional-erasure):
the kinded form becomes the authored form, and the naked form is `rfl`-equal to
`.magnitude` of it. The stage's invariant — **existing theorem statements survive** — is
not claimed but exhibited: PhysLib's own `Space.dist_eq`, Mathlib's `dist_triangle` and
`dist_eq_norm_vsub` each close a kinded goal *verbatim* below, because erasure is
definitional.

The directory's four length-readings each get their kinded author-form, minted at the
boundary tier that sanctions it (Stage 4 pins the audit of these tags):

  * `distanceQ`     — the metric's value, kind *distance* (item 3-1.8)
  * `positionQ`     — a point read from the conventional origin, kind *position vector* (3-1.10)
  * `displacementQ` — the torsor's vector between two points, kind *displacement* (3-1.11)
  * `lengthOf`      — a displacement's norm, kind *length* (3-1.1)

And what the kinds now refuse: summing across the distance/length or the
position/displacement boundary stops *elaborating* — the collisions Stage 0's
distinctness theorems promised, delivered at the term level, while every carrier
instance PhysLib relies on (the torsor, the metric, the `Zero`) stays exactly where
it was.
-/

import ForPhysLib.Kinds.Space
import PropertyKindCalculus.QuantityReal
import PropertyKindCalculus.BoundaryAudit
import Physlib.SpaceAndTime.Space.Basic
import Physlib.SpaceAndTime.Space.Origin

namespace ForPhysLib.Kinded.Space

open PropertyKindCalculus ForPhysLib.Kinds.Space

noncomputable section

/-! ## The four author-forms

Each is a *mint*: a value of PhysLib's carrier enters the calculus under the kind the
directory's prose already assigns it. The tier attribute is the adjudication —
`@[kindIngest]` where a naked value enters, `@[kindCrossing]` where an already-kinded
value crosses to another kind — and Stage 4's `#kind_boundary_audit` pin is what keeps
an *unadjudicated* mint from landing silently later. -/

/-- The directory's metric, read at its kind: `dist p q` is a **distance** — item 3-1.8,
examined shortest-path — in the `Space d` length unit. -/
@[kindIngest]
def distanceQ {d : ℕ} (p q : _root_.Space d) : Quantity distance ℝ := ⟨dist p q⟩

/-- A point of `Space d`, read from the conventional origin `Origin.lean` fixes: a
**position vector** — item 3-1.10, examined from-origin. The origin-dependence the API
map states in prose is this argument's `0`. -/
@[kindIngest]
def positionQ {d : ℕ} (p : _root_.Space d) :
    Quantity positionVector (EuclideanSpace ℝ (Fin d)) := ⟨p -ᵥ (0 : _root_.Space d)⟩

/-- The torsor's vector between two points: a **displacement** — item 3-1.11, examined
between-points, origin-free. -/
@[kindIngest]
def displacementQ {d : ℕ} (p q : _root_.Space d) :
    Quantity displacement (EuclideanSpace ℝ (Fin d)) := ⟨p -ᵥ q⟩

/-- A displacement's norm, crossed to bare **length** — item 3-1.1, the genus. The mint
is attested rather than raw (the ratchet's reviewed column): the norm is not a kind-law
derivation, it is the directory's own `‖·‖`, adjudicated here once. -/
@[kindCrossing]
def lengthOf {d : ℕ} (v : Quantity displacement (EuclideanSpace ℝ (Fin d))) :
    Quantity length ℝ :=
  .attest "the norm of a displacement read as bare length — the directory's own ‖·‖" ‖v.magnitude‖

/-! ## Definitional erasure — the naked form is `.magnitude`, by `rfl` -/

/-- Erasure: the kinded distance *is* the metric's value. -/
@[simp] theorem distanceQ_magnitude {d : ℕ} (p q : _root_.Space d) :
    (distanceQ p q).magnitude = dist p q := rfl

/-- Erasure: the kinded displacement *is* the torsor's vector. -/
@[simp] theorem displacementQ_magnitude {d : ℕ} (p q : _root_.Space d) :
    (displacementQ p q).magnitude = p -ᵥ q := rfl

/-- The emission boundary, stated once as a `def` so it carries its tier: downstream
code that wants the naked real gets it here — and gets exactly `dist`, by `rfl`. -/
@[kindEmission]
def rawDistance {d : ℕ} (p q : _root_.Space d) : ℝ := (distanceQ p q).magnitude

/-- **The Stage-2 invariant, on the nose**: the naked form is definitionally the erasure
of the kinded form, so a theorem stated over `dist` is a theorem about `rawDistance`
with no rewriting at all. -/
theorem rawDistance_eq_dist {d : ℕ} (p q : _root_.Space d) :
    rawDistance p q = dist p q := rfl

/-! ## Existing theorem statements survive — closed by the library's proofs, verbatim -/

/-- PhysLib's own `Space.dist_eq` closes the kinded goal unchanged. -/
example {d : ℕ} (p q : _root_.Space d) :
    (distanceQ p q).magnitude = Real.sqrt (∑ i, (p i - q i) ^ 2) :=
  _root_.Space.dist_eq p q

/-- Mathlib's triangle inequality closes the kinded goal unchanged. -/
theorem distanceQ_triangle {d : ℕ} (p q r : _root_.Space d) :
    (distanceQ p r).magnitude ≤ (distanceQ p q).magnitude + (distanceQ q r).magnitude :=
  dist_triangle p q r

/-- The directory's central law across the kind boundary: the metric is the norm of the
torsor's vector — here, a *distance* and a *length* whose magnitudes agree while the
kinds stay distinct. Mathlib's `dist_eq_norm_vsub` proves it verbatim. -/
theorem distanceQ_eq_lengthOf_displacementQ {d : ℕ} (p q : _root_.Space d) :
    (distanceQ p q).magnitude = (lengthOf (displacementQ p q)).magnitude :=
  dist_eq_norm_vsub (EuclideanSpace ℝ (Fin d)) p q

/-! ## What the kinds refuse — and what they still allow

The refusals are elaboration failures, not proofs: there is no `HAdd` across distinct
kinds, so the collision never reaches a goal. -/

/-- Allowed: displacements compose — same kind, and the carrier has `Add`. -/
example {d : ℕ} (v w : Quantity displacement (EuclideanSpace ℝ (Fin d))) :
    Quantity displacement (EuclideanSpace ℝ (Fin d)) := v + w

-- Refused: a distance is not a bare length, even though both are `ℝ` and their
-- magnitudes can agree (see `distanceQ_eq_lengthOf_displacementQ`).
#check_failure fun (p q : _root_.Space 3) => distanceQ p q + lengthOf (displacementQ p q)

-- Refused: position + displacement across the pair the torsor keeps apart — the
-- kind-level twin of PhysLib's own `Space` vs `EuclideanSpace` separation.
#check_failure fun (p q : _root_.Space 3) => positionQ p + displacementQ p q

end

end ForPhysLib.Kinded.Space
