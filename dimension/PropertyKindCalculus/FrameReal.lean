/-
# FrameReal — what survives a change of frame, proved at the specification carrier

`PropertyKindCalculus.Frame` defines the structure: readings indexed by frame, the three
variances, and the actions that implement their transformation laws. It proves nothing,
because a statement about a sum of products needs ring laws and the Mathlib-free core does
not carry them. This module supplies them at `ℝ`, exactly as `QuantityReal` supplies the
specification carrier for `Quantity`.

Three results, and they are the requirement rather than a convenience:

  * **functoriality** — the identity change acts as the identity, and composing two changes
    is the composite change (`toFrameVector_id`, `toFrameVector_comp`). Without these,
    "changing the frame" would not be an action of anything and "changing it back" would not
    be a meaningful phrase. They are the frame twin of `UnitConversion.convertReal_self` and
    `convertReal_roundtrip`.
  * **invariance of the scalar product** (`dot_toFrameVector`) — the payoff. Two vector
    quantities contracted in one frame give the same number as their images contracted in
    any orthonormally related frame. Everything scalar that a physical model computes from
    vector quantities — a kinetic energy, a potential energy, a modulus, a work — is a
    scalar product, so this single theorem is what "a change of representation does not
    change the physics" amounts to in this setting.
  * **non-invariance of a component** — stated as its own theorem with a witness
    (`component_not_invariant`), because the preceding results are precisely the kind a
    reader over-generalizes. A component is not a scalar; it is a number that happens to
    have no free index left.

The hypothesis throughout is `IsOrthonormal`, never a field of `FrameChange` — a general
linear change of frame is a perfectly good thing to apply, and it does not preserve the dot
product. Making orthonormality a hypothesis is what lets the type say the first and the
theorem say the second.
-/

module

public import PropertyKindCalculus.Frame
public import PropertyKindCalculus.QuantityReal
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
-- Private scope only: the checks below reduce through bodies sealed in the core
-- library; `import all` gives this file the reduction without exposing them.
import all PropertyKindCalculus.Frame
import all PropertyKindCalculus.Bounds

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus

open Finset

variable {n : Nat} {f g h : Frame} {k k₁ k₂ : KindOfProperty}

/-! ## The bridge to `Finset.sum`

The core's `sumFin` is a plain recursion — no `Fintype`, so that a change of frame runs at
`Float`. Over `ℝ` it is Mathlib's sum, and every proof below is conducted through this one
rewrite. -/

/-- **The core recursion is Mathlib's sum.** -/
theorem sumFin_eq_sum : ∀ {m : Nat} (v : Fin m → ℝ), sumFin v = ∑ i, v i := by
  intro m
  induction m with
  | zero => intro v; simp [sumFin]
  | succ p ih => intro v; rw [sumFin, Fin.sum_univ_succ, ih]

/-- The scalar product, as Mathlib writes it. -/
theorem dot_eq_sum (hk : ProductKind k₁ k₂ k)
    (x : InFrame f .vector k₁ (Fin n → ℝ)) (y : InFrame f .vector k₂ (Fin n → ℝ)) :
    (InFrame.dot hk x y).components = ∑ i, x.components i * y.components i := by
  rw [InFrame.dot_components, sumFin_eq_sum]

/-- The matrix action, as Mathlib writes it. -/
theorem mulVec_eq_sum (c : FrameChange n ℝ f g) (v : Fin n → ℝ) (i : Fin n) :
    c.mulVec v i = ∑ j, c.entry i j * v j := by
  rw [FrameChange.mulVec, sumFin_eq_sum]

/-- Orthonormality, as Mathlib writes it. -/
theorem isOrthonormal_iff (c : FrameChange n ℝ f g) :
    c.IsOrthonormal
      ↔ ∀ i j : Fin n, (∑ m, c.entry m i * c.entry m j) = if i = j then 1 else 0 := by
  constructor
  · intro hc i j; rw [← sumFin_eq_sum]; exact hc i j
  · intro hc i j; rw [sumFin_eq_sum]; exact hc i j

/-! ## Functoriality — a change of frame is an action -/

/-- **Staying put changes nothing.** The identity frame change acts as the identity on
components. -/
@[simp] theorem mulVec_id (v : Fin n → ℝ) (i : Fin n) :
    (FrameChange.id n ℝ f).mulVec v i = v i := by
  rw [mulVec_eq_sum]
  simp [FrameChange.id]

/-- The identity change of frame is the identity on readings. -/
@[simp] theorem toFrameVector_id (x : InFrame f .vector k (Fin n → ℝ)) :
    InFrame.toFrameVector (FrameChange.id n ℝ f) x = x := by
  cases x with | mk q => cases q with | mk m =>
  simp only [InFrame.toFrameVector, InFrame.components, InFrame.mk.injEq, Quantity.mk.injEq]
  funext i
  exact mulVec_id m i

/-- **Two changes compose.** Going `f → g` and then `g → h` is going `f → h` by the
composite — so a frame change can be undone, and a chain of them is a single one. -/
theorem mulVec_comp (c₂ : FrameChange n ℝ g h) (c₁ : FrameChange n ℝ f g) (v : Fin n → ℝ) :
    (c₂.comp c₁).mulVec v = c₂.mulVec (c₁.mulVec v) := by
  funext i
  have hL : (c₂.comp c₁).mulVec v i = ∑ j, (∑ m, c₂.entry i m * c₁.entry m j) * v j := by
    rw [mulVec_eq_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [FrameChange.comp, sumFin_eq_sum]
  have hR : c₂.mulVec (c₁.mulVec v) i = ∑ m, c₂.entry i m * (∑ j, c₁.entry m j * v j) := by
    rw [mulVec_eq_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [mulVec_eq_sum]
  rw [hL, hR]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by ring

/-- Composition, on readings. -/
theorem toFrameVector_comp (c₂ : FrameChange n ℝ g h) (c₁ : FrameChange n ℝ f g)
    (x : InFrame f .vector k (Fin n → ℝ)) :
    InFrame.toFrameVector (c₂.comp c₁) x
      = InFrame.toFrameVector c₂ (InFrame.toFrameVector c₁ x) := by
  cases x with | mk q => cases q with | mk m =>
  simp only [InFrame.toFrameVector, InFrame.components, InFrame.mk.injEq, Quantity.mk.injEq]
  exact mulVec_comp c₂ c₁ m

/-! ## The invariance result -/

/-- **The scalar product is invariant under an orthonormal change of frame.**

`(C x) · (C y) = x · y`. Expanding both matrix actions and exchanging the order of
summation collects the frame's entries into `Σᵢ C i j · C i l`, which orthonormality
collapses to `δⱼₗ` — so the frame leaves the expression entirely and what remains is the
contraction in the original frame.

This is the theorem the whole module is for. Every scalar a mechanical model reads off a
configuration is a contraction of vector quantities — kinetic energy `½ m (v·v)`, potential
energy, work `F·d`, a modulus — so *this* is the sense in which choosing Cartesian
coordinates does not change the physics: not that the components agree (they do not, and
`component_not_invariant` below exhibits a pair that differs), but that everything the model
actually asserts is built from contractions, and contractions do not move. -/
theorem dot_toFrameVector {c : FrameChange n ℝ f g} (hc : c.IsOrthonormal)
    (hk : ProductKind k₁ k₂ k)
    (x : InFrame f .vector k₁ (Fin n → ℝ)) (y : InFrame f .vector k₂ (Fin n → ℝ)) :
    (InFrame.dot hk (InFrame.toFrameVector c x) (InFrame.toFrameVector c y)).components
      = (InFrame.dot hk x y).components := by
  rw [dot_eq_sum, dot_eq_sum]
  simp only [InFrame.toFrameVector_components]
  calc ∑ i, c.mulVec x.components i * c.mulVec y.components i
      = ∑ i, ∑ j, ∑ l, c.entry i j * c.entry i l * (x.components j * y.components l) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mulVec_eq_sum, mulVec_eq_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ j, ∑ l, (∑ i, c.entry i j * c.entry i l) * (x.components j * y.components l) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => by rw [Finset.sum_mul]
    _ = ∑ j, x.components j * y.components j := by
        have hcj : ∀ j l : Fin n,
            (∑ i, c.entry i j * c.entry i l) = if j = l then 1 else 0 :=
          fun j l => (isOrthonormal_iff c).mp hc j l
        simp only [hcj, ite_mul, one_mul, zero_mul]
        simp

/-- **The squared magnitude is invariant** — the diagonal case, and the one a kinetic or
potential energy is. -/
theorem normSq_toFrameVector {c : FrameChange n ℝ f g} (hc : c.IsOrthonormal)
    (hk : ProductKind k₁ k₁ k) (x : InFrame f .vector k₁ (Fin n → ℝ)) :
    (InFrame.normSq hk (InFrame.toFrameVector c x)).components
      = (InFrame.normSq hk x).components :=
  dot_toFrameVector hc hk x x

/-- **A scalar reading is invariant, definitionally.** No matrix is consulted, so there is
nothing to prove and nothing to assume — in particular no orthonormality. That contrast is
the content: the scalar product's invariance is a *theorem with a hypothesis*, and a
scalar's is not a theorem at all. -/
theorem toFrameScalar_components' (x : InFrame f .scalar k ℝ) :
    (InFrame.toFrameScalar (g := g) x).components = x.components := by
  rw [InFrame.toFrameScalar, InFrame.components, InFrame.components]

/-! ## And what is *not* invariant

Stated with a witness rather than left as a caveat. -/

/-- The quarter-turn of the plane, `[[0, −1], [1, 0]]` — the smallest concrete orthonormal
change of frame. -/
noncomputable def quarterTurn (f g : Frame) : FrameChange 2 ℝ f g :=
  ⟨fun i j => if i = 0 then (if j = 0 then 0 else -1) else (if j = 0 then 1 else 0)⟩

/-- It is orthonormal, so the invariance theorems apply to it. -/
theorem quarterTurn_isOrthonormal (f g : Frame) : (quarterTurn f g).IsOrthonormal := by
  rw [isOrthonormal_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [quarterTurn, Fin.sum_univ_succ]

/-- **A component is not invariant, and here is the vector that shows it.** `(1, 0)` read in
`f` has first component `1`; the *same quantity* read in the quarter-turned frame has first
component `0`. This is not two vectors — it is one vector and two frames — which is exactly
why a per-component discipline cannot be a metrological guarantee, and why
`InFrame.component` lands at `scalar` variance with no invariance theorem attached to it. -/
theorem component_not_invariant (f g : Frame) (k : KindOfProperty) :
    ∃ x : InFrame f .vector k (Fin 2 → ℝ),
      (InFrame.toFrameVector (quarterTurn f g) x).components 0 ≠ x.components 0 := by
  refine ⟨⟨⟨fun i => if i = 0 then 1 else 0⟩⟩, ?_⟩
  have hl : (InFrame.toFrameVector (quarterTurn f g)
        (⟨⟨fun i => if i = 0 then 1 else 0⟩⟩ : InFrame f .vector k (Fin 2 → ℝ))).components 0
      = (0 : ℝ) := by
    rw [InFrame.toFrameVector_components, mulVec_eq_sum]
    simp [quarterTurn, InFrame.components]
  rw [hl]
  simp [InFrame.components]

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
