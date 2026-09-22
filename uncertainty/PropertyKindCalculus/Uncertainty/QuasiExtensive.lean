/-
# §13.5.2 — quasiextensive: the total *approximately equal* to the sum

Dybkær §13.5 presents Bunge's four types. Three are mereological and are settled in the
Mathlib-free core (`PropertyKindCalculus.Extensivity`): unconditionally extensive, conditionally
extensive, intensive. The fourth is not. §13.5.2 says the value for the total is
"approximately equal" to the arithmetic sum over the parts — and *approximately* is a claim
about measurement uncertainty, not about how the system is carved, which is why it is stated
here rather than there.

Making it a predicate rather than a hedge takes three things.

  * **A tolerance, named.** `QuasiExtensive k m u` is additivity to within `u` **at each
    join**. Without the tolerance in the type, "approximately" is not a claim; with it, two
    quasiextensive claims about the same measurement are comparable, and the sharper one is
    the one with the smaller `u`.
  * **A carving-size law.** A tolerance per join accumulates over a tree, so the honest
    whole-tree statement is bounded by the carving's join count: `quasiExtensive_leafSum`
    gives `|value(whole) − ∑ parts| ≤ joins · u`. That the bound *grows with the carving* is
    the content — a library that reports one tolerance for a total, however the total was
    assembled, is reporting the wrong number, and this says by how much.
  * **The branches, related.** §13.5.1 is the `u = 0` case, in both directions
    (`extensive_iff_quasiExtensive_zero`). So quasiextensivity is not a fourth thing beside
    extensivity but a relaxation of it, and §13.5.3 — the total differing "due to the
    respective internal and environmental conditions" — is what a tolerance too small to
    absorb the conditions looks like: `mixing_not_quasiExtensive` refutes any tolerance below
    the 4 mL that water and ethanol actually contract by.

Where the tolerance comes from is R18's business, and `join_within_tolerance` is the join:
model a join's discrepancy as a variable of mean zero and the Chebyshev bound already proved
for coverage intervals says how often `|D| < k·u` holds. The tolerance a quasiextensive claim
carries is therefore a *coverage* statement, with a probability attached, and not a number
chosen to make the claim come out true.
-/

module

public import PropertyKindCalculus.Recarving
public import PropertyKindCalculus.Uncertainty.Coverage

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory ENNReal

namespace PropertyKindCalculus.Uncertainty

open PropertyKindCalculus

universe u'

/-- **§13.5.2 quasiextensive kind.** A kind `k` is *quasiextensive to within `t`* under a
measurement `m` when (i) every part is measured as a value of kind `k` and (ii) the numeral on
a disjoint union differs from the sum of its parts' numerals by at most `t`.

The tolerance is per **join**, not per whole: it is the balance's rounding, the calibration
residual, the contraction on one mixing — one act of composition. What it costs over a whole
carving is `quasiExtensive_leafSum`. -/
structure QuasiExtensive {O : Type u'} (k : KindOfProperty) (m : Measurement O) (t : ℝ) :
    Prop where
  /-- Every measured part is a value of the kind `k`. -/
  ofKind : ∀ d, (m d).kind = k
  /-- The single-split law, additive **to within `t`**. -/
  nearlyAdditive : ∀ a b, |((m (.union a b)).numeral : ℝ) - ((m a).numeral + (m b).numeral)| ≤ t

/-- **Quasiextensive aggregation (the capstone).** The value measured on the whole differs from
the sum over all atomic parts by at most `joins · t` — the per-join tolerance times the number
of joins the carving actually has.

Proved by induction on the decomposition, exactly as `extensive_additive` is: at a leaf the
discrepancy is zero over zero joins, and at a union the triangle inequality splits it into this
join's tolerance plus the two sub-carvings' accumulated bounds. That the bound depends on the
carving and not only on the whole is not a weakness of the proof — it is the reason
§13.5.2 needed a formalization separate from §13.5.1. -/
theorem quasiExtensive_leafSum {O : Type u'} {k : KindOfProperty} {m : Measurement O} {t : ℝ}
    (h : QuasiExtensive k m t) :
    ∀ d, |((m d).numeral : ℝ) - (leafSum m d : ℝ)| ≤ (d.joins : ℝ) * t
  | .atom s => by
      have : ((m (.atom s)).numeral : ℝ) - (leafSum m (.atom s) : ℝ) = 0 := by
        simp [leafSum, Decomposition.fold]
      simp [this, Decomposition.joins]
  | .union a b => by
      have ha := quasiExtensive_leafSum h a
      have hb := quasiExtensive_leafSum h b
      have hj := h.nearlyAdditive a b
      have hsplit : ((m (.union a b)).numeral : ℝ) - (leafSum m (.union a b) : ℝ)
          = (((m (.union a b)).numeral : ℝ) - ((m a).numeral + (m b).numeral))
            + (((m a).numeral : ℝ) - (leafSum m a : ℝ))
            + (((m b).numeral : ℝ) - (leafSum m b : ℝ)) := by
        show _ = _
        push_cast [leafSum, Decomposition.fold]
        ring
      have hjoins : ((Decomposition.joins (.union a b) : Nat) : ℝ)
          = (a.joins : ℝ) + (b.joins : ℝ) + 1 := by
        show ((a.joins + b.joins + 1 : Nat) : ℝ) = _
        push_cast
        ring
      calc |((m (.union a b)).numeral : ℝ) - (leafSum m (.union a b) : ℝ)|
          ≤ |(((m (.union a b)).numeral : ℝ) - ((m a).numeral + (m b).numeral))
              + (((m a).numeral : ℝ) - (leafSum m a : ℝ))|
            + |((m b).numeral : ℝ) - (leafSum m b : ℝ)| := by
              rw [hsplit]; exact abs_add_le _ _
        _ ≤ (|((m (.union a b)).numeral : ℝ) - ((m a).numeral + (m b).numeral)|
              + |((m a).numeral : ℝ) - (leafSum m a : ℝ)|)
            + |((m b).numeral : ℝ) - (leafSum m b : ℝ)| := by
              gcongr
              exact abs_add_le _ _
        _ ≤ (t + (a.joins : ℝ) * t) + (b.joins : ℝ) * t := by gcongr
        _ = ((a.joins : ℝ) + (b.joins : ℝ) + 1) * t := by ring
        _ = ((Decomposition.joins (.union a b) : Nat) : ℝ) * t := by rw [hjoins]

/-- **The distribution license at §13.5.2** — what re-carving a batch axis costs a
quasiextensive output. The totals over the old and the new carving differ by at most
the per-join tolerance times the joins of *both* carvings, because each total stands
within its own `joins · t` of the same preserved whole. This is the quasi-extensive
counterpart of `Recarving.leafSum_invariant`: the extensive case is this bound at
`t = 0`, and that the price names both carvings' joins is the content — a re-carving
that coarsens (fewer joins) tightens its own half of the budget, and none of it is
free. -/
theorem Recarving.leafSum_within {O : Type u'} {k : KindOfProperty} {m : Measurement O}
    {t : ℝ} (h : QuasiExtensive k m t) (r : Recarving m) (d : Decomposition O) :
    |(leafSum m (r.map d) : ℝ) - (leafSum m d : ℝ)|
      ≤ (((r.map d).joins : ℝ) + (d.joins : ℝ)) * t := by
  have h1 := quasiExtensive_leafSum h (r.map d)
  have h2 := quasiExtensive_leafSum h d
  have hp : ((m (r.map d)).numeral : ℝ) = ((m d).numeral : ℝ) := by
    exact_mod_cast r.preserves d
  calc |(leafSum m (r.map d) : ℝ) - (leafSum m d : ℝ)|
      = |(((m d).numeral : ℝ) - (leafSum m d : ℝ))
          - (((m (r.map d)).numeral : ℝ) - (leafSum m (r.map d) : ℝ))| := by
        congr 1
        rw [← hp]
        ring
    _ ≤ |((m d).numeral : ℝ) - (leafSum m d : ℝ)|
          + |((m (r.map d)).numeral : ℝ) - (leafSum m (r.map d) : ℝ)| := by
        rw [sub_eq_add_neg (((m d).numeral : ℝ) - (leafSum m d : ℝ))]
        exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ (d.joins : ℝ) * t + ((r.map d).joins : ℝ) * t := add_le_add h2 h1
    _ = (((r.map d).joins : ℝ) + (d.joins : ℝ)) * t := by ring

/-! ## §13.5.1 is the zero-tolerance case -/

/-- An extensive kind is quasiextensive to within nothing at all. -/
theorem QuasiExtensive.of_extensive {O : Type u'} {k : KindOfProperty} {m : Measurement O}
    (h : Extensive k m) : QuasiExtensive k m 0 :=
  { ofKind := h.ofKind
    nearlyAdditive := fun a b => by
      have : ((m (.union a b)).numeral : ℝ) - ((m a).numeral + (m b).numeral) = 0 := by
        rw [h.additive a b]; push_cast; ring
      simp [this] }

/-- And a kind quasiextensive to within nothing at all is extensive: `|x| ≤ 0` forces `x = 0`,
so the tolerance is not hiding a weaker law. The two §13.5 branches meet exactly at `t = 0`. -/
theorem QuasiExtensive.extensive_of_zero {O : Type u'} {k : KindOfProperty} {m : Measurement O}
    (h : QuasiExtensive k m 0) : Extensive k m :=
  { ofKind := h.ofKind
    additive := fun a b => by
      have h0 := h.nearlyAdditive a b
      have : ((m (.union a b)).numeral : ℝ) - ((m a).numeral + (m b).numeral) = 0 :=
        abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
      have hcast : ((m (.union a b)).numeral : ℝ) = (((m a).numeral + (m b).numeral : Int) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hcast }

/-- **§13.5.1 is §13.5.2 at zero tolerance**, in both directions. -/
theorem extensive_iff_quasiExtensive_zero {O : Type u'} {k : KindOfProperty}
    {m : Measurement O} : Extensive k m ↔ QuasiExtensive k m 0 :=
  ⟨QuasiExtensive.of_extensive, QuasiExtensive.extensive_of_zero⟩

/-! ## Witness — a balance that rounds, and a mixture that contracts

Two measurements, each answering one of the two questions a predicate has to answer: is
anything quasiextensive that is not extensive, and does the tolerance rule anything out? -/

/-- Mass, a ratio kind. -/
def coarseMassKind : KindOfProperty := { id := "mass", scale := .ratio }

/-- Mass read on a balance whose composite readings carry one digit of rounding: an atomic part
reads its own leaf count, and any composite reads one more than the total of its parts. -/
def coarseMass : Measurement System := fun d =>
  { kind := coarseMassKind
    numeral := d.fold (fun _ => (1 : Int)) (· + ·)
      + (match d with | .atom _ => (0 : Int) | .union _ _ => 1)
    reference := "kg" }

/-- **The rounding balance is quasiextensive to within one digit** — and one digit is all it
takes to escape §13.5.1, which is the whole point of the branch. -/
theorem coarseMass_quasiExtensive :
    QuasiExtensive coarseMassKind coarseMass 1 := by
  refine ⟨fun _ => rfl, fun a b => ?_⟩
  have hcast : ((coarseMass (.union a b)).numeral : ℝ)
      - ((coarseMass a).numeral + (coarseMass b).numeral)
      = ((1 : Int) - (match a with | .atom _ => 0 | .union _ _ => 1)
          - (match b with | .atom _ => 0 | .union _ _ => 1) : Int) := by
    cases a <;> cases b <;> · show _ = _ ; push_cast [coarseMass, Decomposition.fold] ; ring
  rw [hcast]
  cases a <;> cases b <;> · norm_num

/-- **And it is not extensive**: two atomic parts read 1 each and compose to a reading of 3. -/
theorem coarseMass_not_extensive :
    ¬ Extensive coarseMassKind coarseMass := by
  intro h
  have := h.additive (.atom { id := "a" }) (.atom { id := "b" })
  simp [coarseMass, Decomposition.fold] at this

/-- **A tolerance below the contraction is refuted.** Volume on mixing (`volMix`, the §13.5.3
witness) is quasiextensive only from 4 mL up: below that the water/ethanol pair itself is a
counterexample. So the tolerance is doing work — it is not a hedge that any measurement
satisfies — and §13.5.3 reads as §13.5.2 with a tolerance the conditions set. -/
theorem mixing_not_quasiExtensive {t : ℝ} (ht : t < 4) :
    ¬ QuasiExtensive PropertyKindCalculus.volume volMix t := by
  intro h
  have hj := h.nearlyAdditive waterPart ethanolPart
  have : |((volMix (waterPart.union ethanolPart)).numeral : ℝ)
      - ((volMix waterPart).numeral + (volMix ethanolPart).numeral)| = 4 := by
    show |((96 : Int) : ℝ) - (((50 : Int) : ℝ) + ((50 : Int) : ℝ))| = 4
    norm_num
  rw [this] at hj
  linarith

/-! ## Where the tolerance comes from (R18)

A tolerance chosen to make a claim come out true is worth nothing. The one already proved for
coverage intervals is worth something: model the discrepancy at a join as a random variable of
mean zero and finite variance, and Chebyshev bounds how often the `nearlyAdditive` field holds
at `t = k · u`. -/

/-- **The per-join tolerance as a coverage statement.** For a join discrepancy `D` of mean zero,
`|D| < k · u` — the `nearlyAdditive` field at tolerance `k` standard uncertainties — holds with
probability at least `1 − 1/k²`, distribution-free. This is `Coverage.coverageBound_stdUnc` with
the mean discharged: the number a quasiextensive claim carries is a coverage factor, and the
probability it buys is `1 − 1/k²` and not the Gaussian figure. -/
theorem join_within_tolerance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : Ω → ℝ} (hDm : Measurable D) (hD : MemLp D 2 μ)
    (hmean : μ[D] = 0) {k : ℝ} (hk : 0 < k) (hv : 0 < variance D μ) :
    1 - ENNReal.ofReal (1 / k ^ 2) ≤ μ {ω | |D ω| < k * Coverage.stdUnc D μ} := by
  have h := Coverage.coverageBound_stdUnc hDm hD hk hv
  simpa [hmean] using h

end PropertyKindCalculus.Uncertainty

end -- pkc-blanket-expose
end -- pkc-blanket
