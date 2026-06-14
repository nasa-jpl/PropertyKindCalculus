/-
# Extensivity — additive aggregation over parts (Dybkær §13.5)

Dybkær (2009), §13.5, divides kinds-of-quantity by how a value behaves under
*composition of systems*:

  * an **extensive** kind aggregates additively — the value over a whole is the sum
    of the values over its disjoint parts (mass, amount of substance, electric
    charge);
  * other kinds do not — an **intensive** kind is constant under composition
    (temperature, density), and some kinds are neither, failing additivity outright
    (volume *on mixing* contracts: ethanol and water mix sub-additively).

This is a *quantified arithmetic law over the mereology of systems* — exactly the
shape a description logic cannot state. It is recorded here, in the Mathlib-free
core, over the numeral of a property value: the parts are measured in one shared
reference (so their numerals are commensurable and may be summed), and extensivity
is additivity of those numerals over a {decomposition} of the system. Tracking
which kinds are extensive is the precondition for soundly summing measurements.
-/

import PropertyKindCalculus.PropertyValue

namespace PropertyKindCalculus

/-- A **decomposition** of a system into disjoint parts (the mereological structure
deferred from the foundations chapter, §3.3): an atomic {system}, or the disjoint
union of two sub-decompositions. The leaves are the atomic parts; each node stands
for the whole they compose. -/
inductive Decomposition where
  /-- An atomic, indivisible part. -/
  | atom : System → Decomposition
  /-- The disjoint union of two parts. -/
  | union : Decomposition → Decomposition → Decomposition
deriving Repr

/-- A **measurement** of a fixed kind over a decomposition: the property value
observed on the (sub-)system at each node — a leaf carries the value of that atomic
part, a node the value of the whole it composes. -/
abbrev Measurement := Decomposition → PropertyValue

/-- The total over the atomic **parts** (leaves) of a decomposition: the sum of the
numerals the measurement assigns to each leaf. This is the right-hand side
$`\sum_i \mathrm{value}(s_i)` of the extensive law. -/
def leafSum (m : Measurement) : Decomposition → Int
  | .atom s => (m (.atom s)).numeral
  | .union a b => leafSum m a + leafSum m b

/-- **§13.5 extensive kind.** A kind `k` is *extensive* under a measurement `m`
when (i) every part is measured as a value *of kind* `k` (one shared reference, so
the numerals are commensurable) and (ii) the numeral on a disjoint union is the sum
of the numerals on the parts. Mass satisfies this; volume on mixing does not. -/
structure Extensive (k : KindOfProperty) (m : Measurement) : Prop where
  /-- Every measured part is a value of the kind `k`. -/
  ofKind : ∀ d, (m d).kind = k
  /-- The single-split additivity law: a union measures as the sum of its two parts. -/
  additive : ∀ a b, (m (.union a b)).numeral = (m a).numeral + (m b).numeral

/-- **Extensive aggregation (the capstone).** For an extensive kind, the value
measured on the *whole* equals the sum over *all* atomic parts of a decomposition,
$$`\mathrm{value}\Bigl(\bigsqcup_i s_i\Bigr) = \sum_i \mathrm{value}(s_i),`
to arbitrary depth. The $`\forall`-quantified law itself — not a single instance —
is the deliverable: it is proved by induction on the decomposition, lifting the
single-split `additive` field to the whole tree. -/
theorem extensive_additive {k : KindOfProperty} {m : Measurement}
    (h : Extensive k m) : ∀ d, (m d).numeral = leafSum m d
  | .atom _ => rfl
  | .union a b => by
      have ha := extensive_additive h a
      have hb := extensive_additive h b
      simp only [leafSum, h.additive, ha, hb]

/-! ## Counterexample — volume on mixing is not extensive

The classic Flater/metrology example: 50 mL of water and 50 mL of ethanol, mixed,
occupy ≈ 96 mL, not 100 mL. A measurement that returns 50 for each atomic part and
96 for the mixture is therefore *sub-additive* — it witnesses $`\neg\,\mathrm{Extensive}`
for volume, and stating the negation keeps the extensive predicate honest. -/

/-- Volume, a ratio kind. -/
def volume : KindOfProperty := { id := "volume", scale := .ratio }

/-- 50 mL of water, as an atomic part. -/
def waterPart : Decomposition := .atom { id := "50 mL water" }
/-- 50 mL of ethanol, as an atomic part. -/
def ethanolPart : Decomposition := .atom { id := "50 mL ethanol" }
/-- The water/ethanol mixture, as the disjoint union of the two parts. -/
def mixture : Decomposition := .union waterPart ethanolPart

/-- A volume measurement that contracts on mixing: every atomic part reads 50 mL,
any mixture reads 96 mL. -/
def volMix : Measurement
  | .atom _ => { kind := volume, numeral := 50, reference := "mL" }
  | .union _ _ => { kind := volume, numeral := 96, reference := "mL" }

/-- **Volume on mixing is not extensive.** The mixture's volume is *strictly less*
than the sum of the component volumes (96 < 50 + 50), so additivity fails and
`volume` is not extensive under this measurement. Matching the extensive law would
be unsound here — which is exactly why extensivity must be tracked, not assumed. -/
theorem mixing_subadditive :
    (volMix mixture).numeral
        < (volMix waterPart).numeral + (volMix ethanolPart).numeral
      ∧ ¬ Extensive volume volMix :=
  ⟨by decide, fun h => absurd (h.additive waterPart ethanolPart) (by decide)⟩

end PropertyKindCalculus
