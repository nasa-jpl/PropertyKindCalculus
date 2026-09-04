/-
# Extensivity — how a value behaves under composition (Dybkær §13.5)

Dybkær (2009), §13.5, divides kinds-of-quantity "according to physical (and arithmetic)
additivity", presenting Bunge's four types. Three of the four are what a metrology layer has
to tell apart, and this module realizes them:

  * **§13.5.1, unconditionally extensive** — "a quantity value for the total of a system
    equals the arithmetic sum of the quantity values for its parts": mass, amount of
    substance, electric charge. `Extensive`, with `extensive_additive` lifting a single split
    to a whole tree.
  * **§13.5.3, conditionally extensive** — the addition exists, but "a quantity value for the
    total of a system may be different from the arithmetic sum of the quantity values for its
    parts due to the respective internal and environmental conditions". Volume on mixing is
    the witness (`mixing_subadditive`): what this layer records is the failure of §13.5.1,
    which is the fact an aggregating library needs.
  * **§13.5.4, intensive** — "a physical addition operation does not exist and … a quantity
    value is invariant with the extent of a system of constant composition": temperature,
    density, the angular velocity of a rigid body. `Intensive`, whose law carries Dybkær's
    *of constant composition* as an explicit hypothesis, because that clause is where the
    content is.

(§13.5.2, *quasiextensive* — the total "approximately equal" to the sum — is about
measurement uncertainty rather than about the mereology, and belongs to the uncertainty
layer, not here.)

`WholeProper` adds a case the four types do not name: a value the parts do not determine at
all — no addition, and no invariance with extent either, because the parts do not bear the
kind. The normal-mode frequency of a coupled pair is the standard example, a lone oscillator
having no normal mode to contribute. Under the formalizations here it satisfies none of
Bunge's types, and it is Marmodoro's *substantial* power rather than Dybkær's vocabulary
that names it.

This is a *quantified arithmetic law over the mereology of systems* — exactly the
shape a description logic cannot state. It is recorded here, in the Mathlib-free
core, over the numeral of a property value: the parts are measured in one shared
reference (so their numerals are commensurable and may be summed), and extensivity
is additivity of those numerals over a {decomposition} of the system. Tracking
which kinds are extensive is the precondition for soundly summing measurements.

A `Decomposition` is a **carving**, and deliberately not a census: nothing here fixes
how many parts a system has, and every law below is quantified over all carvings
rather than stated for one. That is Marmodoro's point about physical structure — it
unites without bringing a count principle, so "[i]t is an open question how many
entities a physical structure is" (*Whole, but not One*, 2018, §3) — and it is why
the ∀-quantified form of `extensive_additive` is the deliverable: a total that
depends on how the whole was cut is not a total. What a carving cannot supply is the
*whole*; that arrives one layer up, with a sort of system and the license to
aggregate at it (`Composite.lean`).
-/

import PropertyKindCalculus.PropertyValue

namespace PropertyKindCalculus

universe u

/-- A **decomposition** of a system into disjoint parts (the mereological structure
deferred from the foundations chapter, §3.3): an atomic part, or the disjoint
union of two sub-decompositions. The leaves are the atomic parts; each node stands
for the whole they compose.

Parameterized over the **part type** `O` for the reason `IndividualQuantity` is
parameterized over its object type: the mereology of a host library's own objects — the
particles of a mechanical system, the cells of a mesh — is the same mereology, and
nothing here reads a part except to hand it to the measurement. `Decomposition System`
is the nominal reading and the one the counterexample below uses. -/
inductive Decomposition (O : Type u) where
  /-- An atomic, indivisible part. -/
  | atom : O → Decomposition O
  /-- The disjoint union of two parts. -/
  | union : Decomposition O → Decomposition O → Decomposition O
deriving Repr

/-- **The fold over a decomposition**: a value per leaf, combined at every union. The one
recursion this module has over the mereology, so `leafSum` below and the quantity-level
`assemble` (`Composite.lean`) are the *same* traversal at two carriers rather than two
traversals that happen to agree. -/
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

/-- A **measurement** of a fixed kind over a decomposition: the property value
observed on the (sub-)system at each node — a leaf carries the value of that atomic
part, a node the value of the whole it composes. -/
abbrev Measurement (O : Type u) := Decomposition O → PropertyValue

/-- The total over the atomic **parts** (leaves) of a decomposition: the sum of the
numerals the measurement assigns to each leaf. This is the right-hand side
$`\sum_i \mathrm{value}(s_i)` of the extensive law. -/
def leafSum {O : Type u} (m : Measurement O) : Decomposition O → Int :=
  Decomposition.fold (fun s => (m (.atom s)).numeral) (· + ·)

/-- **§13.5 extensive kind.** A kind `k` is *extensive* under a measurement `m`
when (i) every part is measured as a value *of kind* `k` (one shared reference, so
the numerals are commensurable) and (ii) the numeral on a disjoint union is the sum
of the numerals on the parts. Mass satisfies this; volume on mixing does not. -/
structure Extensive {O : Type u} (k : KindOfProperty) (m : Measurement O) : Prop where
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
theorem extensive_additive {O : Type u} {k : KindOfProperty} {m : Measurement O}
    (h : Extensive k m) : ∀ d, (m d).numeral = leafSum m d
  | .atom _ => rfl
  | .union a b => by
      show (m (.union a b)).numeral = leafSum m a + leafSum m b
      rw [h.additive, extensive_additive h a, extensive_additive h b]

/-! ## Intensity, and a case the four types do not name

Additivity is one answer to "what does composition do to this value?", and the alternatives
are not the absence of an answer. An **intensive** kind answers *nothing changes*, on the
condition Dybkær's definition states; a **whole-proper** kind answers *the parts do not
determine it*. Both are stated here against the same `Measurement`, so a model that claims
one is claiming something refutable. -/

/-- **A property of every atomic part of a carving.** The leaf-wise quantifier the intensive
law needs: `Extensive` reaches its leaves through arithmetic (`leafSum`), and intensivity
has no arithmetic to reach them with. -/
def Decomposition.Forall {O : Type u} (p : O → Prop) : Decomposition O → Prop
  | .atom s => p s
  | .union a b => Decomposition.Forall p a ∧ Decomposition.Forall p b

/-- **§13.5.4 intensive kind-of-quantity.** A kind `k` is *intensive* under a measurement `m`
when (i) every part is measured as a value of kind `k`, and (ii) composing two parts **that
already agree** leaves the value where it was: temperature, density, the angular velocity of
a rigid body.

Condition (ii) is Dybkær's definition read literally, and the literal reading is the design.
His §13.5.4 asks that "a physical addition operation does not exist and … a quantity value is
invariant with the extent of a system of constant composition" — and *of constant
composition* is the clause a shorter phrasing drops. Without it the law would assert that
mixing water at 20 °C with water at 80 °C leaves either reading intact. With it, agreement
between the parts is the hypothesis, and what the structure says about parts that *disagree*
is nothing at all: an intensive kind licenses no reading of the whole from unequal parts,
which is a narrower claim than a total law and an honest one. -/
structure Intensive {O : Type u} (k : KindOfProperty) (m : Measurement O) : Prop where
  /-- Every measured part is a value of the kind `k`. -/
  ofKind : ∀ d, (m d).kind = k
  /-- The single-split constancy law, with its hypothesis explicit: two parts reading the
  same value compose to a whole reading that value. -/
  uniform : ∀ a b, (m a).numeral = (m b).numeral → (m (.union a b)).numeral = (m a).numeral

/-- **Intensive aggregation (the capstone).** For an intensive kind, a whole *all* of whose
atomic parts read `v` reads `v` itself — to arbitrary depth, over any carving, proved by
induction on the decomposition exactly as `extensive_additive` is.

The two capstones are the same theorem at two aggregation modes, which is the point of
stating both: `Extensive` sends the leaves to a sum, `Intensive` sends a *uniform* family of
leaves to its common value, and a kind that does neither is not thereby unmeasurable — it is
`WholeProper` below. -/
theorem intensive_uniform {O : Type u} {k : KindOfProperty} {m : Measurement O} {v : Int}
    (h : Intensive k m) :
    ∀ d, Decomposition.Forall (fun s => (m (.atom s)).numeral = v) d → (m d).numeral = v
  | .atom _, hs => hs
  | .union a b, ⟨ha, hb⟩ => by
      have hA := intensive_uniform h a ha
      have hB := intensive_uniform h b hb
      rw [h.uniform a b (hA.trans hB.symm), hA]

/-- **The two branches exclude each other, wherever there is anything to measure.** An
intensive kind is not extensive as soon as two parts agree on a *nonzero* value: additivity
would double it, constancy keeps it, and only `0 = 0 + 0` satisfies both.

The zero escape is not a defect of the statement — it is the observation that a kind whose
every reading is zero satisfies both laws vacuously, which is why the hypothesis is stated
rather than assumed away. -/
theorem not_extensive_of_intensive {O : Type u} {k : KindOfProperty} {m : Measurement O}
    (hi : Intensive k m) {a b : Decomposition O} (hab : (m a).numeral = (m b).numeral)
    (hne : (m a).numeral ≠ 0) : ¬ Extensive k m := by
  intro he
  have hcancel : (m a).numeral + (m b).numeral = (m a).numeral + 0 := by
    rw [Int.add_zero, ← he.additive a b, hi.uniform a b hab]
  exact hne (hab.trans (Int.add_left_cancel hcancel))

/-- **A whole-proper kind — the case Bunge's four types do not name.** The value of the whole
is produced by *no* aggregation over the parts: neither by summing them (`notAdditive`) nor
by sharing a common reading with them (`notUniform`). The normal-mode frequency of a coupled
pair is the standard case — a lone oscillator has no normal mode at all, so there is nothing
to sum and nothing to inherit. It is not §13.5.4 intensive: the value is not invariant with
the extent of the system, since a third oscillator moves every mode.

Both fields are **exhibited**, as pairs of atomic parts, rather than stated as negated
universals. That is deliberate: a negated universal is satisfied by a measurement that is
merely undefined somewhere, while a witness pins the failure to two parts a reader can point
at — the same discipline `mixing_subadditive` follows for volume, and the reason `assemble`
over such a kind can be shown to return the *wrong number* rather than merely an
unjustified one (`assemble_ne_measured`, `Composite.lean`).

This is Marmodoro's substantial power in the §13.5 vocabulary. Her structural powers
constitute a whole out of parts — the aggregable kinds — while the substantial power "*is*
the electron" (*Whole, but not One*, 2018, §4): borne by the whole, and not by anything the
whole is made of. -/
structure WholeProper {O : Type u} (k : KindOfProperty) (m : Measurement O) : Prop where
  /-- Every measured part is a value of the kind `k`. -/
  ofKind : ∀ d, (m d).kind = k
  /-- Two atomic parts whose union does **not** read their sum. -/
  notAdditive : ∃ p q : O,
    (m (.union (.atom p) (.atom q))).numeral
      ≠ (m (.atom p)).numeral + (m (.atom q)).numeral
  /-- Two atomic parts that **agree**, whose union does not read their common value. -/
  notUniform : ∃ p q : O,
    (m (.atom p)).numeral = (m (.atom q)).numeral ∧
      (m (.union (.atom p) (.atom q))).numeral ≠ (m (.atom p)).numeral

namespace WholeProper

variable {O : Type u} {k : KindOfProperty} {m : Measurement O}

/-- A whole-proper kind is not extensive: its own witness refutes the additivity field. -/
theorem not_extensive (h : WholeProper k m) : ¬ Extensive k m := by
  obtain ⟨p, q, hpq⟩ := h.notAdditive
  exact fun he => hpq (he.additive (.atom p) (.atom q))

/-- A whole-proper kind is not intensive either: its own witness refutes the constancy
field. Together with `not_extensive` this is what "neither" means — the third branch is
occupied, not empty. -/
theorem not_intensive (h : WholeProper k m) : ¬ Intensive k m := by
  obtain ⟨p, q, hpq, hne⟩ := h.notUniform
  exact fun hi => hne (hi.uniform (.atom p) (.atom q) hpq)

/-- **The carving that gets it wrong.** For a whole-proper kind there is a decomposition
whose leaf sum is not the value of the whole — the number a library that aggregated anyway
would report. This is the `Int`-level statement; `assemble_ne_measured` (`Composite.lean`)
is the same fact at the quantity layer, where the sum is a term someone actually wrote. -/
theorem exists_leafSum_ne (h : WholeProper k m) :
    ∃ d : Decomposition O, (m d).numeral ≠ leafSum m d := by
  obtain ⟨p, q, hpq⟩ := h.notAdditive
  exact ⟨.union (.atom p) (.atom q), hpq⟩

end WholeProper

/-! ## Counterexample — volume on mixing is not extensive

The classic Flater/metrology example: 50 mL of water and 50 mL of ethanol, mixed,
occupy ≈ 96 mL, not 100 mL. A measurement that returns 50 for each atomic part and
96 for the mixture is therefore *sub-additive* — it witnesses $`\neg\,\mathrm{Extensive}`
for volume, and stating the negation keeps the extensive predicate honest. -/

/-- Volume, a ratio kind. -/
def volume : KindOfProperty := { id := "volume", scale := .ratio }

/-- 50 mL of water, as an atomic part. -/
def waterPart : Decomposition System := .atom { id := "50 mL water" }
/-- 50 mL of ethanol, as an atomic part. -/
def ethanolPart : Decomposition System := .atom { id := "50 mL ethanol" }
/-- The water/ethanol mixture, as the disjoint union of the two parts. -/
def mixture : Decomposition System := .union waterPart ethanolPart

/-- A volume measurement that contracts on mixing: every atomic part reads 50 mL,
any mixture reads 96 mL. -/
def volMix : Measurement System
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

/-! ## Witness — density is intensive, and therefore not extensive

Two parcels of the same water. Each reads 1000 kg/m³; so does the parcel they compose,
which is what intensivity says and all it says. The pair is then a *checked* instance of
the exclusion: a kind that is constant under composition cannot also be additive, on pain
of `1000 = 2000`. -/

/-- Mass density, a ratio kind. -/
def fluidDensity : KindOfProperty := { id := "mass density", scale := .ratio }

/-- A density measurement over parcels of one homogeneous fluid: every part, and every
composition of parts, reads 1000 kg/m³. -/
def densityHomogeneous : Measurement System := fun _ =>
  { kind := fluidDensity, numeral := 1000, reference := "kg/m³" }

/-- One parcel of water, as an atomic part. -/
def waterParcelA : Decomposition System := .atom { id := "1 L water (A)" }
/-- A second parcel of the same water. -/
def waterParcelB : Decomposition System := .atom { id := "1 L water (B)" }

/-- **Density is intensive.** Both fields hold by `rfl` on this measurement: the kind is
fixed, and a union of two parts reading alike reads alike. -/
theorem densityHomogeneous_intensive : Intensive fluidDensity densityHomogeneous :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

/-- **And therefore not extensive.** Two parcels at the same nonzero density refute
additivity — the two 1 L parcels compose to water at 1000 kg/m³, not 2000. -/
theorem density_not_extensive : ¬ Extensive fluidDensity densityHomogeneous :=
  not_extensive_of_intensive densityHomogeneous_intensive
    (a := waterParcelA) (b := waterParcelB) rfl (by decide)

/-! ## Witness — a normal-mode frequency is whole-proper

Two identical oscillators, each with angular frequency ω₀ = 10 rad/s, coupled so that the
upper normal mode sits at ω₊ = 14 rad/s (ω₊² = ω₀² + 2κ/m = 100 + 96). The pair's reading is
neither the sum of the parts' (20) nor their common value (10) — and there is nothing else
for it to be, because a lone oscillator has no normal mode. Both refutations are `decide`,
so the third branch of §13.5 is occupied by a checked witness rather than by an argument. -/

/-- Angular frequency, a ratio kind — the *generic* kind the parts and the whole share. What
distinguishes the pair's reading is its dedication (*"coupled oscillator pair — normal mode +
; angular frequency"*), not the kind-of-property, which is why the failure below is a fact
about aggregation and not about commensurability. -/
def oscillatorFrequency : KindOfProperty := { id := "angular frequency", scale := .ratio }

/-- One oscillator of the pair. -/
def oscillatorA : Decomposition System := .atom { id := "oscillator A" }
/-- The other oscillator of the pair. -/
def oscillatorB : Decomposition System := .atom { id := "oscillator B" }

/-- The frequency measurement of the coupled pair: each oscillator alone reads ω₀ = 10 rad/s,
the pair reads its upper normal mode ω₊ = 14 rad/s. -/
def normalModeFreq : Measurement System
  | .atom _ => { kind := oscillatorFrequency, numeral := 10, reference := "rad/s" }
  | .union _ _ => { kind := oscillatorFrequency, numeral := 14, reference := "rad/s" }

/-- **The pair's normal-mode frequency is whole-proper.** 14 is not 10 + 10, and 14 is not
the parts' shared 10: the value belongs to the pair and is inherited from neither part. -/
theorem normalMode_wholeProper : WholeProper oscillatorFrequency normalModeFreq :=
  { ofKind := fun d => by cases d <;> rfl
    notAdditive := ⟨{ id := "oscillator A" }, { id := "oscillator B" }, by decide⟩
    notUniform := ⟨{ id := "oscillator A" }, { id := "oscillator B" }, by decide, by decide⟩ }

/-- Summing the parts would report 20 rad/s for a pair whose mode is at 14 — the wrong
number, exhibited on the carving that produces it. -/
theorem normalMode_leafSum_wrong :
    (normalModeFreq (.union oscillatorA oscillatorB)).numeral
      ≠ leafSum normalModeFreq (.union oscillatorA oscillatorB) := by decide

end PropertyKindCalculus
