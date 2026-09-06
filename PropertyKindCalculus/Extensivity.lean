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
measurement uncertainty rather than about the mereology, so it is stated where the
uncertainty is: `PropertyKindCalculus.Uncertainty.QuasiExtensive`, which reads `joins`
below to bound how far a per-join tolerance accumulates over a whole carving, and has
§13.5.1 back as its zero-tolerance case.)

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

The carving itself — `Decomposition`, its fold, its join count, and the leaf-wise
quantifier — is `Mereology.lean`'s, as pure structure with no imports; this module
states the laws over it. A carving is not a census, and every law below is quantified
over all carvings rather than stated for one: a total that depends on how the whole
was cut is not a total, which is why the ∀-quantified form of `extensive_additive`
is the deliverable.
-/

import PropertyKindCalculus.Mereology
import PropertyKindCalculus.PropertyValue

namespace PropertyKindCalculus

universe u

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

/-! ## Extensivity about a shared parameter (§13.5.1, relative to an axis)

Some quantities add only *relative to something the parts must share*: a moment of inertia
about a common axis, a potential energy about a common datum, a position about a common
origin. `Extensive` cannot say this, because a `Measurement` reads a carving and nothing
else — so the parameter is made an explicit argument. What that buys is not a weaker law but
a statable one: `ExtensiveAbout` is `Extensive` at *every* parameter at once, and on top of
it one can say what happens when the parts are read about **different** parameters, which is
the case a library that forgets the axis actually hits.

The correction term is the content. `Transports` says the reading about `a` is the reading
about `b` plus a term determined by the two parameters and the part — the shape of the
parallel-axis theorem, of a change of datum, of a frame shift. The general parallel-axis
instance needs ring normalization over `Int`, which the Mathlib-free core does not have, so
it lives in `PropertyKindCalculus.AggregationLaws`; what is exhibited here is the failure it
corrects, on two point masses. -/

/-- **A measurement taken about a parameter** — an axis, an origin, a datum, a frame. The
parameter is not part of the mereology: it is chosen before the parts are read, and reading
two parts about different choices is exactly what `Transports` below prices. -/
abbrev ParamMeasurement (A : Type) (O : Type u) := A → Measurement O

/-- **§13.5.1 relative to a parameter.** `k` is extensive *about* each value of `A`: fix the
axis and the ordinary additivity law holds. Every parameter at once — which is what makes the
mixed-parameter statement below a statement about this predicate rather than about one
lucky choice. -/
structure ExtensiveAbout {A : Type} {O : Type u} (k : KindOfProperty)
    (m : ParamMeasurement A O) : Prop where
  /-- Every measured part is a value of the kind `k`, about every parameter. -/
  ofKind : ∀ a d, (m a d).kind = k
  /-- The single-split additivity law, at a fixed parameter. -/
  additive : ∀ a d₁ d₂, (m a (.union d₁ d₂)).numeral = (m a d₁).numeral + (m a d₂).numeral

/-- At a fixed parameter it **is** extensivity, so `extensive_additive` applies unchanged and
the whole-tree law comes for free about each axis separately. -/
theorem ExtensiveAbout.at {A : Type} {O : Type u} {k : KindOfProperty}
    {m : ParamMeasurement A O} (h : ExtensiveAbout k m) (a : A) : Extensive k (m a) :=
  ⟨h.ofKind a, h.additive a⟩

/-- **A transport law.** The reading about `a` is the reading about `b` plus a correction
determined by the two parameters and the part. Carrying `corr` as an argument rather than
defining it as the difference is the whole point: a transport law is useful only when the
correction is computable from data the part already carries — for the parallel-axis theorem,
the part's total mass and first moment, both themselves extensive. -/
structure Transports {A : Type} {O : Type u} (m : ParamMeasurement A O)
    (corr : A → A → Decomposition O → Int) : Prop where
  /-- The correction from `b` to `a`, on every part. -/
  transport : ∀ a b d, (m a d).numeral = (m b d).numeral + corr a b d

/-- **Aggregating parts that were read about their own parameters.** The whole about `a` is
the sum of the parts about `a₁` and `a₂`, *each transported* — the general form of "add the
moments of inertia after moving them to a common axis". -/
theorem extensiveAbout_mixed {A : Type} {O : Type u} {k : KindOfProperty}
    {m : ParamMeasurement A O} {corr : A → A → Decomposition O → Int}
    (he : ExtensiveAbout k m) (ht : Transports m corr) (a a₁ a₂ : A)
    (d₁ d₂ : Decomposition O) :
    (m a (.union d₁ d₂)).numeral
      = ((m a₁ d₁).numeral + corr a a₁ d₁) + ((m a₂ d₂).numeral + corr a a₂ d₂) := by
  rw [he.additive a d₁ d₂, ht.transport a a₁ d₁, ht.transport a a₂ d₂]

/-- **And summing them untransported is wrong by exactly the corrections.** Whenever the two
corrections do not cancel, the naive sum of readings taken about different parameters is not
the reading of the whole — the numerical statement of what a type that does not carry the
axis cannot warn about. -/
theorem extensiveAbout_mixed_ne {A : Type} {O : Type u} {k : KindOfProperty}
    {m : ParamMeasurement A O} {corr : A → A → Decomposition O → Int}
    (he : ExtensiveAbout k m) (ht : Transports m corr) {a a₁ a₂ : A}
    {d₁ d₂ : Decomposition O} (hc : corr a a₁ d₁ + corr a a₂ d₂ ≠ 0) :
    (m a (.union d₁ d₂)).numeral ≠ (m a₁ d₁).numeral + (m a₂ d₂).numeral := by
  rw [extensiveAbout_mixed he ht a a₁ a₂ d₁ d₂]
  omega

/-! ### Witness — a moment of inertia is extensive about a common axis

Point masses on a line, each carrying a mass `w` and a position `x`. About a fixed axis `a`
every part contributes `w · (x − a)²` and a union contributes the sum, so the moment of
inertia is extensive about each axis — by `rfl`, the fold's own union case. Read the two
masses of a rod about axes through *themselves*, though, and each contributes nothing while
the rod about its centre reads 2: the mixed-axis sum is wrong, exhibited rather than argued.
The correction that repairs it is the parallel-axis theorem (`AggregationLaws`). -/

/-- The moment of inertia of a system of point masses, a ratio kind. Named for its role
rather than generically, so it does not shadow a host library's own `momentOfInertia`. -/
def pointMassInertia : KindOfProperty := { id := "moment of inertia", scale := .ratio }

/-- **The total of a per-part integer over a carving** — the mass of a part, when `w` is the
mass of a point. Extensive by construction, and one of the two summaries the parallel-axis
correction is built from. -/
def partTotal {O : Type u} (w : O → Int) : Decomposition O → Int :=
  Decomposition.fold w (· + ·)

/-- **The first moment** `∑ wᵢ xᵢ` of a carving — the other summary the parallel-axis
correction is built from, and the one that vanishes about the centre of mass. -/
def firstMoment {O : Type u} (w x : O → Int) : Decomposition O → Int :=
  Decomposition.fold (fun p => w p * x p) (· + ·)

/-- **The moment of inertia about the axis at `a`**: `∑ wᵢ (xᵢ − a)²`, as a fold. -/
def inertiaAbout {O : Type u} (w x : O → Int) (a : Int) : Decomposition O → Int :=
  Decomposition.fold (fun p => w p * ((x p - a) * (x p - a))) (· + ·)

/-- The inertia fold as a `ParamMeasurement`, so the predicates above apply to it. -/
def inertiaMeasurement {O : Type u} (w x : O → Int) : ParamMeasurement Int O := fun a d =>
  { kind := pointMassInertia, numeral := inertiaAbout w x a d, reference := "kg·m²" }

/-- **A moment of inertia is extensive about every axis.** Both fields are `rfl`: additivity
at a fixed axis is the fold's union case, and nothing about the axis enters the proof — which
is why the mixed-axis failure below is a fact about the *parameter*, not about additivity. -/
theorem inertiaMeasurement_extensiveAbout {O : Type u} (w x : O → Int) :
    ExtensiveAbout pointMassInertia (inertiaMeasurement w x) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- A point mass on a line: where it sits, and how much of it there is. -/
structure PointMass where
  /-- The position of the mass along the line, in whole units. -/
  position : Int
  /-- The mass, in whole units. -/
  mass : Int
deriving DecidableEq, Repr

/-- The inertia measurement of point masses, at their own mass and position. -/
abbrev rodInertia : ParamMeasurement Int PointMass :=
  inertiaMeasurement PointMass.mass PointMass.position

/-- One unit mass at `x = −1`. -/
def rodLeft : Decomposition PointMass := .atom { position := -1, mass := 1 }
/-- One unit mass at `x = +1`. -/
def rodRight : Decomposition PointMass := .atom { position := 1, mass := 1 }
/-- The rod, carved into its two masses. -/
def rod : Decomposition PointMass := .union rodLeft rodRight

/-- About its centre the rod reads `1·1 + 1·1 = 2`. -/
theorem rod_inertia_centre : (rodInertia 0 rod).numeral = 2 := by decide

/-- About its left mass it reads `0 + 1·2² = 4` — the same rod, a different number, because
the axis is a different axis. -/
theorem rod_inertia_end : (rodInertia (-1) rod).numeral = 4 := by decide

/-- **Reading each half about an axis through itself gets the rod wrong.** Each mass alone
sits *on* its own axis and contributes nothing, so the untransported sum is 0 where the rod
about its centre reads 2. This is `extensiveAbout_mixed_ne` with an exhibited witness: the
failure is not that inertia fails to add, but that it adds only about a shared axis. -/
theorem rod_mixed_axes_wrong :
    (rodInertia 0 rod).numeral
      ≠ (rodInertia (-1) rodLeft).numeral + (rodInertia 1 rodRight).numeral := by decide

/-! ### The parameter is kind-specific — a momentum is extensive per frame

`ExtensiveAbout` fixes no reading of its parameter: for a moment of inertia it is an axis,
and for a momentum it is a *frame* — the velocity a part's motion is read against. Same
predicate, same failure mode: read each part in its own rest frame and every reading is
zero, so the untransported sum reports a system with no momentum at all. The transport that
repairs it is the Galilean boost (`momentumBoost`, `AggregationLaws`), whose correction is
priced by the carving's mass — the first rung of a tower in which each transport is paid in
a quantity that is itself extensive one rung down: momentum's in mass, angular momentum's in
momentum (`angularMomentumTransport`), the moment of inertia's in mass and first moment
(`parallelAxis`). -/

/-- Linear momentum of a system of point masses, a ratio kind. Role-named as
`pointMassInertia` is, so it does not shadow a host library's own momentum. -/
def pointMassMomentum : KindOfProperty := { id := "linear momentum", scale := .ratio }

/-- **Momentum read in the frame moving at `u`**: `∑ wᵢ (vᵢ − u)`, as a fold. -/
def momentumIn {O : Type u} (w v : O → Int) (u : Int) : Decomposition O → Int :=
  Decomposition.fold (fun p => w p * (v p - u)) (· + ·)

/-- In the frame at rest (`u = 0`) a momentum **is** the first moment of the velocities —
the summary `parallelAxis` prices its correction in, read at velocity instead of position. -/
theorem momentumIn_zero {O : Type u} (w v : O → Int) :
    ∀ d : Decomposition O, momentumIn w v 0 d = firstMoment w v d
  | .atom p => by show w p * (v p - 0) = w p * v p; rw [Int.sub_zero]
  | .union a b => by
      show momentumIn w v 0 a + momentumIn w v 0 b = firstMoment w v a + firstMoment w v b
      rw [momentumIn_zero w v a, momentumIn_zero w v b]

/-- The momentum fold as a `ParamMeasurement` over frames. -/
def momentumMeasurement {O : Type u} (w v : O → Int) : ParamMeasurement Int O := fun u d =>
  { kind := pointMassMomentum, numeral := momentumIn w v u d, reference := "kg·m/s" }

/-- **A momentum is extensive in every frame** — both fields `rfl`, exactly as for the
moment of inertia: nothing about the frame enters the proof, so the mixed-frame failure
below is a fact about the parameter and not about additivity. -/
theorem momentumMeasurement_extensiveAbout {O : Type u} (w v : O → Int) :
    ExtensiveAbout pointMassMomentum (momentumMeasurement w v) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- A point mass in motion along the line. -/
structure MovingPointMass where
  /-- Where it sits. -/
  position : Int
  /-- How fast it moves, read in the laboratory frame. -/
  velocity : Int
  /-- The mass, in whole units. -/
  mass : Int
deriving DecidableEq, Repr

/-- The momentum measurement of moving point masses, at their own mass and velocity. -/
abbrev driftMomentum : ParamMeasurement Int MovingPointMass :=
  momentumMeasurement MovingPointMass.mass MovingPointMass.velocity

/-- One unit mass drifting at `v = 1`. -/
def driftA : Decomposition MovingPointMass :=
  .atom { position := 0, velocity := 1, mass := 1 }
/-- Another unit mass drifting at `v = 2`. -/
def driftB : Decomposition MovingPointMass :=
  .atom { position := 1, velocity := 2, mass := 1 }
/-- The drifting pair. -/
def driftPair : Decomposition MovingPointMass := .union driftA driftB

/-- In the laboratory frame the pair carries momentum 3. -/
theorem drift_momentum_lab : (driftMomentum 0 driftPair).numeral = 3 := by decide

/-- **Reading each mass in its own rest frame loses the pair.** Each part reads zero there,
so the untransported sum reports 0 for a pair the laboratory reads at 3 — inertia's
mixed-axis failure, at a parameter that is a frame rather than an axis. -/
theorem drift_rest_frames_wrong :
    (driftMomentum 0 driftPair).numeral
      ≠ (driftMomentum 1 driftA).numeral + (driftMomentum 2 driftB).numeral := by decide

/-! ### And an angular momentum is extensive per reference point

Planar point masses: a position `(x, y)`, a velocity `(vx, vy)`, and the axial component of
the moment of the motion about a chosen point. The parameter is now a *point*, and the
transport that relates two points is priced by the carving's momentum
(`angularMomentumTransport`, `AggregationLaws`) — zero for a part whose momentum vanishes,
which is why a parked flywheel's spin reads the same about every point and a translating
one's does not. -/

/-- Angular momentum of a system of point masses (the axial component), a ratio kind. -/
def pointMassAngularMomentum : KindOfProperty :=
  { id := "angular momentum", scale := .ratio }

/-- **Angular momentum about the point `c`**: `∑ wᵢ ((xᵢ − c₁)·vyᵢ − (yᵢ − c₂)·vxᵢ)` — the
axial component of `∑ (rᵢ − c) × wᵢvᵢ`, as a fold. -/
def angularMomentumAbout {O : Type u} (w x y vx vy : O → Int) (c : Int × Int) :
    Decomposition O → Int :=
  Decomposition.fold
    (fun p => w p * ((x p - c.1) * vy p - (y p - c.2) * vx p)) (· + ·)

/-- The angular-momentum fold as a `ParamMeasurement` over reference points. -/
def angularMomentumMeasurement {O : Type u} (w x y vx vy : O → Int) :
    ParamMeasurement (Int × Int) O := fun c d =>
  { kind := pointMassAngularMomentum, numeral := angularMomentumAbout w x y vx vy c d,
    reference := "kg·m²/s" }

/-- **An angular momentum is extensive about every reference point** — `rfl` again, so the
whole-tree law holds about each point separately and only the transport between points has
content. -/
theorem angularMomentumMeasurement_extensiveAbout {O : Type u} (w x y vx vy : O → Int) :
    ExtensiveAbout pointMassAngularMomentum (angularMomentumMeasurement w x y vx vy) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

end PropertyKindCalculus
