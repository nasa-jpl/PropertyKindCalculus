/-
`Tests.Dimension.ExaminationCoverage` — the indexed probe for `#kind_examination_coverage`
(the census behind the model template's M6) and its gate.

One probe world, every verdict class exercised, the full report pinned:

  * `[individuated]` — a dimension-one kind carrying an `examPrinciple`;
  * `⊘ exempted` — a dimension-one kind marked `@[kindPrincipleFree "…"]`, listed with its
    reason and NOT gated on;
  * `⚠ UNINDIVIDUATED` — a dimension-one kind with neither: the finding;
  * a dimensioned kind (`L`) with no principle, which must NOT appear — it is outside M6's
    population (a kind the dimension functor already separates);
  * a marked kind that *also* carries a principle, which must report `[individuated]` — the
    mark is inert where an individuation exists, so a stale exemption cannot hide one.
  * a bare `KindOfProperty` no `DimensionedKind` wraps, reported `⚠ UNDIMENSIONED` — the
    census cannot decide it and must not pass over it — beside one a `DimensionedKind` does
    wrap, which must appear once, decided through its wrapper, and never as undimensioned.

Then the gate: it throws on the probe world (one unindividuated kind), and passes silently on
a sub-namespace holding only individuated and exempted kinds — an exemption is not a
violation and must not fire it. Finally the attribute's own refusals: a mark on something
that is not a `DimensionedKind`, and a mark with an empty reason.
-/

module

public import PropertyKindCalculus.ExaminationCoverage
meta import PropertyKindCalculus.ExaminationCoverage

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Tests.Dimension.Examination

open PropertyKindCalculus

/-! ## The probe world -/

/-- Dimension one, individuated by a principle. -/
def probeIndividuated : DimensionedKind :=
  { kind := { id := "probe individuated", scale := .ratio, examPrinciple := some "probe-principle" },
    dim := 1 }

/-- Dimension one, no principle, no mark: the finding. -/
def probeBare : DimensionedKind :=
  { kind := { id := "probe bare", scale := .ratio }, dim := 1 }

/-- Dimension one, no principle, exempted with a reason. -/
@[kindPrincipleFree "the wave calculus's own geometry, the product of no phenomenon"]
def probeGeometry : DimensionedKind :=
  { kind := { id := "probe geometry", scale := .ratio }, dim := 1 }

/-- Dimension one, a principle AND a (stale) mark: the principle wins. -/
@[kindPrincipleFree "stale — this kind has since been individuated"]
def probeStaleMark : DimensionedKind :=
  { kind := { id := "probe stale mark", scale := .ratio, examPrinciple := some "later-principle" },
    dim := 1 }

/-- Dimension `L`, no principle: outside the population, must not appear. -/
def probeLength : DimensionedKind :=
  { kind := { id := "probe length", scale := .ratio }, dim := Dim.length }

/-- A bare `KindOfProperty` no `DimensionedKind` wraps: the census cannot decide it, and says
so — `UNDIMENSIONED`, a violation, never silence. -/
def probeBareKind : KindOfProperty := { id := "probe bare kind", scale := .ratio }

/-- A bare `KindOfProperty` that a `DimensionedKind` below does wrap: not undimensioned, and
decided through its wrapper like any other. -/
def probeWrappedKind : KindOfProperty :=
  { id := "probe wrapped kind", scale := .ratio, examPrinciple := some "wrapped-principle" }

/-- The wrapper, dimension one: individuated through the constant it names. -/
def probeWrapped : DimensionedKind := { kind := probeWrappedKind, dim := 1 }

/-! ## The pinned report -/

/--
info: examination coverage:
[individuated] PropertyKindCalculus.Tests.Dimension.Examination.probeIndividuated (probe individuated) — principle: probe-principle
[individuated] PropertyKindCalculus.Tests.Dimension.Examination.probeStaleMark (probe stale mark) — principle: later-principle
[individuated] PropertyKindCalculus.Tests.Dimension.Examination.probeWrapped (probe wrapped kind) — principle: wrapped-principle
⊘ exempted PropertyKindCalculus.Tests.Dimension.Examination.probeGeometry (probe geometry) — the wave calculus's own geometry, the product of no phenomenon
⚠ UNDIMENSIONED PropertyKindCalculus.Tests.Dimension.Examination.probeBareKind (probe bare kind) — no DimensionedKind wraps it
⚠ UNINDIVIDUATED PropertyKindCalculus.Tests.Dimension.Examination.probeBare (probe bare)
5 dimension-one kind(s): 3 individuated, 1 exempted, 1 UNINDIVIDUATED; 1 kind(s) UNDIMENSIONED — examination-coverage violation
-/
#guard_msgs (whitespace := lax) in
#kind_examination_coverage PropertyKindCalculus.Tests.Dimension.Examination

/-! ## `#kind_examination_clean` — the invariant, which cannot be re-blessed -/

/--
error: examination coverage: 2 kind(s) not individuated or not dimensioned — examination-coverage violation
  ⚠ UNDIMENSIONED PropertyKindCalculus.Tests.Dimension.Examination.probeBareKind (probe bare kind) — no DimensionedKind wraps it
  ⚠ UNINDIVIDUATED PropertyKindCalculus.Tests.Dimension.Examination.probeBare (probe bare)

Inside the dimension-one fiber the examination principle is the only defining aspect that separates two kinds. Give each UNINDIVIDUATED kind its `examPrinciple`, or — where it is correctly principle-free (a geometry vocabulary, a nominal designation, a bookkeeping fraction) — mark its declaration `@[kindPrincipleFree "reason"]` so the exemption is data the sweep can read. Give each UNDIMENSIONED kind a `DimensionedKind` declaring its dimension (M10): until then this census cannot place it in or out of the dimension-one fiber, and a gate that passed over it would pass over nothing. Do NOT re-pin a `#kind_examination_coverage` report whose summary says `violation` — that turns the build green and the census off.
-/
#guard_msgs (whitespace := lax) in
#kind_examination_clean PropertyKindCalculus.Tests.Dimension.Examination

/-! A namespace holding only individuated and exempted kinds: the gate passes silently. The
exempted kind is the point — an exemption is not a violation and must not fire it. -/
namespace Clean

/-- Individuated. -/
def cleanIndividuated : DimensionedKind :=
  { kind := { id := "clean individuated", scale := .ratio, examPrinciple := some "clean-principle" },
    dim := 1 }

/-- Exempted. -/
@[kindPrincipleFree "a nominal designation, compared for equality and nothing else"]
def cleanNominal : DimensionedKind :=
  { kind := { id := "clean nominal", scale := .nominal }, dim := 1 }

end Clean

-- no message: every dimension-one kind under `Clean` is individuated or exempted
#guard_msgs in
#kind_examination_clean PropertyKindCalculus.Tests.Dimension.Examination.Clean

/-! ## The attribute's own refusals -/

/-- Not a `DimensionedKind`. -/
def notAKind : Nat := 0

/--
error: `@[kindPrincipleFree]` expects a 'DimensionedKind' — 'PropertyKindCalculus.Tests.Dimension.Examination.notAKind' is not one. The mark exempts a dimension-one kind from the examination-coverage sweep, and dimension is a fact about the DimensionedKind, so that is where the mark goes.
-/
#guard_msgs (whitespace := lax) in
attribute [kindPrincipleFree "misplaced"] notAKind

/--
error: `@[kindPrincipleFree]` on 'PropertyKindCalculus.Tests.Dimension.Examination.probeBare' needs a reason: an exemption without one is the docstring problem in a new place
-/
#guard_msgs (whitespace := lax) in
attribute [kindPrincipleFree "  "] probeBare

end PropertyKindCalculus.Tests.Dimension.Examination

end -- pkc-blanket-expose
end -- pkc-blanket
