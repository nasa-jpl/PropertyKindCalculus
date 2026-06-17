import Verso
import VersoManual
import VersoBlueprint
-- The Part-11 nodes link real declarations (the catalogued characteristic-number kinds,
-- the measurement-principle constructor, the proof that every one is dimension one, the
-- sub-suffixed homonyms distinct by measurement principle, the unit-incommensurability,
-- the dimension-one collision capstone, and the work-to-go references), so this chapter
-- imports the Part-11 module of the `Iso80000` library.
import PropertyKindCalculus.Iso80000.Part11
import PropertyKindCalculusBlueprint.ItemIndex

open Verso.Genre
open Verso.Genre.Manual
open Informal

open PropertyKindCalculusBlueprint.ItemIndex

/-- Default blueprint node for ISO/IEC 80000-11 item-index rows (editorial). -/
def part11Default : String := "thm_part11_all_dim_one"

/-- Per-item blueprint cross-reference overrides for the ISO/IEC 80000-11 item
index (editorial; items not listed link to `part11Default`). Every other column
is generated from `PropertyKindCalculus.Iso80000.Part11.catalogue`. -/
def part11Refs : List (String × String) := [
  ("11-4.1", "thm_part11_collision"),
  ("11-4.2", "thm_part11_collision"),
  ("11-4.3", "thm_part11_homonym"),
  ("11-4.15", "thm_part11_bejan"),
  ("11-4.32", "thm_part11_stokes"),
  ("11-4.33", "thm_part11_stokes"),
  ("11-4.34", "thm_part11_stokes"),
  ("11-4.35", "thm_part11_stokes"),
  ("11-4.36", "thm_part11_stokes"),
  ("11-5.1", "thm_part11_homonym"),
  ("11-5.4", "thm_part11_homonym"),
  ("11-5.5", "thm_part11_homonym"),
  ("11-5.9", "thm_part11_bejan"),
  ("11-5.10", "thm_part11_bejan"),
  ("11-6.1", "thm_part11_homonym"),
  ("11-6.4", "thm_part11_homonym"),
  ("11-6.16", "thm_part11_bejan")
]

/-- The ISO/IEC 80000-11 item index, generated live from the catalogue. -/
def part11IndexTable : DocTable :=
  characteristicNumberIndex PropertyKindCalculus.Iso80000.Part11.catalogue part11Default part11Refs

#doc (Manual) "ISO 80000-11 — Characteristic numbers" =>

The sixth part specified is ISO 80000-11, _Characteristic numbers_ — and it is where the
_dimension does not classify the kind_ thesis (_R1_) becomes _total_. Every item is
catalogued: all 115 of items 11-4.1 … 11-9.2, across the six clauses — momentum transfer
(the Reynolds, Euler, Froude, Mach, Knudsen, … numbers), transfer of heat (Fourier,
Péclet, Rayleigh, Nusselt, Biot, …), transfer of matter in a binary mixture (the
mass-transfer analogues), constants of matter (Prandtl, Schmidt, Lewis, …),
magnetohydrodynamics (the magnetic and electric numbers), and miscellaneous — each
carrying its exact source as data: the part, the printed item designation, the principal
quantity symbol, and the coherent SI unit symbol. Only _citation locators_ are recorded;
no normative content from the licensed standard is reproduced.

A characteristic number is a _dimensionless_ ratio. So *every one of the 115 is dimension
one*: the dimension functor sends the Reynolds number (inertial / viscous forces), the
Mach number (flow speed / sound speed), and the Prandtl number (momentum / thermal
diffusivity) all to the _single point_ `1`. A dimension-only model sees one type — "a real
number" — for the entire part and cannot tell any two of its 115 members apart. What keeps
them apart is their _measurement principle_: the physical ratio each one expresses, carried
as an examination principle (requirement _R2_). This is the pattern Part 3 set on the length family, Part 4 on the
force family, Part 7 on the radiation trios — here at its widest, over a part with _no_
dimensional variation at all.

# Quantity-kinds of ISO 80000-11 — one dimension, 115 kinds

:::group "iso80000_part11"
Each catalogued kind reuses the {uses "def_dim"}[dimension functor] `dim` over PhysLib's
`Dimension`, but here every kind maps to the same value, dimension one. The distinguishing
datum is moved entirely onto the {uses "def_examination"}[examination principle] — the
measurement principle, this work's terse descriptor of the defining ratio, paired with the
transport-phenomena context (the clause). Each kind still bears values and a coherent unit
(`1` for all); commensurability is a type-level fact, so two characteristic numbers with
the _same_ unit symbol `1` are still not interchangeable.
:::

:::definition "def_part11_catalogued_kind" (parent := "iso80000_part11") (lean := "PropertyKindCalculus.Iso80000.CataloguedKind")
A _catalogued kind_ pairs a dimensioned {uses "def_quantity"}[quantity]-kind with its
exact source in the series — the part, the printed item designation (e.g. "11-4.1"), the
principal quantity symbol (e.g. `Re`), and the coherent SI unit symbol (`1` for every
characteristic number). The citation travels with the kind as data, so the source of each
definition can be rendered or audited downstream.
:::

:::proof "def_part11_catalogued_kind"
Realized as `structure CataloguedKind` over a `DimensionedKind`, with `cite` rendering e.g.
`ISO 80000-11, Second edition, 2019-10 item 11-4.1`. The `catalogue` lists all 115 items
in item order across clauses 4 … 9; `catalogue_length : catalogue.length = 115` checks the
count.
:::

:::definition "def_part11_char_number" (parent := "iso80000_part11") (lean := "PropertyKindCalculus.Iso80000.Part11.charNum")
A _characteristic number_ is a ratio-scale {uses "def_quantity"}[quantity]-kind of
_dimension one_, individuated by its {uses "def_examination"}[examination principle] —
the _measurement principle_, formed as `context: defining-ratio`. The context is one of
ISO 80000-11's six clauses (momentum transfer, heat transfer, mass transfer, constants of
matter, magnetohydrodynamics, miscellaneous); it is part of the principle because the same
ratio name recurs across clauses as a _different_ kind.
:::

:::proof "def_part11_char_number"
`charNum ctx id principle := { kind := { id, scale := .ratio, examPrinciple := some
(ctx.id ++ ": " ++ principle) }, dim := Dim.one }`, with the clause `Context` an
enumeration (`momentum`, `heat`, `mass`, `constants`, `mhd`, `misc`). Every kind in the
part is built by this one constructor.
:::

:::theorem "thm_part11_all_dim_one" (parent := "iso80000_part11") (lean := "PropertyKindCalculus.Iso80000.Part11.catalogue_all_dim_one") (tags := "proved") (effort := "small")
*Every characteristic number is dimension one — the widest collapse in the series.* All
115 catalogued kinds share the dimensionless dimension; the {uses "def_dim"}[dimension
functor] collapses the entire part to one point. What distinguishes them is the
measurement principle, never the dimension. Uses {uses "def_dim"}[the dimension map].
:::

:::proof "thm_part11_all_dim_one"
`catalogue_all_dim_one : ∀ c ∈ catalogue, c.qk.dim = 1`, by `fin_cases` over the catalogue
then reflexivity (each entry is a `charNum` application, whose `dim` is `Dim.one` by
construction — `charNum_dim_one`). Axiom-free.
:::

# The sub-suffixed homonyms — same name, distinct kind

ISO 80000-11 reuses one name across its transport-phenomena clauses, distinguishing the
variants only by a symbol suffix and a different defining ratio. The Froude number appears
as 11-4.3 (`Fr`, momentum) and 11-5.4 (`Fr*`, heat); the Fourier, Péclet, Grashof,
Nusselt, Stanton, Graetz and Biot numbers each as a heat (`Fo`, …) and a mass (`Fo*`, …)
member; the Bejan number _four_ times; and the Stokes number _five_ times (`Stk`, `Stk₁` …
`Stk₄`). These are the sub-suffixed quantity kinds — and they are the sharpest form of
_R2_ in the whole series: a member shares its name _and_ its dimension (one) with its
siblings, so neither the name nor the dimension can tell them apart. Only the measurement
principle can.

:::group "iso80000_part11_homonyms"
The homonym families are individuated by the {uses "def_examination"}[examination
principle] alone — `distinct_of_examPrinciple`, not the `id` strings, which are equal.
Every characteristic number has the same coherent unit symbol `1`, so the unit cannot tell
them apart either; yet two are not commensurable, because they reference different kinds.
:::

:::theorem "thm_part11_homonym" (parent := "iso80000_part11_homonyms") (lean := "PropertyKindCalculus.Iso80000.Part11.froudeMomentum_ne_froudeHeat") (tags := "proved") (effort := "small")
*The two Froude numbers are distinct kinds — by measurement principle, not by name.* Both
are named "Froude number" and both are dimension one (11-4.3, `Fr`, momentum transfer;
11-5.4, `Fr*`, heat transfer), yet they isolate different physical ratios —
inertial/gravitational versus gravitational/thermodiffusion forces — so the calculus
proves them distinct from their differing principles. The Fourier (11-5.1, 11-6.1) and
Nusselt (11-5.5, 11-6.4) numbers recur likewise. Uses {uses "def_examination"}[the
examination principle].
:::

:::proof "thm_part11_homonym"
`froudeMomentum_ne_froudeHeat : froudeMomentum.kind ≠ froudeHeat.kind`, from
`KindOfProperty.distinct_of_examPrinciple` on the differing principles
`momentum-transfer: …` and `heat-transfer: …`; `froudeMomentum_id_eq_froudeHeat` checks
the names _are_ equal. The companions `fourierHeat_ne_fourierMass` and
`nusseltHeat_ne_nusseltMass` cover the other recurring pairs. Axiom-free.
:::

:::theorem "thm_part11_stokes" (parent := "iso80000_part11_homonyms") (lean := "PropertyKindCalculus.Iso80000.Part11.stokes_pairwise_distinct") (tags := "proved") (effort := "small")
*The five Stokes numbers are pairwise distinct kinds.* All five (11-4.32 … 11-4.36) carry
the name "Stokes number" and dimension one, distinguished only by symbol suffix (`Stk`,
`Stk₁` … `Stk₄`) and the measurement principle each isolates — friction/inertia for
particles in flow, for vibrating particles, rotameter calibration, viscous/gravity for
settling particles, drag/internal-friction. Uses {uses "def_examination"}[the examination
principle].
:::

:::proof "thm_part11_stokes"
`stokes_pairwise_distinct`, a conjunction of five `distinct_of_examPrinciple` applications
on the differing principles. Axiom-free.
:::

:::theorem "thm_part11_bejan" (parent := "iso80000_part11_homonyms") (lean := "PropertyKindCalculus.Iso80000.Part11.bejan_four_distinct") (tags := "proved") (effort := "small")
*The four Bejan numbers are distinct kinds — even two sharing a transport context.* The
momentum (11-4.15), the two heat (11-5.9, 11-5.10) and the mass (11-6.16) Bejan numbers
are four kinds. The two heat-transfer ones share name _and_ context, and differ only in
the measurement principle (mechanical-work/diffusion-losses versus heat-transfer
efficiency by entropy generation) — the finest distinction the calculus draws in this part.
Uses {uses "def_examination"}[the examination principle].
:::

:::proof "thm_part11_bejan"
`bejan_four_distinct`, a conjunction of four `distinct_of_examPrinciple` applications.
Axiom-free.
:::

:::theorem "thm_part11_commensurable" (parent := "iso80000_part11_homonyms") (lean := "PropertyKindCalculus.Iso80000.Part11.reynolds_euler_not_commensurable") (tags := "proved") (effort := "small")
*One unit symbol, many kinds.* The Reynolds and Euler units are not commensurable, though
both carry the coherent unit symbol `1` and dimension one. Same symbol, same dimension,
different kind — so a value of one cannot be read as a value of the other. The kind layer
keeps them apart where the unit symbol and the dimension cannot. Uses
{uses "def_metrologicalUnit"}[the metrological unit].
:::

:::proof "thm_part11_commensurable"
`reynolds_euler_not_commensurable : ¬ reynoldsUnit.Commensurable eulerUnit`, by unfolding
`Commensurable` (equality of the referenced kinds) and `decide`;
`reynoldsUnit_wellFormed` checks the unit is well-formed (a ratio-scale kind bears a unit).
Axiom-free.
:::

# Dimension does not classify; the measurement principle does

:::group "iso80000_part11_collision"
This is the dimension-disambiguation capstone, on _standard_ quantities, and the most
extreme in the series: _every_ kind in the part collides on dimension one. The
{uses "def_dim"}[dimension map] sees a single type; the kind layer, through the
{uses "def_examination"}[measurement principle], keeps 115 distinct members apart.
:::

:::theorem "thm_part11_collision" (parent := "iso80000_part11_collision") (lean := "PropertyKindCalculus.Iso80000.Part11.iso80000_11_dim_one_collision") (tags := "capstone, proved") (effort := "small") (priority := "high")
*The dimension-one collision, on the standard — total, the widest in the series.* There
exist distinct ISO 80000-11 kinds with the same dimension one — the Reynolds and Euler
numbers witness it, alongside _all_ 113 others. No dimension-only type system can separate
any two characteristic numbers; the kind layer, through the measurement principle (R2),
holds the entire part apart. This is _dimension does not classify the kind_ (R1) at its
absolute limit. Uses {uses "def_dim"}[the dimension map] and {uses "def_examination"}[the
examination principle].
:::

:::proof "thm_part11_collision"
`iso80000_11_dim_one_collision : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim
∧ a.dim = 1`, witnessed by `⟨reynolds, euler, reynolds_ne_euler, rfl, rfl⟩`. Axiom-free.
:::

# References to other parts — specified versus work-to-go

The definitions of these characteristic numbers name quantities from other parts of the
80000 series. Some of those parts this library has already specified; others it leans on
but has _not_ yet mapped — and those are recorded as _work-to-go_, so the dependency is
explicit rather than silent.

:::group "iso80000_part11_refs"
The referenced parts split exactly into the specified ones (ISO 80000-3, -4, -5, IEC
80000-6, ISO 80000-7) and the work-to-go ones. The split is a checked fact, not a comment.
:::

:::definition "def_part11_worktogo" (parent := "iso80000_part11_refs") (lean := "PropertyKindCalculus.Iso80000.Part11.workToGoParts")
The _work-to-go_ references are the parts ISO 80000-11 leans on that this library has not
yet specified: ISO 80000-8 _Acoustics_ (the speed of sound, for the Mach number), ISO
80000-9 _Physical chemistry and molecular physics_ (diffusion coefficients, for the
mass-transfer and material-constant numbers), and ISO 80000-12 _Condensed matter physics_
(relaxation times, for the rheological and superconductivity numbers).
:::

:::proof "def_part11_worktogo"
`workToGoParts := [iso80000_8, iso80000_9, iso80000_12]`, with `referencedParts_partition :
referencedParts = specifiedReferencedParts ++ workToGoParts` (`rfl`) and
`workToGoParts_eq_unmapped`, which checks (`decide`) that the work-to-go parts are exactly
the referenced parts whose part number is not among those this library has mapped
(`partIsMapped`, the parts 3, 4, 5, 6, 7).
:::

# Item index — ISO 80000-11

Every catalogued item of ISO 80000-11, indexed by its printed item number, with the
characteristic number's name, the principal quantity symbol, and the _measurement
principle_ — this work's terse descriptor of the defining ratio, which is what individuates
the kind. The coherent SI unit and the PhysLib dimension are `1` for _every_ item, so they
are omitted from the table; that uniformity is exactly the point. Each item number links to
the formalized result it participates in — a homonym distinction, the dimension-one
collision, or the dimension-one theorem itself. Names, symbols, and principle descriptors
are _citation locators_; nothing normative is reproduced.

:::iso_doc_table part11IndexTable
:::
