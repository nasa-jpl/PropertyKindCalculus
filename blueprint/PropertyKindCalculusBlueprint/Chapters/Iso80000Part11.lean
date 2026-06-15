import Verso
import VersoManual
import VersoBlueprint
-- The Part-11 nodes link real declarations (the catalogued characteristic-number kinds,
-- the measurement-principle constructor, the proof that every one is dimension one, the
-- sub-suffixed homonyms distinct by measurement principle, the unit-incommensurability,
-- the dimension-one collision capstone, and the work-to-go references), so this chapter
-- imports the Part-11 module of the `Iso80000` library.
import PropertyKindCalculus.Iso80000.Part11

open Verso.Genre
open Verso.Genre.Manual
open Informal

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

:::definition "def_part11_catalogued_kind" (parent := "iso80000_part11") (lean := "PropertyKindCalculus.Iso80000.Part11.CataloguedKind")
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

:::table +header (align := left)
*
  * Item
  * Characteristic number
  * Symbol
  * Measurement principle (dimension one)
*
  * {bpref "thm_part11_collision"}[11-4.1]
  * Reynolds number
  * `Re`
  * inertial forces / viscous forces
*
  * {bpref "thm_part11_collision"}[11-4.2]
  * Euler number
  * `Eu`
  * pressure drop / kinetic energy per volume
*
  * {bpref "thm_part11_homonym"}[11-4.3]
  * Froude number
  * `Fr`
  * inertial forces / gravitational forces
*
  * {bpref "thm_part11_all_dim_one"}[11-4.4]
  * Grashof number
  * `Gr`
  * thermal buoyancy forces / viscous forces
*
  * {bpref "thm_part11_all_dim_one"}[11-4.5]
  * Weber number
  * `We`
  * inertial forces / surface-tension forces
*
  * {bpref "thm_part11_all_dim_one"}[11-4.6]
  * Mach number
  * `Ma`
  * speed of flow / speed of sound
*
  * {bpref "thm_part11_all_dim_one"}[11-4.7]
  * Knudsen number
  * `Kn`
  * mean free path / characteristic length
*
  * {bpref "thm_part11_all_dim_one"}[11-4.8]
  * Strouhal number
  * `Sr`
  * characteristic frequency / characteristic speed
*
  * {bpref "thm_part11_all_dim_one"}[11-4.9]
  * drag coefficient
  * `c_D`
  * drag force / inertial force
*
  * {bpref "thm_part11_all_dim_one"}[11-4.10]
  * Bagnold number
  * `Bg`
  * drag and gravitational force / inertial force
*
  * {bpref "thm_part11_all_dim_one"}[11-4.11]
  * Bagnold number
  * `Ba₂`
  * drag force / viscous force, solid particles
*
  * {bpref "thm_part11_all_dim_one"}[11-4.12]
  * lift coefficient
  * `c_l`
  * lift force / inertial force
*
  * {bpref "thm_part11_all_dim_one"}[11-4.13]
  * thrust coefficient
  * `c_t`
  * thrust force / inertial force
*
  * {bpref "thm_part11_all_dim_one"}[11-4.14]
  * Dean number
  * `Dn`
  * centrifugal force / inertial force, curved pipe
*
  * {bpref "thm_part11_bejan"}[11-4.15]
  * Bejan number
  * `Be`
  * mechanical work / frictional energy loss
*
  * {bpref "thm_part11_all_dim_one"}[11-4.16]
  * Lagrange number
  * `Lg`
  * mechanical work / frictional energy loss, Lagrange form
*
  * {bpref "thm_part11_all_dim_one"}[11-4.17]
  * Bingham number
  * `Bm`
  * yield stress / viscous stress
*
  * {bpref "thm_part11_all_dim_one"}[11-4.18]
  * Hedström number
  * `He`
  * yield stress / viscous stress, at flow limit
*
  * {bpref "thm_part11_all_dim_one"}[11-4.19]
  * Bodenstein number
  * `Bd`
  * convective / diffusive matter transfer
*
  * {bpref "thm_part11_all_dim_one"}[11-4.20]
  * Rossby number
  * `Ro`
  * inertial forces / Coriolis forces
*
  * {bpref "thm_part11_all_dim_one"}[11-4.21]
  * Ekman number
  * `Ek`
  * viscous forces / Coriolis forces
*
  * {bpref "thm_part11_all_dim_one"}[11-4.22]
  * elasticity number
  * `El`
  * relaxation time / diffusion time
*
  * {bpref "thm_part11_all_dim_one"}[11-4.23]
  * Darcy friction factor
  * `f_D`
  * pressure loss / pipe-wall friction
*
  * {bpref "thm_part11_all_dim_one"}[11-4.24]
  * Fanning number
  * `f_F`
  * wall shear stress / dynamic pressure
*
  * {bpref "thm_part11_all_dim_one"}[11-4.25]
  * Goertler number
  * `Go`
  * centrifugal effects / viscous effects, boundary layer
*
  * {bpref "thm_part11_all_dim_one"}[11-4.26]
  * Hagen number
  * `Hg`
  * pressure-gradient force / viscous force
*
  * {bpref "thm_part11_all_dim_one"}[11-4.27]
  * Laval number
  * `La`
  * flow speed / critical sound speed, nozzle throat
*
  * {bpref "thm_part11_all_dim_one"}[11-4.28]
  * Poiseuille number
  * `Poi`
  * pressure force / viscous force, pipe flow
*
  * {bpref "thm_part11_all_dim_one"}[11-4.29]
  * power number
  * `Ne`
  * agitator power / inertial power
*
  * {bpref "thm_part11_all_dim_one"}[11-4.30]
  * Richardson number
  * `Ri`
  * potential energy / kinetic energy
*
  * {bpref "thm_part11_all_dim_one"}[11-4.31]
  * Reech number
  * `Re_e`
  * object speed / wave speed, submerged
*
  * {bpref "thm_part11_stokes"}[11-4.32]
  * Stokes number
  * `Stk`
  * friction force / inertial force, particles in flow
*
  * {bpref "thm_part11_stokes"}[11-4.33]
  * Stokes number
  * `Stk₁`
  * friction force / inertial force, vibrating particles
*
  * {bpref "thm_part11_stokes"}[11-4.34]
  * Stokes number
  * `Stk₂`
  * drag / inertia, rotameter calibration
*
  * {bpref "thm_part11_stokes"}[11-4.35]
  * Stokes number
  * `Stk₃`
  * viscous force / gravity force, settling particles
*
  * {bpref "thm_part11_stokes"}[11-4.36]
  * Stokes number
  * `Stk₄`
  * drag force / internal friction force, particles
*
  * {bpref "thm_part11_all_dim_one"}[11-4.37]
  * Laplace number
  * `La`
  * capillary force / viscous force, free surface
*
  * {bpref "thm_part11_all_dim_one"}[11-4.38]
  * Blake number
  * `Bl`
  * inertial force / viscous force, porous medium
*
  * {bpref "thm_part11_all_dim_one"}[11-4.39]
  * Sommerfeld number
  * `So`
  * viscous force / load force, lubrication
*
  * {bpref "thm_part11_all_dim_one"}[11-4.40]
  * Taylor number
  * `Ta`
  * centrifugal force / viscous force, rotating flow
*
  * {bpref "thm_part11_all_dim_one"}[11-4.41]
  * Galilei number
  * `Ga`
  * gravitational force / viscous force, fluid film
*
  * {bpref "thm_part11_all_dim_one"}[11-4.42]
  * Womersley number
  * `Wo`
  * inertial forces / viscous forces, oscillating flow
*
  * {bpref "thm_part11_homonym"}[11-5.1]
  * Fourier number
  * `Fo`
  * heat conduction rate / thermal storage rate
*
  * {bpref "thm_part11_all_dim_one"}[11-5.2]
  * Péclet number
  * `Pe`
  * convective / conductive heat transfer rate
*
  * {bpref "thm_part11_all_dim_one"}[11-5.3]
  * Rayleigh number
  * `Ra`
  * thermal buoyancy forces / viscous forces, free convection
*
  * {bpref "thm_part11_homonym"}[11-5.4]
  * Froude number
  * `Fr*`
  * gravitational forces / thermodiffusion forces
*
  * {bpref "thm_part11_homonym"}[11-5.5]
  * Nusselt number
  * `Nu`
  * convective / conductive heat transfer at a surface
*
  * {bpref "thm_part11_all_dim_one"}[11-5.6]
  * Biot number
  * `Bi`
  * internal / surface thermal resistance
*
  * {bpref "thm_part11_all_dim_one"}[11-5.7]
  * Stanton number
  * `St`
  * wall heat transfer / fluid heat-capacity flow
*
  * {bpref "thm_part11_all_dim_one"}[11-5.8]
  * j-factor
  * `j`
  * heat transfer / mass transfer, Colburn analogy
*
  * {bpref "thm_part11_bejan"}[11-5.9]
  * Bejan number
  * `Be₁`
  * mechanical work / frictional and thermal-diffusion losses
*
  * {bpref "thm_part11_bejan"}[11-5.10]
  * Bejan number
  * `Be_S`
  * heat-transfer efficiency / entropy generation
*
  * {bpref "thm_part11_all_dim_one"}[11-5.11]
  * Stefan number
  * `Ste`
  * sensible heat / latent heat, phase change
*
  * {bpref "thm_part11_all_dim_one"}[11-5.12]
  * Brinkman number
  * `Br`
  * viscous heat production / wall heat conduction
*
  * {bpref "thm_part11_all_dim_one"}[11-5.13]
  * Clausius number
  * `Cl`
  * kinetic energy transfer / thermal conduction
*
  * {bpref "thm_part11_all_dim_one"}[11-5.14]
  * Carnot number
  * `Ca`
  * maximum thermodynamic (Carnot) efficiency
*
  * {bpref "thm_part11_all_dim_one"}[11-5.15]
  * Eckert number
  * `Ec`
  * kinetic energy / enthalpy difference
*
  * {bpref "thm_part11_all_dim_one"}[11-5.16]
  * Graetz number
  * `Gz`
  * convective / conductive heat, laminar pipe
*
  * {bpref "thm_part11_all_dim_one"}[11-5.17]
  * heat transfer number
  * `K_Q`
  * heat flow / kinetic energy of flow
*
  * {bpref "thm_part11_all_dim_one"}[11-5.18]
  * Pomerantsev number
  * `Po`
  * generated heat / conducted heat in a body
*
  * {bpref "thm_part11_all_dim_one"}[11-5.19]
  * Boltzmann number
  * `Bz`
  * convective heat / radiant heat
*
  * {bpref "thm_part11_all_dim_one"}[11-5.20]
  * Stark number
  * `Sk`
  * radiant heat / conductive heat
*
  * {bpref "thm_part11_homonym"}[11-6.1]
  * Fourier number
  * `Fo*`
  * diffusive mass transfer / storage rate
*
  * {bpref "thm_part11_all_dim_one"}[11-6.2]
  * Péclet number
  * `Pe*`
  * advective / diffusive mass transfer rate
*
  * {bpref "thm_part11_all_dim_one"}[11-6.3]
  * Grashof number
  * `Gr*`
  * buoyancy forces / viscous forces, natural convection
*
  * {bpref "thm_part11_homonym"}[11-6.4]
  * Nusselt number
  * `Nu*`
  * mass flux / molecular-diffusion flux
*
  * {bpref "thm_part11_all_dim_one"}[11-6.5]
  * Stanton number
  * `St*`
  * perpendicular / parallel surface mass transfer
*
  * {bpref "thm_part11_all_dim_one"}[11-6.6]
  * Graetz number
  * `Gz*`
  * advective / radial diffusive mass transfer
*
  * {bpref "thm_part11_all_dim_one"}[11-6.7]
  * mass transfer factor
  * `j*`
  * interface mass transfer / parallel flux, Chilton-Colburn
*
  * {bpref "thm_part11_all_dim_one"}[11-6.8]
  * Atwood number
  * `At`
  * density difference / density sum, two fluids
*
  * {bpref "thm_part11_all_dim_one"}[11-6.9]
  * Biot number
  * `Bi*`
  * interface / interior mass transfer rate
*
  * {bpref "thm_part11_all_dim_one"}[11-6.10]
  * Morton number
  * `Mo`
  * gravitational forces / viscous forces, bubbles
*
  * {bpref "thm_part11_all_dim_one"}[11-6.11]
  * Bond number
  * `Bo`
  * gravitational and inertial force / capillary force
*
  * {bpref "thm_part11_all_dim_one"}[11-6.12]
  * Archimedes number
  * `Ar`
  * buoyancy forces / viscous forces, density difference
*
  * {bpref "thm_part11_all_dim_one"}[11-6.13]
  * expansion number
  * `Ex`
  * buoyancy force / inertial force, rising bubbles
*
  * {bpref "thm_part11_all_dim_one"}[11-6.14]
  * Marangoni number
  * `Mg`
  * surface-tension convection / thermal diffusion
*
  * {bpref "thm_part11_all_dim_one"}[11-6.15]
  * Lockhart-Martinelli parameter
  * `Lp`
  * two-phase mass-flow-rate ratio by density
*
  * {bpref "thm_part11_bejan"}[11-6.16]
  * Bejan number
  * `Be*`
  * mechanical work / frictional and diffusion losses
*
  * {bpref "thm_part11_all_dim_one"}[11-6.17]
  * cavitation number
  * `Ca`
  * static-vapour head / dynamic head
*
  * {bpref "thm_part11_all_dim_one"}[11-6.18]
  * absorption number
  * `Ab`
  * mass flow rate / surface area, gas absorption
*
  * {bpref "thm_part11_all_dim_one"}[11-6.19]
  * capillary number
  * `Ca`
  * gravitational forces / capillary forces
*
  * {bpref "thm_part11_all_dim_one"}[11-6.20]
  * dynamic capillary number
  * `Ca*`
  * viscous force / capillary force, interface
*
  * {bpref "thm_part11_all_dim_one"}[11-7.1]
  * Prandtl number
  * `Pr`
  * kinematic viscosity / thermal diffusivity
*
  * {bpref "thm_part11_all_dim_one"}[11-7.2]
  * Schmidt number
  * `Sc`
  * kinematic viscosity / diffusion coefficient
*
  * {bpref "thm_part11_all_dim_one"}[11-7.3]
  * Lewis number
  * `Le`
  * thermal diffusivity / diffusion coefficient
*
  * {bpref "thm_part11_all_dim_one"}[11-7.4]
  * Ohnesorge number
  * `Oh`
  * viscous force / root of inertia times capillary force
*
  * {bpref "thm_part11_all_dim_one"}[11-7.5]
  * Cauchy number
  * `Cy`
  * inertia forces / compression forces
*
  * {bpref "thm_part11_all_dim_one"}[11-7.6]
  * Hooke number
  * `Ho₂`
  * inertia forces / linear-stress forces
*
  * {bpref "thm_part11_all_dim_one"}[11-7.7]
  * Weissenberg number
  * `Wi`
  * shear rate times relaxation time
*
  * {bpref "thm_part11_all_dim_one"}[11-7.8]
  * Deborah number
  * `De`
  * relaxation time / observation time
*
  * {bpref "thm_part11_all_dim_one"}[11-7.9]
  * Lorentz number
  * `Lo`
  * electrical conductivity / thermal conductivity
*
  * {bpref "thm_part11_all_dim_one"}[11-7.10]
  * compressibility number
  * `Z`
  * real-gas / ideal-gas compressibility factor
*
  * {bpref "thm_part11_all_dim_one"}[11-8.1]
  * Reynolds magnetic number
  * `Rm`
  * inertial force / magneto-dynamic viscous force
*
  * {bpref "thm_part11_all_dim_one"}[11-8.2]
  * Batchelor number
  * `Bt`
  * inertia / magneto-dynamic diffusion
*
  * {bpref "thm_part11_all_dim_one"}[11-8.3]
  * Nusselt electric number
  * `Ne_e`
  * convective / diffusive ion current
*
  * {bpref "thm_part11_all_dim_one"}[11-8.4]
  * Alfvén number
  * `Al`
  * flow speed / Alfvén wave speed
*
  * {bpref "thm_part11_all_dim_one"}[11-8.5]
  * Hartmann number
  * `Ha`
  * magnetically induced stress / viscous force
*
  * {bpref "thm_part11_all_dim_one"}[11-8.6]
  * Cowling number
  * `Co`
  * magnetic / kinematic energy density
*
  * {bpref "thm_part11_all_dim_one"}[11-8.7]
  * Stuart electrical number
  * `Se`
  * electric / kinematic energy density
*
  * {bpref "thm_part11_all_dim_one"}[11-8.8]
  * magnetic pressure number
  * `N_mp`
  * gas pressure / magnetic pressure
*
  * {bpref "thm_part11_all_dim_one"}[11-8.9]
  * Chandrasekhar number
  * `Q`
  * Lorentz force / viscous force
*
  * {bpref "thm_part11_all_dim_one"}[11-8.10]
  * Prandtl magnetic number
  * `Pr_m`
  * kinematic viscosity / magnetic viscosity
*
  * {bpref "thm_part11_all_dim_one"}[11-8.11]
  * Roberts number
  * `Ro_m`
  * thermal diffusivity / magnetic viscosity
*
  * {bpref "thm_part11_all_dim_one"}[11-8.12]
  * Stuart number
  * `N_St`
  * magnetic force / inertial force
*
  * {bpref "thm_part11_all_dim_one"}[11-8.13]
  * magnetic number
  * `N_mg`
  * magnetic body force / viscous force
*
  * {bpref "thm_part11_all_dim_one"}[11-8.14]
  * electric field parameter
  * `E_f`
  * Coulomb force / Lorentz force
*
  * {bpref "thm_part11_all_dim_one"}[11-8.15]
  * Hall number
  * `Hl`
  * gyrofrequency / collision frequency
*
  * {bpref "thm_part11_all_dim_one"}[11-8.16]
  * Lundquist number
  * `Lu`
  * Alfvén speed / magneto-dynamic diffusion speed
*
  * {bpref "thm_part11_all_dim_one"}[11-8.17]
  * Joule magnetic number
  * `Jo_m`
  * Joule heating / magnetic field energy
*
  * {bpref "thm_part11_all_dim_one"}[11-8.18]
  * Grashof magnetic number
  * `Gr_m`
  * thermo-magnetic buoyancy / viscous force
*
  * {bpref "thm_part11_all_dim_one"}[11-8.19]
  * Naze number
  * `Na`
  * Alfvén wave speed / sound speed
*
  * {bpref "thm_part11_all_dim_one"}[11-8.20]
  * Reynolds electric number
  * `Re_e`
  * fluid speed / charged-particle drift speed
*
  * {bpref "thm_part11_all_dim_one"}[11-8.21]
  * Ampère number
  * `Am`
  * electric surface current / magnetic field
*
  * {bpref "thm_part11_all_dim_one"}[11-9.1]
  * Arrhenius number
  * `α`
  * chemical activation energy / thermal energy
*
  * {bpref "thm_part11_all_dim_one"}[11-9.2]
  * Landau-Ginzburg number
  * `κ`
  * penetration depth / coherence length
:::
