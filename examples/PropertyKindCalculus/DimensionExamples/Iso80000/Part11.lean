/-
# Worked examples — ISO 80000-11 (Characteristic numbers)

Part-11 examples, mirroring the `Iso80000` library's own `Iso80000/Part11` layout. This
is the part where the *dimension does not classify the kind* thesis is total:

1. **one dimension, 115 kinds** — every characteristic number is dimension one, so the
   dimension functor collapses the entire part to a single point;
2. **the sub-suffixed homonyms (requirement R2)** — the two Froude numbers, the five
   Stokes numbers, and the four Bejan numbers as distinct kinds **sharing a name**,
   individuated by their *measurement principle* (the examination principle), not by
   dimension and not by name;
3. **one unit symbol, many kinds** — every characteristic number has coherent unit `"1"`,
   yet two are *not commensurable* (different kinds);
4. **the dimension-one collision capstone** — distinct standard kinds at dimension one;
5. **references to parts not yet specified** — the work-to-go split (ISO 80000-8, -9, -12);
6. **catalogue coverage** — all 115 items carry their source as data.

Series-wide catalogue examples are in the sibling
`PropertyKindCalculus.DimensionExamples.Iso80000.References`.
-/

module

public import PropertyKindCalculus.Iso80000
meta import PropertyKindCalculus.Iso80000
public import PropertyKindCalculus.QuantityReal
meta import PropertyKindCalculus.QuantityReal

@[expose] public section Blanket

namespace PropertyKindCalculus.Examples.Iso80000.Part11

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open PropertyKindCalculus.Iso80000.Part11

/-! ## (1) One dimension, 115 kinds — the widest collapse in the series

Every characteristic number is dimension one: the Reynolds number (inertial / viscous),
the Mach number (flow speed / sound speed), the Prandtl number (momentum / thermal
diffusivity), all of them. The dimension cannot tell any two of them apart. -/

example : reynolds.dim = 1 := rfl
example : mach.dim = 1 := rfl
example : prandtl.dim = 1 := rfl
example : hartmann.dim = 1 := rfl
-- by construction, every characteristic number is dimension one …
example (ctx : Part11.Context) (id principle : String) :
    (charNum ctx id principle).dim = 1 := charNum_dim_one ctx id principle
-- … and so is every member of the catalogue.
example : ∀ c ∈ Part11.catalogue, c.qk.dim = 1 := catalogue_all_dim_one

-- the measurement principle is recorded as the examination principle (context : ratio).
#guard reynolds.kind.examPrinciple == some "momentum-transfer: inertial forces / viscous forces"
#guard prandtl.kind.examPrinciple == some "constants-of-matter: kinematic viscosity / thermal diffusivity"

/-! ## (2) The sub-suffixed homonyms — same name, distinct kind (requirement R2)

ISO 80000-11 reuses one name across its transport clauses, distinguishing the variants
only by a symbol suffix and a different defining ratio. Each is a distinct kind, told
apart **by its measurement principle alone** — proved via `distinct_of_examPrinciple`,
not by `id` strings (the names are identical). -/

-- (a) THE TWO FROUDE NUMBERS share a name and a dimension, yet are distinct kinds.
example : froudeMomentum.kind.id = froudeHeat.kind.id := froudeMomentum_id_eq_froudeHeat
example : froudeMomentum.dim = froudeHeat.dim := rfl
example : froudeMomentum.kind ≠ froudeHeat.kind := froudeMomentum_ne_froudeHeat

-- (b) THE FIVE STOKES NUMBERS (`Stk`, `Stk₁` … `Stk₄`) are pairwise distinct kinds.
example :
    stokesPlasma.kind ≠ stokesVibrating.kind ∧
    stokesVibrating.kind ≠ stokesRotameter.kind ∧
    stokesRotameter.kind ≠ stokesGravity.kind ∧
    stokesGravity.kind ≠ stokesDrag.kind ∧
    stokesPlasma.kind ≠ stokesDrag.kind := stokes_pairwise_distinct

-- (c) THE FOUR BEJAN NUMBERS — even the two heat-transfer ones (sharing name *and*
--     transport context) differ by measurement principle.
example :
    bejanMomentum.kind ≠ bejanHeat.kind ∧
    bejanHeat.kind ≠ bejanEntropy.kind ∧
    bejanEntropy.kind ≠ bejanMass.kind ∧
    bejanMomentum.kind ≠ bejanMass.kind := bejan_four_distinct

-- (d) the Fourier and Nusselt numbers recur across heat / mass transfer as distinct kinds.
example : fourierHeat.kind ≠ fourierMass.kind := fourierHeat_ne_fourierMass
example : nusseltHeat.kind ≠ nusseltMass.kind := nusseltHeat_ne_nusseltMass

/-! ## (3) One unit symbol, many kinds

Every characteristic number has the same coherent unit symbol, `"1"` — yet two are not
commensurable. The shared symbol does not make a Reynolds number a Euler number. -/

example : reynoldsUnit.WellFormed := reynoldsUnit_wellFormed
example : ¬ reynoldsUnit.Commensurable eulerUnit := reynolds_euler_not_commensurable

-- a Reynolds number bears values: the laminar–turbulent transition near `Re = 2300` (at Int).
#guard (⟨2300⟩ : Quantity reynolds.kind Int).magnitude == 2300

/-! ## (4) The dimension-one collision capstone — R1 at its widest -/

example : reynolds.kind ≠ euler.kind := reynolds_ne_euler
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  iso80000_11_dim_one_collision

/-! ## (5) References to other parts — now all specified

ISO 80000-11's definitions name quantities from other parts. With parts 8, 9, and 12 now
mapped, **every** referenced part is specified and the work-to-go list is empty. -/

-- the referenced parts split exactly into specified ++ work-to-go.
example : referencedParts = specifiedReferencedParts ++ workToGoParts :=
  referencedParts_partition
-- the work-to-go list is now EMPTY — every referenced part is mapped.
#guard workToGoParts.map (·.part) == []
example : referencedParts = specifiedReferencedParts := referencedParts_all_specified
-- the referenced (and now all-specified) parts are 3, 4, 5, 6, 7, 8, 9, 12.
#guard specifiedReferencedParts.map (·.part) == [3, 4, 5, 6, 7, 8, 9, 12]

/-! ## (6) Catalogue coverage — all 115 items carry their source as data -/

-- every ISO 80000-11 item is catalogued, in item order …
#guard Part11.catalogue.length == 115
example : Part11.catalogue.length = 115 := catalogue_length
-- … with the item designations (first and last, spanning clauses 4 … 9) …
#guard Part11.catalogue.head?.map (·.item) == some "11-4.1"
#guard Part11.catalogue.head?.map (·.symbol) == some "Re"
#guard Part11.catalogue.getLast?.map (·.item) == some "11-9.2"
-- … each citing its full source …
#guard Part11.catalogue.head?.map (·.cite) ==
  some "ISO 80000-11, Second edition, 2019-10 item 11-4.1"
-- … and recording the coherent SI unit symbol `"1"` for every one (all dimension one).
#guard Part11.catalogue.all (·.coherentUnit == "1")

end PropertyKindCalculus.Examples.Iso80000.Part11

end Blanket
