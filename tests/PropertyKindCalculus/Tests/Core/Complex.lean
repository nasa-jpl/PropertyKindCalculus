/-
# Validation probes — the complexified carrier (`Quantity k (Complex R)`)

Complex-ness is a property of the **carrier**, not of the kind: a complex permittivity is
one kind of quantity whose value happens to be complex, not two real quantities of a "real
part kind" and an "imaginary part kind". The two probes below are what that commits the
library to. Taking a part changes the carrier and leaves the kind alone, so `Quantity.re`
and `Quantity.im` take no witness — there is no kind equation to check. And they exist as
named operations for a reason a type cannot state: written inline, a part is an anonymous
`⟨z.magnitude.re⟩`, which a boundary audit reads as a mint — a quantity conjured from a
bare number — standing where a carrier operation belongs.
-/
import PropertyKindCalculus.Complex

namespace PropertyKindCalculus.Tests.Complex

open PropertyKindCalculus

/-- A probe kind whose values are complex — a relative permittivity in miniature. -/
def epsK : KindOfProperty := { id := "complex probe permittivity", scale := .ratio }

/-- A complex-carried quantity at that kind. -/
def probeEps : Quantity epsK (PropertyKindCalculus.Complex Int) := ⟨⟨5, -2⟩⟩

-- The part is at the SAME kind: this typechecks with no witness and no cast.
example : Quantity epsK Int := probeEps.re
example : Quantity epsK Int := probeEps.im

#guard probeEps.re.magnitude == 5
#guard probeEps.im.magnitude == -2

-- and the `@[simp]` bridges are definitional, so the analysis of a part runs on the
-- carrier arithmetic without a rewriting step of its own
example : probeEps.re.magnitude = probeEps.magnitude.re := rfl
example : probeEps.im.magnitude = probeEps.magnitude.im := rfl

end PropertyKindCalculus.Tests.Complex
