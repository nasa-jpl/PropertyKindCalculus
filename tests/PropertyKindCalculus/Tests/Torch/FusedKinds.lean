/-
# Validation probes — the kinded fused forms (`Quantity.scaledProdExp`)

Inhabitation, boundary, and axiom-profile probes for the kind layer over the fused
forms (`PropertyKindCalculus.Torch.Paradigm.FusedKinds`). Driven at a host stub carrier
(`HostT s := Float`, with the composed `Float.exp (c * x * y)` as its "fused" kernel)
so the probes *compute*:

  * the kinded fused op evaluates, and its magnitude is bit-identical (`==`) to the
    naked composed spelling of the same left-associated shape;
  * erasure to the naked `FusedExp.scaledProdExp` call is definitional (`rfl`);
  * swapping the two batch operands is a *type* error whenever their kinds differ —
    the compile-time guarantee the naked fused op cannot give.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.FusedKinds
meta import PropertyKindCalculus.Torch.Paradigm.FusedKinds

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.FusedKinds

open Spec TorchLean
open PropertyKindCalculus
open PropertyKindCalculus.Paradigm (FusedExp)

/-- A host stub batch carrier — every batch is one `Float` — so the probes evaluate in
`#guard` without a device. -/
abbrev HostT (_s : Shape) : Type := Float

/-- The stub's "fused" kernel is the composed shape itself, left-associated — the
bit-exactness contract of `FusedExp` made trivially true. -/
instance : FusedExp HostT := ⟨fun c x y => Float.exp (c * x * y)⟩

/-- Extinction coefficient (Beer–Lambert `κ`), a ratio kind. -/
def kappaK : KindOfProperty := { id := "extinction-coefficient", scale := .ratio }
/-- Path length, a ratio kind. -/
def pathK : KindOfProperty := { id := "path-length", scale := .ratio }
/-- Dimension one, a ratio kind — the exponent and the transmittance. -/
def dimlessK : KindOfProperty := { id := "dimensionless", scale := .ratio }

/-- `(−2)·κ` stays an extinction coefficient. -/
theorem hcx : ProductKind dimlessK kappaK kappaK := ProductKind.ofRatio _ _ _
/-- `κ·ℓ` is the dimension-one exponent. -/
theorem hcxy : ProductKind kappaK pathK dimlessK := ProductKind.ofRatio _ _ _
/-- `exp` carries the dimension-one exponent to the dimension-one transmittance. -/
theorem hexp : TranscendentalKind dimlessK dimlessK := ⟨rfl, rfl⟩

abbrev s4 : Shape := Shape.dim 4 Shape.scalar

def negTwo : Quantity dimlessK Float := ⟨-2.0⟩
def kappa : Quantity kappaK (HostT s4) := ⟨0.5⟩
def ell : Quantity pathK (HostT s4) := ⟨2.0⟩

-- Inhabitation: the kinded fused op evaluates at the stub carrier, bit-identical to the
-- naked composed spelling of the same left-associated shape `exp((−2·κ)·ℓ)`.
#guard (Quantity.scaledProdExp hcx hcxy hexp negTwo kappa ell).magnitude
    == Float.exp (-2.0 * 0.5 * 2.0)

-- Erasure is definitional: the kinded op *is* the naked fused call on magnitudes.
example : (Quantity.scaledProdExp hcx hcxy hexp negTwo kappa ell).magnitude
    = FusedExp.scaledProdExp (C := HostT) (-2.0) kappa.magnitude ell.magnitude := rfl

-- Boundary (Rule 2): the batch operands cannot swap — `ℓ` where `κ` is expected is a
-- *type* error, exactly the argument-transposition hazard the naked
-- `FusedExp.scaledProdExp (b ndvi : C s)` interface cannot catch.
#check_failure (Quantity.scaledProdExp hcx hcxy hexp negTwo ell kappa)

/-- info: 'PropertyKindCalculus.Quantity.scaledProdExp_magnitude' does not depend on any axioms -/
#guard_msgs in #print axioms Quantity.scaledProdExp_magnitude

end PropertyKindCalculus.Tests.FusedKinds

end Blanket
