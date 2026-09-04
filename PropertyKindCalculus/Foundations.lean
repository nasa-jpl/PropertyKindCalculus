/-
# Foundations — system and object

Dybkær, *An Ontology on Property for Physical, Chemical, and Biological Systems*
(2009), Chapter 3.
-/

namespace PropertyKindCalculus

universe u

/-- **§3.3 system** — "part or phenomenon of the perceivable or conceivable
world consisting of a demarcated arrangement of a set of elements and a set of
relationships or processes between these elements."

Specified abstractly by identity here; the mereological structure needed for
extensivity (§13.5) is added in a later module. -/
structure System where
  /-- Terminological identity of the system/object (mirrors the OML `id`). -/
  id : String
deriving DecidableEq, Repr

/-- **§3.3 Note 6** — 'object' is given as a synonym of 'system'. We keep the
synonym so that the *instance* layer can read as "characterizes an object". -/
abbrev Object := System

/-! ## What an object type has to supply

`System` above is the **nominal** object type: an object *is* its terminological identity,
so naming one and telling two apart are the same act. That is the right reading for a
sample, an instrument, a rover — and it is not the only reading a host library offers. A
particle of a mechanical system, a cell of a mesh, a pixel of a scene are objects whose
identity is a *position in a structure*, with no name stored anywhere.

The instance layer (`IndividualQuantity`) is therefore parameterized over the object type,
and the parameterization splits its obligations in two:

  * **discrimination** — telling two objects apart. Every type in Lean already does this,
    definitionally, which is why the object *gate* needs no class and costs nothing to
    carry to a foreign object type.
  * **designation** — naming an object in the terminological vocabulary, which is what
    `IndividualProperty` (Ch. 3) and the §20 dedicated kind consume. This is *not* free,
    and `Designated` below is where an object type supplies it.

The nominal type supplies both; a structural one supplies only the first, and honestly
saying so is the point of separating them. -/

/-- **An object type with terminological identity.** A map from the object type into the
nominal `Object`, so an individual property can name the object it characterizes (§3.3,
Ch. 20) whatever the object type is.

The injectivity field is the whole content of the class. Without it, an author facing a
structural object type — physlib's particles, a mesh cell — can always satisfy the class by
sending every object to one constant name, and the resulting designation is *worse than
none*: it type-checks, it renders, and it silently reports two distinct objects as the same
system. With it, a type whose objects carry no identity simply has no instance, which is
the true answer and is the one a reader should get. -/
class Designated (O : Type u) where
  /-- The nominal designation of an object. -/
  designation : O → Object
  /-- **Distinct objects are distinctly named.** A designation that collapses two objects
  is not a designation; this is what makes the instance a claim rather than a formality. -/
  designation_inj : ∀ {x y : O}, designation x = designation y → x = y

/-- **The nominal object type designates itself** — the existing API is the instance, and
`Object` is one inhabitant of the parameterization rather than the only object type there
is. Injectivity is reflexivity: for a nominal object, the name *is* the identity. -/
instance : Designated Object where
  designation o := o
  designation_inj h := h

end PropertyKindCalculus
