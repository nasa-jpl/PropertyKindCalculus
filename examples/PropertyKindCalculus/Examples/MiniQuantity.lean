/-
# Worked examples — the representation-parametric quantity (R10)

Checked facts exercising `Quantity k R`: the *same* kind-indexed value layer
instantiated at two carriers, the additivity laws transferring for free to the
lawful one, the executable carrier actually running, and the kind index gating
addition. The third (proof) carrier `ℝ` lives with the `Dimension` library
(`PropertyKindCalculus.QuantityReal`), since it needs Mathlib.
-/

module

public import PropertyKindCalculus.Quantity
meta import PropertyKindCalculus.Quantity

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Examples.MiniQuantity

open PropertyKindCalculus

/-! ## Two kinds, one value layer

`length` and `mass` are distinct kinds; quantities of each are *different types*. -/

def length : KindOfProperty := { id := "length", scale := .ratio }
def mass : KindOfProperty := { id := "mass", scale := .ratio }

/-- Both kinds are ratio-scale, so each is a `DifferenceKind` — the comparability
witness `Quantity.add` requires. Supplied explicitly here, the gate stays visible. -/
theorem hLen : DifferenceKind length := .ofScale
theorem hMass : DifferenceKind mass := .ofScale

/-! ## The `Int` carrier: lawful, so the additivity laws hold for free -/

def lenA : Quantity length Int := ⟨3⟩
def lenB : Quantity length Int := ⟨5⟩

/-- Addition adds magnitudes within the kind. -/
example : (Quantity.add hLen lenA lenB).magnitude = 8 := by decide

/-- Commutativity, proved once over any lawful carrier, specialized to `Int`. -/
example (x y : Quantity length Int) :
    Quantity.add hLen x y = Quantity.add hLen y x := Quantity.add_comm hLen x y

/-- Associativity, likewise. -/
example (x y z : Quantity length Int) :
    Quantity.add hLen (Quantity.add hLen x y) z
      = Quantity.add hLen x (Quantity.add hLen y z) := Quantity.add_assoc hLen x y z

/-- The zero quantity is a unit. -/
example (x : Quantity length Int) :
    Quantity.add hLen Quantity.zero x = x := Quantity.zero_add hLen x

/-! ## The `Float` carrier: the *executable* representation

The identical `Quantity` layer at `R := Float` actually runs. -/

def lenF : Quantity length Float := ⟨3.0⟩

-- The magnitude reduces — execution, not just specification (`3.0 + 0.5 = 3.5`).
#guard (Quantity.add hLen lenF ⟨0.5⟩).magnitude == 3.5

-- A `Quantity Float` value computes (prints `3.500000`):
#eval (Quantity.add hLen lenF ⟨0.5⟩).magnitude

/- `Float` is a `Carrier` but **not** a `LawfulCarrier`: floating-point addition
is not associative, so the additivity laws are unavailable at `Float`. The next
line is therefore a *type error* (no `LawfulCarrier Float` instance) — exactly
the gap the planned exec/spec refinement bridge (R10) closes:

    example (x y : Quantity length Float) : x.add y = y.add x := Quantity.add_comm x y
-/

/-! ## Kind-gated addition (R4)

`Quantity.add : DifferenceKind k → Quantity k R → Quantity k R → Quantity k R`
forces both summands to share the kind `k` (and to be a kind whose scale admits
differences — the `DifferenceKind k` witness, here `hLen`). -/

def massA : Quantity mass Int := ⟨2⟩

/-- Adding two lengths is well-typed. -/
example : (Quantity.add hLen lenA lenB).magnitude = 8 := by decide

/- Adding a length to a mass is a *type error*, not a runtime check —
`massA : Quantity mass Int` cannot be a summand where a `Quantity length Int` is
expected:

    #check lenA.add massA   -- type error: kind `mass` ≠ kind `length`

The same source, kept honest by the kind index. -/

/-- The mass quantity, for its part, computes on its own. -/
example : massA.magnitude = 2 := by decide

end PropertyKindCalculus.Examples.MiniQuantity

end -- pkc-blanket-expose
end -- pkc-blanket
