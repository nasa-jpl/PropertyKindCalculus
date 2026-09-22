/-
`PropertyKindCalculus.Paradigm.NumCarrier` — `NumCarrier α`, the **branchless numeric
capability**.

A scalar interface bundling exactly the operations that have a *batchable, elementwise*
realisation: arithmetic (`+ − × ÷`), the lattice selectors `min`/`max` (and `relu` derived
from them), the transcendental surface (PKC's `MathCarrier`: `sqrt`/`exp`/`log`/`sin`/…), the
constants `0`/`1`, and the `Nat → α` embedding for structural literals.

WHAT IT DELIBERATELY OMITS — and why that is the point. `NumCarrier` carries **no
ordering-to-`Bool`**: no `decide (x > y)`, no `BEq`/`LT`/`LE`. A kernel written against
`NumCarrier` therefore *cannot* express a data-dependent branch on its inputs — every
conditional must be re-expressed with the branchless selectors `min`/`max`/`relu`. That
restriction is exactly the property a fused elementwise backend needs: **"typechecks against
`NumCarrier`" ⟹ "lowers to one elementwise kernel, no per-element control flow."** The same
source then interprets at the proof carrier (`ℝ`), the rounding-spec carrier (binary32), and
the executable carrier (`Float`) without a per-carrier copy, and — in the `Torch` library — at
a recording tape carrier for GPU execution.

`NumCarrier` *extends* PKC's `MathCarrier`, so the kind-tracked function calculus
(`Quantity.sqrt`/`exp`/…) rides on a `[NumCarrier α]` kernel directly: `MathCarrier α` is the
free parent projection `NumCarrier.toMathCarrier`, with no bridge instance. Because
`MathCarrier` is itself field-identical to TorchLean's `MathFunctions`, the TorchLean coupling
— every `Context` is a `NumCarrier` — lives one layer out in the `Torch` library
(`PropertyKindCalculus.Torch.Paradigm.NumCarrierContext`), so this core class is Mathlib- and
TorchLean-free.
-/

module

public import PropertyKindCalculus.QuantityFunction

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Paradigm

/-- **The branchless numeric capability.** Bundles arithmetic, the lattice selectors
`min`/`max`, PKC's transcendental surface `MathCarrier`, the constants `0`/`1`, and the
`Nat → α` embedding — *without* any ordering-to-`Bool`. A kernel over `[NumCarrier α]` is
branchless by construction, hence lowers to a single fused elementwise kernel; and because it
*extends* `MathCarrier`, the kind-tracked function calculus instantiates over it directly. -/
class NumCarrier (α : Type) extends
  Zero α, One α, Add α, Sub α, Mul α, Div α, Min α, Max α,
  MathCarrier α, Coe Nat α

/-- **Every `NumCarrier` is a `ScalarCarrier`.** The defining property above is that a kernel
over `[NumCarrier α]` lowers to a *single fused elementwise kernel* — so whatever `α`'s lanes
are, they are independent, and `α`'s `*` is the multiplication of magnitudes lane by lane.
That is exactly the claim `ScalarCarrier` records, which is why the batch carriers qualify
(`N` samples of one scalar quantity) while a numerical-array carrier holding the `n`
*components of one* vector quantity does not — the latter is not a `NumCarrier` either, for
the same reason. Low priority so a carrier that states the claim directly still wins. -/
instance (priority := low) numCarrierIsScalar {α : Type} [NumCarrier α] : ScalarCarrier α := ⟨⟩

/-- ReLU as the branchless `max x 0` — the rectifier the moisture-mixing collapse uses for the
free-water increment `max(mv − m_vt, 0)`. -/
def NumCarrier.relu {α : Type} [NumCarrier α] (x : α) : α := Max.max x 0

end PropertyKindCalculus.Paradigm

end -- pkc-blanket-expose
end -- pkc-blanket
