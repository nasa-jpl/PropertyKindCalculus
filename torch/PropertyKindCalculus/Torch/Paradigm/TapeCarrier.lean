/-
`paradigm.tape_carrier` — the **tape carrier** `TapeBuilder s`, the `[NumCarrier]` instance
that lets a WO1 kernel (written *once* over `[NumCarrier α]`) be instantiated at `α := Tape`
and *build a batched tensor program* (plan milestone **WO3**, README §3.2).

THE IDEA. `dielectric.lean`'s ε kernel is polymorphic over `[NumCarrier α]`. At `α := Float`
it computes one pixel's scalar ε; at `α := ℝ`/binary32 it carries the proof/rounding
certificates. WO3 adds *one more carrier* — a value that, instead of being a number, is a
**thunk that appends its sub-expression to a TorchLean autograd `Tape` and returns the
result node id**. Interpreting the same kernel at this carrier *builds the batched GPU
kernel* — no hand transcription (`dielectric_batch.lean`), parity by construction.

  `TapeBuilder s := { run : TapeM Float Nat }`  — a deferred tensor sub-program of shape `s`.

Every `NumCarrier` operation is realised purely: `x + y` is the *thunk* that runs `x`, runs
`y`, and emits one `TapeM.add` node — a total function `TapeBuilder s → TapeBuilder s →
TapeBuilder s`, exactly the `Add` interface. Because `NumCarrier` carries **no
ordering-to-`Bool`** (§`num_carrier`), a kernel over it cannot ask for a data-dependent
branch, so every op it *can* name has a single fused-elementwise tape realisation — which is
precisely why the instantiation lowers to one kernel.

WHAT THE TAPE BACKEND LACKS. The elementwise tape surface (WO2 audit) has
`add/sub/mul/div/scale/min/max/relu` and the unary `abs/sqrt/exp/log` — everything the
*collapsible-Mironov* ε fragment uses (it needs only `sqrt` + the constant `pi` beyond
arithmetic and `min`/`max`). It has **no** `sin/cos/tanh/cosh/sinh` on either backend; those
`MathFunctions` fields are filled with an honest "unsupported on the tape backend" thunk that
errors *if run*. The Mironov ε kernel never runs them (the Fresnel incidence `sin`/`cos` are
pixel-invariant host scalars, computed off-tape), so the instantiation is total in practice.

No sharing/CSE here: a sub-expression named twice (`n·n`) emits its node twice. That is
*value*-correct (both copies compute the same tensor); de-duplication is the WO3 memoizing-
tape stretch, an optimisation orthogonal to parity.

A `module` file: imports the `num_carrier` capability and TorchLean's `TapeM` builder.
-/

module

public import PropertyKindCalculus.Paradigm.NumCarrier
public import PropertyKindCalculus.Torch.Paradigm.NumCarrierContext
public import NN.Runtime.Autograd.Engine.TapeM

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open Spec TorchLean
open TorchLean TorchLean.Tensor
open Runtime.Autograd

namespace PropertyKindCalculus.Paradigm

/-- **The tape carrier.** A `TapeBuilder s` is a deferred tensor sub-program over the pixel
batch shape `s`: running it inside `TapeM` appends its nodes to the autograd `Tape` and
returns the id of its result tensor. The underlying tensor carrier is `Float` (the
executable tape). A WO1 kernel instantiated at `α := TapeBuilder s` *is* the batched kernel. -/
structure TapeBuilder (s : Shape) where
  /-- The deferred build action: emit this sub-expression's nodes, yield its result id. -/
  run : TapeM Float Nat

namespace TapeBuilder

variable {s : Shape}

/-- A constant tensor leaf filled with the host scalar `x` (shape `s`). Constants of the
kernel (coefficients, `0`/`1`, `Nat` literals, `pi`) enter the tape this way. -/
def const (x : Float) : TapeBuilder s := ⟨TapeM.leaf (Tensor.full s x) (name := none)⟩

/-- A `MathFunctions` field with no tape realisation on either backend (`sin/cos/tanh/…`):
an honest error if ever run. The collapsible-Mironov ε kernel never names these. -/
def unsupported (op : String) : TapeBuilder s :=
  ⟨throw s!"TapeBuilder: `{op}` has no elementwise tape op (absent on CPU & CUDA backends); \
    the collapsible Mironov ε kernel does not use it"⟩

/-- Lift a binary tape op into the carrier: run both operands, emit one node. Public so the
WO3 parity proofs (`paradigm.tape_parity`) can unfold the carrier's arithmetic op-by-op. -/
@[inline] def bin (f : Nat → Nat → TapeM Float Nat) (x y : TapeBuilder s) : TapeBuilder s :=
  ⟨do let a ← x.run; let b ← y.run; f a b⟩

/-- Lift a unary tape op into the carrier: run the operand, emit one node. -/
@[inline] def un (f : Nat → TapeM Float Nat) (x : TapeBuilder s) : TapeBuilder s :=
  ⟨do let a ← x.run; f a⟩

instance : Zero (TapeBuilder s) := ⟨const 0⟩
instance : One (TapeBuilder s) := ⟨const 1⟩
instance : Add (TapeBuilder s) := ⟨bin (TapeM.add (s := s))⟩
instance : Sub (TapeBuilder s) := ⟨bin (TapeM.sub (s := s))⟩
instance : Mul (TapeBuilder s) := ⟨bin (TapeM.mul (s := s))⟩
instance : Div (TapeBuilder s) := ⟨bin (TapeM.div (s := s))⟩
instance : Min (TapeBuilder s) := ⟨bin (TapeM.min (s := s))⟩
instance : Max (TapeBuilder s) := ⟨bin (TapeM.max (s := s))⟩
/-- `Nat` literals enter as constant leaves — the same `Float` value `ofN n` produces at
`α := Float` (`(n : Float)` via the shared `Coe Nat Float`), so parity is preserved. -/
instance : Coe Nat (TapeBuilder s) := ⟨fun n => const ((n : Float))⟩

/-- The transcendental surface at the tape carrier. `exp/log/abs/sqrt` are real tape ops and
`pi` a constant leaf; `sin/cos/tanh/cosh/sinh` are tape-absent (see `unsupported`). -/
instance : MathFunctions (TapeBuilder s) where
  exp  := un (TapeM.exp  (s := s))
  log  := un (TapeM.log  (s := s))
  abs  := un (TapeM.abs  (s := s))
  sqrt := un (TapeM.sqrt (s := s))
  pi   := const MathFunctions.pi
  sin  := fun _ => unsupported "sin"
  cos  := fun _ => unsupported "cos"
  tanh := fun _ => unsupported "tanh"
  cosh := fun _ => unsupported "cosh"
  sinh := fun _ => unsupported "sinh"

/-- **The tape carrier is a `NumCarrier`** — every branchless numeric capability realised as a
deferred tensor sub-program. A WO1 kernel `[NumCarrier α] → …` therefore instantiates at
`α := TapeBuilder s` to *build* the batched tensor program. There is no `Context` instance
(no ordering-to-`Bool`), so this does not collide with `instNumCarrierOfContext`. -/
instance instNumCarrier : NumCarrier (TapeBuilder s) where

end TapeBuilder

end PropertyKindCalculus.Paradigm

end -- pkc-blanket-expose
end -- pkc-blanket
