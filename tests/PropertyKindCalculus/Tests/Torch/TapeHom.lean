/-
# Validation probes — tape-parity as a homomorphism, closed by `tape_hom`

Inhabitation, negative, and axiom-profile probes for `paradigm.tape_hom`
(`PropertyKindCalculus.Torch.Paradigm.TapeHom`): the bundled `Evaluates.isNumCarrierHom`
witness and the `tape_hom` closure tactic.

The worked kernel is the `METROLOGICAL_RIGOR.md` §12.1 toy — one authored kinded form `gQ`
(`x + exp y`) and its naked `.magnitude` derivation `g` — instantiated at the tape carrier
(inputs as leaves) against the eager `Tensor Float s` carrier:

  * **positive** — `g_tape_parity` closes in one `tape_hom [g, gQ]` line: the erase-set names
    `g`/`gQ` only to unfold, and the `Evaluates_*` alphabet closes the exposed `+`/`exp` tree;
  * **negative** — with a deliberately wrong eager right-hand side (`subSpec` where the tree is
    a `+`), `tape_hom` cannot close, so it cannot rubber-stamp a false parity;
  * the bundled `Evaluates.isNumCarrierHom` projections compose the same congruences by hand;
  * axiom profiles are pinned (`#guard_msgs in #print axioms`).

The eager `Tensor Float s` `NumCarrier` instance is set up locally (as
`paradigm.tape_parity`'s clients do), and the tape ops are made `local irreducible` so a wrong
fold fails on a head mismatch rather than by executing the tape monad.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeHom

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.TapeHom

set_option linter.unusedVariables false

open TorchLean
open TorchLean TorchLean.Tensor
open PropertyKindCalculus.Paradigm (TapeM CpuTape CpuNode)
open FloatLib.Numerics (MathFunctions)
open PropertyKindCalculus
open PropertyKindCalculus.Paradigm (NumCarrier TapeBuilder)
open PropertyKindCalculus.Paradigm.TapeParity
  (Evaluates Evaluates.isNumCarrierHom)

variable {s : Shape}

/-! ## The eager `Tensor Float s` carrier (each branchless op as its elementwise `Spec`) -/

local instance : Zero (Tensor Float s) := ⟨Tensor.full s 0⟩
local instance : One (Tensor Float s) := ⟨Tensor.full s 1⟩
local instance : Pow (Tensor Float s) (Tensor Float s) := ⟨Tensor.pow⟩
local instance : Min (Tensor Float s) := ⟨Tensor.minimum⟩
local instance : Max (Tensor Float s) := ⟨Tensor.maximum⟩
local instance : Coe Nat (Tensor Float s) := ⟨fun n => Tensor.full s (n : Float)⟩
local instance instEagerMath : MathFunctions (Tensor Float s) where
  exp := Tensor.exp
  log := Tensor.log
  abs := Tensor.abs
  sqrt := fun x => Tensor.sqrt x .clampNegative
  pi := Tensor.full s MathFunctions.pi
  sin := Tensor.map MathFunctions.sin
  cos := Tensor.map MathFunctions.cos
  tanh := Tensor.map MathFunctions.tanh
  cosh := Tensor.map MathFunctions.cosh
  sinh := Tensor.map MathFunctions.sinh
local instance instEagerNumCarrier : NumCarrier (Tensor Float s) where

-- A wrong fold would otherwise reduce both carriers to `TapeBuilder.bin …` and execute the
-- tape monad; opacity makes a head mismatch fail immediately (the `paradigm.tape_parity`
-- client discipline `tape_hom` relies on for its clean negative behaviour).
attribute [local irreducible] TapeM.add TapeM.sub TapeM.mul TapeM.pow TapeM.exp TapeM.leaf

/-! ## The toy kernel — authored once, kinded; derived by erasure -/

/-- A dimension-one toy kind — the exponent and the sum share it. -/
def dimlessK : KindOfProperty := { id := "tape-hom-toy-dimensionless", scale := .ratio }
/-- `exp` carries the toy kind to itself. -/
theorem hexp : TranscendentalKind dimlessK dimlessK := ⟨rfl, rfl⟩

/-- Authored once, kinded — the single site of the op tree `x + exp y`. -/
def gQ {α : Type} [NumCarrier α] (x y : Quantity dimlessK α) : Quantity dimlessK α :=
  x + Quantity.exp hexp y

/-- The naked kernel is that form composed with `.magnitude` — defeq, not re-typed. -/
def g {α : Type} [NumCarrier α] (x y : α) : α := (gQ ⟨x⟩ ⟨y⟩).magnitude

/-- A per-pixel input tensor as a tape leaf. -/
def leafT (t : Tensor Float s) (name : Option String := none) : TapeBuilder s :=
  ⟨TapeM.leaf t (name := name)⟩

/-! ## Positive — the parity is one `tape_hom` line -/

/-- The tape program built by `g` (inputs as leaves) `Evaluates` to the eager value of the same
`g` source — proved in one line, naming `g`/`gQ` only to unfold. -/
theorem g_tape_parity (x y : Tensor Float s) :
    Evaluates (g (leafT x "x") (leafT y "y")) (g (α := Tensor Float s) x y) := by
  tape_hom [g, gQ]


/-! ## The kinded real power — the exponent a recorded operand -/

/-- The real-power witness: base, exponent and result in the toy kind. -/
theorem hpow : RealPowerKind dimlessK dimlessK dimlessK := ⟨rfl, rfl, rfl⟩

/-- Authored once, kinded: `x ^ y + x`, the power carrying its one witness. -/
def pQ {α : Type} [NumCarrier α] (x y : Quantity dimlessK α) : Quantity dimlessK α :=
  Quantity.pow hpow x y + x

/-- The naked power kernel, by erasure. -/
def p {α : Type} [NumCarrier α] (x y : α) : α := (pQ ⟨x⟩ ⟨y⟩).magnitude

/-- The tape recorded by `p` evaluates to the eager `Tensor.pow` reading, for all inputs. -/
theorem p_tape_parity (x y : Tensor Float s) :
    Evaluates (p (leafT x "x") (leafT y "y")) (p (α := Tensor Float s) x y) := by
  tape_hom [p, pQ]


/-! ## Negative — `tape_hom` cannot close a false parity -/

-- A deliberately wrong eager RHS (`subSpec` where the exposed tree is a `+`): after the
-- erase-set, `apply Evaluates_add` will not unify with `subSpec`, and no other congruence
-- matches the `+` head, so `tape_hom` leaves the goal open and the trailing `done` fails —
-- `fail_if_success` therefore succeeds, certifying the tactic refuses the false parity.
example (x y : Tensor Float s) : True := by
  fail_if_success
    have : Evaluates (g (leafT x "x") (leafT y "y")) (x - (Tensor.exp y)) := by
      tape_hom [g, gQ]; done
  trivial

/-! ## The bundled homomorphism composes the same congruences -/

-- `Evaluates.isNumCarrierHom` is the named object; its projections re-assemble the tree the
-- tactic walks (`x + exp y`), by hand.
example (x y : Tensor Float s) (hx : Evaluates (leafT x "x") x) (hy : Evaluates (leafT y "y") y) :
    Evaluates (leafT x "x" + MathCarrier.exp (leafT y "y")) (x + (Tensor.exp y)) :=
  Evaluates.isNumCarrierHom.add hx (Evaluates.isNumCarrierHom.exp hy)

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.Tests.TapeHom.g_tape_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms g_tape_parity

/-- info: 'PropertyKindCalculus.Tests.TapeHom.p_tape_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms p_tape_parity

/-- info: 'PropertyKindCalculus.Paradigm.TapeParity.Evaluates.isNumCarrierHom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Evaluates.isNumCarrierHom

end PropertyKindCalculus.Tests.TapeHom

end Blanket
