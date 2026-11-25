/-
`paradigm.tape_m` — the **tape recording monad** `TapeM α` and the elementwise recorders the tape
carrier is built on, over TorchLean's CPU tape `Tape (SomeTensor α)`.

TorchLean records every operator through one entry, `Tape.apply`, from its operator table
(`TorchLean.Op`). This module names the elementwise fragment the kernels use (`add`/`sub`/`mul`/
`div`/`min`/`max` and `abs`/`sqrt`/`exp`/`log`), each a `Tape.apply` at one table operator, and
threads the tape through `StateT`.

`sqrt` records the table's `.clampNegative` root, so a negative operand gives `0`.

A `module` file: imports TorchLean's tape recorder and operator table.
-/

module

public import TorchLean.NN.Tape.Apply
public import TorchLean.Tensor.Op.Table

@[expose] public section Blanket

open TorchLean

namespace PropertyKindCalculus.Paradigm

/-- The CPU autograd tape over the scalar `α`. -/
abbrev CpuTape (α : Type) [Storage α] : Type := Tape (SomeTensor α)

/-- A node of a CPU tape. -/
abbrev CpuNode (α : Type) [Storage α] : Type := Tape.Node (SomeTensor α)

namespace CpuTape

variable {α : Type} [Storage α] [Context α] [Op.Capabilities α]

/-- Record a one-input, one-output table operator; returns the new tape and the node id. -/
def unary {σ τ : Shape} (t : CpuTape α) (name : String)
    (op : Op [⟨.value, σ⟩] [⟨.value, τ⟩]) (x : Nat) : Result (CpuTape α × Nat) := do
  let (t', out) ← Tape.apply t name op (x, ())
  pure (t', out.1)

/-- Record a two-input, one-output table operator; returns the new tape and the node id. -/
def binary {σ₁ σ₂ τ : Shape} (t : CpuTape α) (name : String)
    (op : Op [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] [⟨.value, τ⟩]) (a b : Nat) :
    Result (CpuTape α × Nat) := do
  let (t', out) ← Tape.apply t name op (a, b, ())
  pure (t', out.1)

variable {s : Shape}

def add (t : CpuTape α) (a b : Nat) : Result (CpuTape α × Nat) :=
  binary t "add" (Op.add (s := s)) a b
def sub (t : CpuTape α) (a b : Nat) : Result (CpuTape α × Nat) :=
  binary t "sub" (Op.sub (s := s)) a b
def mul (t : CpuTape α) (a b : Nat) : Result (CpuTape α × Nat) :=
  binary t "mul" (Op.mul (s := s)) a b
def div (t : CpuTape α) (a b : Nat) : Result (CpuTape α × Nat) :=
  binary t "div" (Op.div (s := s)) a b
def min (t : CpuTape α) (a b : Nat) : Result (CpuTape α × Nat) :=
  binary t "min" (Op.min (s := s)) a b
def max (t : CpuTape α) (a b : Nat) : Result (CpuTape α × Nat) :=
  binary t "max" (Op.max (s := s)) a b
def fmin (t : CpuTape α) (a b : Nat) : Result (CpuTape α × Nat) :=
  binary t "fmin" (Op.fmin (s := s)) a b
def fmax (t : CpuTape α) (a b : Nat) : Result (CpuTape α × Nat) :=
  binary t "fmax" (Op.fmax (s := s)) a b
def abs (t : CpuTape α) (x : Nat) : Result (CpuTape α × Nat) :=
  unary t "abs" (Op.abs (s := s)) x
def sqrt (t : CpuTape α) (x : Nat) : Result (CpuTape α × Nat) :=
  unary t "sqrt" (Op.sqrt (s := s) .clampNegative) x
def exp (t : CpuTape α) (x : Nat) : Result (CpuTape α × Nat) :=
  unary t "exp" (Op.exp (s := s)) x
def log (t : CpuTape α) (x : Nat) : Result (CpuTape α × Nat) :=
  unary t "log" (Op.log (s := s)) x

/-- Append a leaf holding the tensor `x`. -/
def leaf (t : CpuTape α) (x : Tensor α s) (name : Option String := none)
    (requiresGrad : Bool := true) : CpuTape α × Nat :=
  Tape.leaf t (SomeTensor.ofTensor x) name requiresGrad

end CpuTape

/-- The tape recording monad: a state of the CPU tape, failing with a message. -/
abbrev TapeM (α : Type) [Storage α] : Type → Type := StateT (CpuTape α) Result

namespace TapeM

variable {α : Type} [Storage α] [Context α] [Op.Capabilities α] {s : Shape}

/-- Run a pure tape step (tape-then-id) as a `TapeM` action (id-then-tape). -/
@[inline] def record (f : CpuTape α → Result (CpuTape α × Nat)) : TapeM α Nat :=
  fun t => (f t).map fun r => (r.2, r.1)

/-- Run a recording program from tape `t`. -/
@[inline] def run {β : Type} (t : CpuTape α) (m : TapeM α β) : Result (β × CpuTape α) :=
  StateT.run m t

omit [Context α] [Op.Capabilities α] in
/-- A pure step's success is the wrapped action's success, with the pair swapped. -/
theorem record_run_ok {f : CpuTape α → Result (CpuTape α × Nat)} {t t' : CpuTape α} {id : Nat}
    (h : f t = .ok (t', id)) : (record f).run t = .ok (id, t') := by
  simp [run, record, StateT.run, h, Except.map]

def leaf (x : Tensor α s) (name : Option String := none) (requiresGrad : Bool := true) :
    TapeM α Nat :=
  fun t => let r := CpuTape.leaf t x name requiresGrad; pure (r.2, r.1)

def add (a b : Nat) : TapeM α Nat := record fun t => CpuTape.add (s := s) t a b
def sub (a b : Nat) : TapeM α Nat := record fun t => CpuTape.sub (s := s) t a b
def mul (a b : Nat) : TapeM α Nat := record fun t => CpuTape.mul (s := s) t a b
def div (a b : Nat) : TapeM α Nat := record fun t => CpuTape.div (s := s) t a b
def min (a b : Nat) : TapeM α Nat := record fun t => CpuTape.min (s := s) t a b
def max (a b : Nat) : TapeM α Nat := record fun t => CpuTape.max (s := s) t a b
def fmin (a b : Nat) : TapeM α Nat := record fun t => CpuTape.fmin (s := s) t a b
def fmax (a b : Nat) : TapeM α Nat := record fun t => CpuTape.fmax (s := s) t a b
def abs (x : Nat) : TapeM α Nat := record fun t => CpuTape.abs (s := s) t x
def sqrt (x : Nat) : TapeM α Nat := record fun t => CpuTape.sqrt (s := s) t x
def exp (x : Nat) : TapeM α Nat := record fun t => CpuTape.exp (s := s) t x
def log (x : Nat) : TapeM α Nat := record fun t => CpuTape.log (s := s) t x

end TapeM

end PropertyKindCalculus.Paradigm

end Blanket
