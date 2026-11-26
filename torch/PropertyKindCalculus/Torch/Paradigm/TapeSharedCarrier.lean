/-
`paradigm.tape_shared_carrier` — the **sharing tape carrier** `SharedTapeBuilder s`: a recording
carrier that emits each distinct sub-expression once.

`TapeBuilder` re-emits a sub-expression at every reference, so a kernel with heavy reuse unfolds
to its expression tree before `cseCompact` can collapse it (one trust-region fit step: tens of
millions of nodes for a few hundred distinct ones). `SharedTapeBuilder` applies `cseCompact`'s
step *while recording*: it runs the recorder `TapeBuilder` runs, keys the node it appended with
`TapeCSE.nodeKey` (name, operands, value bits), and on a hit drops the node and returns the one
already holding that key. The tape stays the size of the DAG.

OPERANDS. The appended node's operands are set to the ids the op was called with. TorchLean's
recorder drops the second operand of `min x x` / `max x x` when both are one node, which
`TapeBuilder` never is; without this the two recordings would differ there.

COST. Memory is bounded by the DAG; time is not: a shared sub-expression is still *visited* once
per reference, and each visit evaluates the op before looking it up.

A `module` file: imports the tape carriers, the CSE key and the LUT vocabulary.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeBatchCarrier
public import PropertyKindCalculus.Torch.Paradigm.TapeCse
public import PropertyKindCalculus.Torch.Paradigm.LutCarrier
public import Std.Data.HashMap

@[expose] public section Blanket

open TorchLean
open FloatLib.Numerics (MathFunctions)

namespace PropertyKindCalculus.Paradigm

/-- The sharing recorder's state: the tape, and `cseCompact`'s memo of the nodes on it. -/
structure SharedTape where
  tape : CpuTape Float := Tape.empty
  memo : Std.HashMap (Option String × Array Nat × List UInt64) Nat := {}

/-- The sharing recording monad. -/
abbrev SharedTapeM : Type → Type := StateT SharedTape Result

namespace SharedTapeM

/-- Run a recording program from the empty tape; yields its result and the recorded tape. -/
def record {β : Type} (m : SharedTapeM β) : Result (β × CpuTape Float) := do
  let (b, st) ← StateT.run m {}
  pure (b, st.tape)

/-- Record one node with `raw` on operands `ps`, or return the node already holding its key.
`raw` must append exactly one node; its operands are set to `ps`. -/
def emit (ps : Array Nat) (raw : TapeM Float Nat) : SharedTapeM Nat := fun st =>
  -- Take the state apart so the tape stays unshared and `raw` pushes in place.
  let ⟨tape, memo⟩ := st
  do
    let (_, tape') ← raw tape
    match tape'.nodes.back? with
    | none => throw "SharedTapeM.emit: the recorder appended no node"
    | some last =>
      let node := { last with parents := ps }
      let key := TapeCSE.nodeKey #[] node
      let nodes := tape'.nodes.pop
      match memo[key]? with
      | some id => pure (id, ⟨{ tape' with nodes := nodes }, memo⟩)
      | none =>
        pure (nodes.size, ⟨{ tape' with nodes := nodes.push node }, memo.insert key nodes.size⟩)

/-- Record a leaf holding `x`, or return the leaf with the same name and value bits. -/
def leaf {s : Shape} (x : Tensor Float s) (name : Option String := none) : SharedTapeM Nat :=
  emit #[] (TapeM.leaf x (name := name))

end SharedTapeM

/-- **The sharing tape carrier.** Running it appends the nodes of its sub-expression that are
not yet on the tape and returns the id of its result. -/
structure SharedTapeBuilder (s : Shape) where
  run : SharedTapeM Nat

namespace SharedTapeBuilder

variable {s : Shape}

/-- A constant leaf filled with the host scalar `x`. -/
def const (x : Float) : SharedTapeBuilder s := ⟨SharedTapeM.leaf (Tensor.full s x)⟩

/-- A named input leaf holding `x`. -/
def input (name : String) (x : Tensor Float s) : SharedTapeBuilder s :=
  ⟨SharedTapeM.leaf x (name := some name)⟩

/-- A `MathFunctions` field with no tape op: an error if run (as `TapeBuilder.unsupported`). -/
def unsupported (op : String) : SharedTapeBuilder s :=
  ⟨throw s!"SharedTapeBuilder: `{op}` has no elementwise tape op"⟩

/-- Lift a binary tape op: run both operands, emit or reuse one node. -/
@[inline] def bin (f : Nat → Nat → TapeM Float Nat)
    (x y : SharedTapeBuilder s) : SharedTapeBuilder s :=
  ⟨do let a ← x.run; let b ← y.run; SharedTapeM.emit #[a, b] (f a b)⟩

/-- Lift a unary tape op: run the operand, emit or reuse one node. -/
@[inline] def un (f : Nat → TapeM Float Nat)
    (x : SharedTapeBuilder s) : SharedTapeBuilder s :=
  ⟨do let a ← x.run; SharedTapeM.emit #[a] (f a)⟩

instance : Zero (SharedTapeBuilder s) := ⟨const 0⟩
instance : One (SharedTapeBuilder s) := ⟨const 1⟩
instance : Add (SharedTapeBuilder s) := ⟨bin (TapeM.add (s := s))⟩
instance : Sub (SharedTapeBuilder s) := ⟨bin (TapeM.sub (s := s))⟩
instance : Mul (SharedTapeBuilder s) := ⟨bin (TapeM.mul (s := s))⟩
instance : Div (SharedTapeBuilder s) := ⟨bin (TapeM.div (s := s))⟩
instance : Min (SharedTapeBuilder s) := ⟨bin (TapeM.min (s := s))⟩
instance : Max (SharedTapeBuilder s) := ⟨bin (TapeM.max (s := s))⟩
/-- The NaN-ignoring minimum (`Op.fmin`) as one shared tape node. -/
def fmin : SharedTapeBuilder s → SharedTapeBuilder s → SharedTapeBuilder s :=
  bin (TapeM.fmin (s := s))
/-- The NaN-ignoring maximum (`Op.fmax`) as one shared tape node. -/
def fmax : SharedTapeBuilder s → SharedTapeBuilder s → SharedTapeBuilder s :=
  bin (TapeM.fmax (s := s))
instance : Coe Nat (SharedTapeBuilder s) := ⟨fun n => const ((n : Float))⟩

instance : MathFunctions (SharedTapeBuilder s) where
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

/-- The sharing tape carrier is a `NumCarrier`, op for op as `TapeBuilder`. -/
instance instNumCarrier : NumCarrier (SharedTapeBuilder s) where

/-- One shared `lutfetch:<name>` node: `TapeBuilder.lutFetchM` on the operands' ids. -/
instance : LutInterp (SharedTapeBuilder s) where
  lutFetch := fun tbl => bin
    (fun l u => (TapeBuilder.lutFetchM (s := s) tbl ⟨pure l⟩ ⟨pure u⟩).run)

end SharedTapeBuilder

/-- **The sharing tape carrier as a `BatchCarrier`**, field for field as `TapeBuilder`'s. -/
instance SharedTapeBuilder.instBatchCarrier : BatchCarrier SharedTapeBuilder where
  const        := fun v => SharedTapeBuilder.const v
  ofFloatArray := fun {s} a => ⟨SharedTapeM.leaf (TapeBuilder.tensorOfFloatArray s a 0)⟩
  toFloatArray := fun {s} b =>
    match SharedTapeM.record b.run with
    | .ok (id, t) =>
        match t.nodes[id]? with
        | some node => (TorchLean.Storage.toArray node.value.tensor.buffer).foldl
                          (fun acc x => acc.push x) (FloatArray.emptyWithCapacity (Shape.size s))
        | none      => FloatArray.emptyWithCapacity 0
    | .error _  => FloatArray.emptyWithCapacity 0
  fmin         := SharedTapeBuilder.fmin
  fmax         := SharedTapeBuilder.fmax
  liveSize     := fun {s} _ => (Shape.size s).toUInt32
  release      := fun _ => 0

end PropertyKindCalculus.Paradigm

end Blanket
