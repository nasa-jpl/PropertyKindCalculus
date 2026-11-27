/-
`paradigm.tape_shared_carrier` — the **sharing tape carrier** `SharedTapeBuilder s`: a recording
carrier that emits each distinct sub-expression once.

`TapeBuilder` re-emits a sub-expression at every reference, so a kernel with heavy reuse unfolds
to its expression tree before `cseCompact` can collapse it (one trust-region fit step: tens of
millions of nodes for a few hundred distinct ones). `SharedTapeBuilder` applies `cseCompact`'s
step *while recording*: it runs the recorder `TapeBuilder` runs, keys the node it appended with
`TapeCSE.nodeKey` (name, operands, value bits) and its stored shape, and on a hit drops the node
and returns the one already holding that key. The tape stays the size of the DAG.

SHAPE. `cseCompact`'s key has no shape, so it merges a scalar and a one-element vector with the
same name and bits; this recorder does not. The two agree on recordings at one shape.

OPERANDS. The appended node's operands are set to the ids the op was called with. TorchLean's
recorder drops the second operand of `min x x` / `max x x` when both are one node, which
`TapeBuilder` never is; without this the two recordings would differ there.

COST. Memory is bounded by the DAG; time is not: a shared sub-expression is still *visited* once
per reference. An elementwise op (`SharedOp`) is looked up by op, shape and operands before it
is run; a leaf or a table fetch is run, then looked up.

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

/-- The elementwise tape ops the sharing recorder can look up before running. -/
inductive SharedOp where
  | add | sub | mul | div | min | max | fmin | fmax | exp | log | abs | sqrt
  deriving DecidableEq, Hashable, Repr

/-- The `TapeM` recorder of `op` at shape `s` on operands `ps` (a missing operand reads id 0). -/
def SharedOp.raw (s : Shape) : SharedOp → Array Nat → TapeM Float Nat
  | .add,  ps => TapeM.add  (s := s) (ps.getD 0 0) (ps.getD 1 0)
  | .sub,  ps => TapeM.sub  (s := s) (ps.getD 0 0) (ps.getD 1 0)
  | .mul,  ps => TapeM.mul  (s := s) (ps.getD 0 0) (ps.getD 1 0)
  | .div,  ps => TapeM.div  (s := s) (ps.getD 0 0) (ps.getD 1 0)
  | .min,  ps => TapeM.min  (s := s) (ps.getD 0 0) (ps.getD 1 0)
  | .max,  ps => TapeM.max  (s := s) (ps.getD 0 0) (ps.getD 1 0)
  | .fmin, ps => TapeM.fmin (s := s) (ps.getD 0 0) (ps.getD 1 0)
  | .fmax, ps => TapeM.fmax (s := s) (ps.getD 0 0) (ps.getD 1 0)
  | .exp,  ps => TapeM.exp  (s := s) (ps.getD 0 0)
  | .log,  ps => TapeM.log  (s := s) (ps.getD 0 0)
  | .abs,  ps => TapeM.abs  (s := s) (ps.getD 0 0)
  | .sqrt, ps => TapeM.sqrt (s := s) (ps.getD 0 0)

/-- The sharing recorder's state. -/
structure SharedTape where
  tape : CpuTape Float := Tape.empty
  /-- `cseCompact`'s memo of the nodes on `tape`, with the stored shape added to its key. -/
  memo : Std.HashMap (Shape × Option String × Array Nat × List UInt64) Nat := {}
  /-- The node `emit` returned for an op at a shape on operands; read before running the op. -/
  seen : Std.HashMap (SharedOp × Shape × Array Nat) Nat := {}

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
  let ⟨tape, memo, seen⟩ := st
  do
    let (_, tape') ← raw tape
    match tape'.nodes.back? with
    | none => throw "SharedTapeM.emit: the recorder appended no node"
    | some last =>
      let node := { last with parents := ps }
      let key := (node.value.shape, TapeCSE.nodeKey #[] node)
      let nodes := tape'.nodes.pop
      match memo[key]? with
      | some id => pure (id, ⟨{ tape' with nodes := nodes }, memo, seen⟩)
      | none =>
        pure (nodes.size, ⟨{ tape' with nodes := nodes.push node }, memo.insert key nodes.size,
          seen⟩)

/-- Record `op` at shape `s` on operands `ps`: the node `seen` holds for it, else `emit`'s. A
`seen` entry is what `emit` returned for the same op, shape and operands on an earlier tape; the
tape only grows, so `emit` would return it again. -/
def op (o : SharedOp) (s : Shape) (ps : Array Nat) : SharedTapeM Nat := fun st =>
  match st.seen[(o, s, ps)]? with
  | some id => pure (id, st)
  | none => do
    let (id, ⟨tape, memo, seen⟩) ← emit ps (o.raw s ps) st
    pure (id, ⟨tape, memo, seen.insert (o, s, ps) id⟩)

/-- Record a leaf holding `x`, or return the leaf with the same name, shape and value bits. -/
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

/-- Lift a binary tape op: run both operands, look up or emit one node. -/
@[inline] def bin (o : SharedOp) (x y : SharedTapeBuilder s) : SharedTapeBuilder s :=
  ⟨do let a ← x.run; let b ← y.run; SharedTapeM.op o s #[a, b]⟩

/-- Lift a unary tape op: run the operand, look up or emit one node. -/
@[inline] def un (o : SharedOp) (x : SharedTapeBuilder s) : SharedTapeBuilder s :=
  ⟨do let a ← x.run; SharedTapeM.op o s #[a]⟩

instance : Zero (SharedTapeBuilder s) := ⟨const 0⟩
instance : One (SharedTapeBuilder s) := ⟨const 1⟩
instance : Add (SharedTapeBuilder s) := ⟨bin .add⟩
instance : Sub (SharedTapeBuilder s) := ⟨bin .sub⟩
instance : Mul (SharedTapeBuilder s) := ⟨bin .mul⟩
instance : Div (SharedTapeBuilder s) := ⟨bin .div⟩
instance : Min (SharedTapeBuilder s) := ⟨bin .min⟩
instance : Max (SharedTapeBuilder s) := ⟨bin .max⟩
/-- The NaN-ignoring minimum (`Op.fmin`) as one shared tape node. -/
def fmin : SharedTapeBuilder s → SharedTapeBuilder s → SharedTapeBuilder s :=
  bin .fmin
/-- The NaN-ignoring maximum (`Op.fmax`) as one shared tape node. -/
def fmax : SharedTapeBuilder s → SharedTapeBuilder s → SharedTapeBuilder s :=
  bin .fmax
instance : Coe Nat (SharedTapeBuilder s) := ⟨fun n => const ((n : Float))⟩

instance : MathFunctions (SharedTapeBuilder s) where
  exp  := un .exp
  log  := un .log
  abs  := un .abs
  sqrt := un .sqrt
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
  lutFetch := fun tbl x y => ⟨do
    let l ← x.run
    let u ← y.run
    SharedTapeM.emit #[l, u] (TapeBuilder.lutFetchM (s := s) tbl ⟨pure l⟩ ⟨pure u⟩).run⟩

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
