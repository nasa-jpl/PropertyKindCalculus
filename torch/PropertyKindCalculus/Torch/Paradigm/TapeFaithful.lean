/-
# Forward-value faithfulness for the eager autograd tape

The eager engine (`NN.Runtime.Autograd.Tape`) records a forward pass as a grow-only array of
nodes, each storing a shape-erased forward value; `requireValue` reads a typed value back. This
module proves that the value stored by each elementwise op is *exactly* the corresponding pure
`Spec` operation of its inputs:

  **every elementwise tape op stores, as its forward value, the matching `Spec` op applied to its
  inputs' values** — `Tape.div` stores `divSpec a b`, `Tape.add` stores `addSpec a b`, and so on.

This is the *forward-value faithfulness* of the eager tape. It matters whenever the same numeric
program is interpreted at more than one carrier `α` (e.g. an exact carrier for proofs and `Float`
for execution): building the program on a `Tape α` and reading the output back equals the pure
`Spec` computation **by construction**, so agreement between a tape program and its specification
becomes a *proof*, not a numerical comparison.

The op lemmas are proved op-by-op from three generic building blocks:

  1. `requireValue_addNode_self` — reading back the value of a freshly-appended node returns its
     stored tensor (the `cast_shape_self` boundary of the dynamic shape check);
  2. `requireValue_addNode_of_lt` — appending a node does not disturb the value read back at any
     earlier id (value stability, so a multi-op tape can re-read its inputs);
  3. `leaf_value` — a leaf node reads back as the tensor it was created with.

Each op lemma additionally exposes a `FrameOver` witness: the op preserves every earlier node's
value, so a later op can re-read an earlier input. Together the `*_value` lemmas reduce a
whole-program faithfulness proof to a mechanical chain — each op's output rewrites to its `Spec`
term and earlier values survive by `FrameOver` — even for *symbolic* inputs `a b : Tensor α s`,
where evaluating/`decide`-ing the tape is impossible (see `Demo.kernel_eq_spec`).

Covered ops: the binary arithmetic (`add`/`sub`/`mul`/`div`), the scalar `scale`, the branchless
selectors (`min`/`max`/`relu`), and the unary family (`abs`/`sqrt`/`clamp`/`exp`/`log`/`inv`) via
one `unary_value` lemma over the shared `Tape.unary` builder.
-/
import NN.Runtime.Autograd.Engine.TapeM

open Spec TorchLean
open TorchLean TorchLean.Tensor
open Runtime.Autograd

namespace PropertyKindCalculus.Paradigm.TapeFaithful

open Runtime.Autograd.Tape

variable {α : Type} [TorchLean.Storage α]

/-! ## Generic building blocks -/

/-- `requireValue` depends only on the stored value (`getValue?`): two tapes that agree on `id`'s
stored value agree on `requireValue`. This is the congruence that turns *value stability* under
`addNode` into *`requireValue` stability*. -/
theorem requireValue_congr [DecidableEq Shape] {s : Shape}
    (t₁ t₂ : Tape α) (id : Nat) (hg : t₁.getValue? id = t₂.getValue? id) :
    t₁.requireValue (s := s) id = t₂.requireValue (s := s) id := by
  unfold Tape.requireValue
  rw [hg]

/-- `requireValue` succeeds with exactly the stored tensor when `getValue?` returns it (the dynamic
shape check passes via `cast_shape_self`). -/
theorem requireValue_of_getValue [DecidableEq Shape] {s : Shape}
    (t : Tape α) (id : Nat) {y : Tensor α s}
    (h : t.getValue? id = some (Spec.SomeTensor.ofTensor y)) :
    t.requireValue (s := s) id = .ok y := by
  unfold Tape.requireValue
  rw [h]
  simp [Spec.SomeTensor.ofTensor]

/-- Reading back the value of a freshly-appended node returns its stored tensor. The new node's id
is `t.size`. -/
theorem requireValue_addNode_self [DecidableEq Shape] {s : Shape}
    (t : Tape α) (node : Node α) {y : Tensor α s}
    (hval : node.value = Spec.SomeTensor.ofTensor y) :
    (t.addNode node).1.requireValue (s := s) t.size = .ok y := by
  apply requireValue_of_getValue
  simp only [Tape.addNode, Tape.getValue?, Tape.getNode?, Tape.size]
  rw [Array.getElem?_push_size]
  simp [hval]

/-- Appending a node does not disturb the value read back at any pre-existing id `id < t.size`
(value stability: a later op can still re-read an earlier input). -/
theorem requireValue_addNode_of_lt [DecidableEq Shape] {s : Shape}
    (t : Tape α) (node : Node α) (id : Nat) (hlt : id < t.size) :
    (t.addNode node).1.requireValue (s := s) id = t.requireValue (s := s) id := by
  apply requireValue_congr
  simp only [Tape.addNode, Tape.getValue?, Tape.getNode?]
  congr 1
  rw [Array.getElem?_push, ite_eq_right (Nat.ne_of_lt (by simpa [Tape.size] using hlt))]

/-- `t'` extends `t` by appending one node: it reads back the same value as `t` at every
pre-existing id. This is the *frame* an op carries so a later op can re-read an earlier input. -/
def FrameOver [DecidableEq Shape] (t' t : Tape α) : Prop :=
  ∀ {s : Shape} (id : Nat), id < t.size → t'.requireValue (s := s) id = t.requireValue (s := s) id

/-- Appending a node frames the previous tape. -/
theorem frameOver_addNode [DecidableEq Shape] (t : Tape α) (node : Node α) :
    FrameOver (t.addNode node).1 t := by
  intro s id h
  exact requireValue_addNode_of_lt t node id h

/-- A leaf node reads back as the tensor it was created with. -/
theorem leaf_value [DecidableEq Shape] {s : Shape}
    (t : Tape α) (x : Tensor α s) (name : Option String) (rg : Bool) :
    (Tape.leaf (t := t) x (name := name) (requiresGrad := rg)).1.requireValue (s := s) t.size
      = .ok x := by
  unfold Tape.leaf
  exact requireValue_addNode_self t _ rfl

/-! ## Per-op forward-value faithfulness

Each lemma reads: given the input values, the op's output node reads back as the corresponding
`Spec` operation of those values. The successor tape is `(op …).1` at the new id `t.size`. -/

/-- `Tape.add` stores `addSpec a b`. -/
theorem add_value [Add α] [DecidableEq Shape] {s : Shape}
    (t : Tape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : t.requireValue (s := s) aId = .ok a)
    (hb : t.requireValue (s := s) bId = .ok b) :
    ∃ t', t.add (s := s) aId bId = .ok (t', t.size) ∧
          t'.requireValue (s := s) t.size = .ok (addSpec a b) ∧ FrameOver t' t := by
  unfold Tape.add
  rw [ha, hb]
  exact ⟨_, rfl, requireValue_addNode_self t _ rfl, frameOver_addNode t _⟩

/-- `Tape.sub` stores `subSpec a b`. -/
theorem sub_value [Sub α] [Zero α] [DecidableEq Shape] {s : Shape}
    (t : Tape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : t.requireValue (s := s) aId = .ok a)
    (hb : t.requireValue (s := s) bId = .ok b) :
    ∃ t', t.sub (s := s) aId bId = .ok (t', t.size) ∧
          t'.requireValue (s := s) t.size = .ok (subSpec a b) ∧ FrameOver t' t := by
  unfold Tape.sub
  rw [ha, hb]
  exact ⟨_, rfl, requireValue_addNode_self t _ rfl, frameOver_addNode t _⟩

/-- `Tape.mul` stores `mulSpec a b`. -/
theorem mul_value [Mul α] [DecidableEq Shape] {s : Shape}
    (t : Tape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : t.requireValue (s := s) aId = .ok a)
    (hb : t.requireValue (s := s) bId = .ok b) :
    ∃ t', t.mul (s := s) aId bId = .ok (t', t.size) ∧
          t'.requireValue (s := s) t.size = .ok (mulSpec a b) ∧ FrameOver t' t := by
  unfold Tape.mul
  rw [ha, hb]
  exact ⟨_, rfl, requireValue_addNode_self t _ rfl, frameOver_addNode t _⟩

/-- `Tape.div` stores `divSpec a b`. -/
theorem div_value [Context α] [DecidableEq Shape] {s : Shape}
    (t : Tape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : t.requireValue (s := s) aId = .ok a)
    (hb : t.requireValue (s := s) bId = .ok b) :
    ∃ t', t.div (s := s) aId bId = .ok (t', t.size) ∧
          t'.requireValue (s := s) t.size = .ok (divSpec a b) ∧ FrameOver t' t := by
  unfold Tape.div
  rw [ha, hb]
  exact ⟨_, rfl, requireValue_addNode_self t _ rfl, frameOver_addNode t _⟩

/-- `Tape.scale` stores `scaleSpec x c`. -/
theorem scale_value [Mul α] [DecidableEq Shape] {s : Shape}
    (t : Tape α) (xId : Nat) (c : α) {x : Tensor α s}
    (hx : t.requireValue (s := s) xId = .ok x) :
    ∃ t', t.scale (s := s) xId c = .ok (t', t.size) ∧
          t'.requireValue (s := s) t.size = .ok (scaleSpec x c) ∧ FrameOver t' t := by
  unfold Tape.scale
  rw [hx]
  exact ⟨_, rfl, requireValue_addNode_self t _ rfl, frameOver_addNode t _⟩

/-- `Tape.min` stores `minSpec a b`. -/
theorem min_value [Context α] [DecidableRel ((· > ·) : α → α → Prop)] [DecidableEq Shape] {s : Shape}
    (t : Tape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : t.requireValue (s := s) aId = .ok a)
    (hb : t.requireValue (s := s) bId = .ok b) :
    ∃ t', t.min (s := s) aId bId = .ok (t', t.size) ∧
          t'.requireValue (s := s) t.size = .ok (minSpec a b) ∧ FrameOver t' t := by
  unfold Tape.min
  rw [ha, hb]
  exact ⟨_, rfl, requireValue_addNode_self t _ rfl, frameOver_addNode t _⟩

/-- `Tape.max` stores `maxSpec a b`. -/
theorem max_value [Context α] [DecidableRel ((· > ·) : α → α → Prop)] [DecidableEq Shape] {s : Shape}
    (t : Tape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : t.requireValue (s := s) aId = .ok a)
    (hb : t.requireValue (s := s) bId = .ok b) :
    ∃ t', t.max (s := s) aId bId = .ok (t', t.size) ∧
          t'.requireValue (s := s) t.size = .ok (maxSpec a b) ∧ FrameOver t' t := by
  unfold Tape.max
  rw [ha, hb]
  exact ⟨_, rfl, requireValue_addNode_self t _ rfl, frameOver_addNode t _⟩

/-- `Tape.relu` stores `Activation.reluSpec x`. -/
theorem relu_value [Mul α] [Zero α] [Max α] [BEq α] [One α] [LT α]
    [DecidableRel ((· > ·) : α → α → Prop)] [DecidableEq Shape] {s : Shape}
    (t : Tape α) (xId : Nat) {x : Tensor α s}
    (hx : t.requireValue (s := s) xId = .ok x) :
    ∃ t', t.relu (s := s) xId = .ok (t', t.size) ∧
          t'.requireValue (s := s) t.size = .ok (Activation.reluSpec x) ∧ FrameOver t' t := by
  unfold Tape.relu
  rw [hx]
  exact ⟨_, rfl, requireValue_addNode_self t _ rfl, frameOver_addNode t _⟩

/-- Generic unary forward-value: a `Tape.unary` node stores `forward x`. Covers
`abs`/`sqrt`/`clamp`/`exp`/`log`/`inv`, each of which is a `Tape.unary` with a fixed `forward`. -/
theorem unary_value [DecidableEq Shape] {σ τ : Shape}
    (t : Tape α) (opName : String) (xId : Nat)
    (forward : Tensor α σ → Tensor α τ)
    (backward : Tensor α σ → Tensor α τ → Tensor α σ)
    {x : Tensor α σ} (hx : t.requireValue (s := σ) xId = .ok x) :
    ∃ t', t.unary opName xId forward backward = .ok (t', t.size) ∧
          t'.requireValue (s := τ) t.size = .ok (forward x) ∧ FrameOver t' t := by
  unfold Tape.unary
  rw [hx]
  exact ⟨_, rfl, requireValue_addNode_self t _ rfl, frameOver_addNode t _⟩

/-- `Tape.sqrt` stores `sqrtSpec x` (unary specialization). -/
theorem sqrt_value [Context α] [DecidableRel ((· > ·) : α → α → Prop)] [DecidableEq Shape] {s : Shape}
    (t : Tape α) (xId : Nat) {x : Tensor α s}
    (hx : t.requireValue (s := s) xId = .ok x) :
    ∃ t', t.sqrt (s := s) xId = .ok (t', t.size) ∧
          t'.requireValue (s := s) t.size = .ok (sqrtSpec (α := α) (s := s) x) ∧ FrameOver t' t := by
  unfold Tape.sqrt
  exact unary_value t _ xId _ _ hx

/-- `Tape.exp` stores `expSpec x` — the one extra transcendental the AVS forward model names
(`exp(−2·b·ndvi)`). `Tape.exp` is a direct `addNode` (not a `Tape.unary`), so this mirrors the
`unary_value` skeleton by hand: read the input value, then read back the appended node. -/
theorem exp_value [Context α] [DecidableEq Shape] {s : Shape}
    (t : Tape α) (xId : Nat) {x : Tensor α s}
    (hx : t.requireValue (s := s) xId = .ok x) :
    ∃ t', t.exp (s := s) xId = .ok (t', t.size) ∧
          t'.requireValue (s := s) t.size = .ok (expSpec (α := α) (s := s) x) ∧ FrameOver t' t := by
  unfold Tape.exp
  rw [hx]
  exact ⟨_, rfl, requireValue_addNode_self t _ rfl, frameOver_addNode t _⟩

/-! ## Faithfulness-by-construction demonstrator

A symbolic kernel `g(a,b) = (a / b) + b` built on the eager tape, proved equal to its `Spec` term
`addSpec (divSpec a b) b` with **no execution** — the inputs are abstract `Tensor α s`. It shows the
intended composition: every intermediate value rewrites to a `Spec` op via the `*_value` lemmas, and
the re-read of the earlier leaf `b` survives the `div` by the carried `FrameOver`. -/

namespace Demo

variable [Context α] [DecidableEq Shape] {s : Shape}

/-- Leaf tape holding only `a` (node id `0`). -/
private def ta (a : Tensor α s) : Tape α := (Tape.leaf (t := (Tape.empty : Tape α)) a).1
/-- Leaf tape holding `a` (id `0`) then `b` (id `1`). -/
private def tab (a b : Tensor α s) : Tape α := (Tape.leaf (t := ta a) b).1

/-- The kernel `g(a,b) = (a / b) + b`: leaf `a` (id 0), leaf `b` (id 1), `div 0 1` (id 2 = a/b),
`add 2 1` (id 3 = a/b + b, *re-reading* leaf `b` across the `div`). Returns the final node's value. -/
def kernel (a b : Tensor α s) : Result (Tensor α s) :=
  let t2 := tab a b
  do
    let (t3, id2) ← Tape.div (t := t2) (s := s) 0 1
    let (t4, id3) ← Tape.add (t := t3) (s := s) id2 1
    t4.requireValue (s := s) id3

/-- **Faithfulness by construction**: the symbolic tape kernel equals its `Spec` term, with no
execution — each op's output rewrites to a `Spec` op via the `*_value` lemmas, and the re-read of
leaf `b` survives the `div` by the carried `FrameOver`. -/
theorem kernel_eq_spec (a b : Tensor α s) :
    kernel a b = .ok (addSpec (divSpec a b) b) := by
  -- Concrete tape sizes (the Array lengths are decidable even though the values are symbolic).
  have hsz_e : (Tape.empty : Tape α).size = 0 := by simp [Tape.empty, Tape.size]
  have hsz_a : (ta a).size = 1 := by simp [ta, Tape.leaf, Tape.addNode, Tape.size, Tape.empty]
  have hsz_ab : (tab a b).size = 2 := by
    simp [tab, ta, Tape.leaf, Tape.addNode, Tape.size, Tape.empty]
  -- Leaf values, read back symbolically.
  have hA_a : (ta a).requireValue (s := s) 0 = .ok a := by
    have h := leaf_value (Tape.empty : Tape α) a none true
    rwa [hsz_e] at h
  have hB_ab : (tab a b).requireValue (s := s) 1 = .ok b := by
    have h := leaf_value (ta a) b none true
    rwa [hsz_a] at h
  -- `a` (id 0) survives the second leaf append (frame).
  have hA_ab : (tab a b).requireValue (s := s) 0 = .ok a := by
    unfold tab Tape.leaf
    rw [requireValue_addNode_of_lt (ta a) _ 0 (by rw [hsz_a]; decide)]
    exact hA_a
  -- `div` output value, plus its frame.
  obtain ⟨t3, hdiv, hv3, hf3⟩ := div_value (tab a b) 0 1 hA_ab hB_ab
  -- `b` (id 1) survives the `div` append (frame), so `add` can re-read it.
  have hB_3 : t3.requireValue (s := s) 1 = .ok b := by
    have hfr : t3.requireValue (s := s) 1 = (tab a b).requireValue (s := s) 1 :=
      hf3 (s := s) 1 (by rw [hsz_ab]; decide)
    rw [hfr]; exact hB_ab
  -- `add` output value = the full Spec term.
  obtain ⟨t4, hadd, hv4, _⟩ := add_value t3 (tab a b).size 1 hv3 hB_3
  -- Reduce the kernel's monadic binds with the two op equations.
  show (let t2 := tab a b;
        Tape.div (t := t2) (s := s) 0 1 >>= fun r3 =>
          Tape.add (t := r3.1) (s := s) r3.2 1 >>= fun r4 =>
            r4.1.requireValue (s := s) r4.2) = _
  simp only []
  rw [hdiv]
  simp only [bind, Except.bind]
  rw [hadd]
  exact hv4

end Demo

end PropertyKindCalculus.Paradigm.TapeFaithful
