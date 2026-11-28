/-
`paradigm.tape_faithful` — **forward-value faithfulness** of the elementwise tape recorders.

Each recorder of `paradigm.tape_m` is `Tape.apply` at one operator of TorchLean's table. The
lemmas here read: given the input values, the recorded node reads back as the table rule's forward
map of those values, at the new id `t.size`, and every earlier value survives (`FrameOver`). That
turns a whole-program faithfulness proof into a mechanical chain, even for *symbolic* inputs
`a b : Tensor α s`, where evaluating the tape is impossible (see `Demo.kernel_eq_spec`).

Covered ops: `add`/`sub`/`mul`/`div`/`pow`, `min`/`max`, `fmin`/`fmax`, and the unary `abs`/`sqrt`/`exp`/`log`, through
one `binary_value` and one `unary_value` lemma over `Tape.apply`.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeM
public import TorchLean.NN.Tape.Apply.Correctness

@[expose] public section Blanket

open TorchLean

namespace PropertyKindCalculus.Paradigm.TapeFaithful

open TorchLean.Tape
open PropertyKindCalculus.Paradigm

variable {α : Type} [TorchLean.Storage α]

/-! ## Generic building blocks -/

/-- `requireValue` depends only on the stored value: two tapes that agree on `id`'s stored value
agree on `requireValue`. -/
theorem requireValue_congr {s : Shape}
    (t₁ t₂ : CpuTape α) (id : Nat) (hg : t₁.getValue? id = t₂.getValue? id) :
    requireValue (s := s) t₁ id = requireValue (s := s) t₂ id := by
  unfold requireValue
  rw [hg]

/-- `requireValue` succeeds with exactly the stored tensor when `getValue?` returns it. -/
theorem requireValue_of_getValue {s : Shape}
    (t : CpuTape α) (id : Nat) {y : Tensor α s}
    (h : t.getValue? id = some (SomeTensor.ofTensor y)) :
    requireValue (s := s) t id = .ok y := by
  unfold requireValue
  rw [h]
  simp [SomeTensor.ofTensor]

/-- Reading back the value of a freshly-appended node returns its stored tensor, at id
`t.size`. -/
theorem requireValue_addNode_self {s : Shape}
    (t : CpuTape α) (node : Tape.Node (SomeTensor α)) {y : Tensor α s}
    (hval : node.value = SomeTensor.ofTensor y) :
    requireValue (s := s) (t.addNode node).1 t.size = .ok y := by
  apply requireValue_of_getValue
  simp only [Tape.addNode, Tape.getValue?, Tape.getNode?, Tape.size]
  rw [Array.getElem?_push_size]
  simp [hval]

/-- Appending a node does not disturb the value read back at any earlier id. -/
theorem requireValue_addNode_of_lt {s : Shape}
    (t : CpuTape α) (node : Tape.Node (SomeTensor α)) (id : Nat) (hlt : id < t.size) :
    requireValue (s := s) (t.addNode node).1 id = requireValue (s := s) t id := by
  apply requireValue_congr
  simp only [Tape.addNode, Tape.getValue?, Tape.getNode?]
  congr 1
  rw [Array.getElem?_push, ite_eq_right (Nat.ne_of_lt (by simpa [Tape.size] using hlt))]

/-- `t'` reads back the same value as `t` at every id of `t`: the *frame* an op carries so a later
op can re-read an earlier input. -/
def FrameOver (t' t : CpuTape α) : Prop :=
  ∀ {s : Shape} (id : Nat), id < t.size →
    requireValue (s := s) t' id = requireValue (s := s) t id

/-- Appending a node frames the previous tape. -/
theorem frameOver_addNode (t : CpuTape α) (node : Tape.Node (SomeTensor α)) :
    FrameOver (t.addNode node).1 t := by
  intro s id h
  exact requireValue_addNode_of_lt t node id h

/-- A leaf node reads back as the tensor it was created with. -/
theorem leaf_value {s : Shape}
    (t : CpuTape α) (x : Tensor α s) (name : Option String) (rg : Bool) :
    requireValue (s := s) (CpuTape.leaf t x name rg).1 t.size = .ok x := by
  unfold CpuTape.leaf Tape.leaf
  exact requireValue_addNode_self t _ rfl

/-! ## Per-op forward-value faithfulness

Every recorder is `Tape.apply` at a table operator with one value output, so each per-op lemma is
the generic one at that operator's rule. -/

variable [Context α] [Op.Capabilities α]

/-- The node a binary table operator appends: its name, its value parents and the rule's forward
value. The parents are stated for rules without an alias rule: an aliased `min x x` records one
parent. -/
theorem binary_node {σ₁ σ₂ τ : Shape}
    (t : CpuTape α) (name : String) (op : Op [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] [⟨.value, τ⟩])
    (aId bId : Nat) {rule : Op.Rule α [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] [⟨.value, τ⟩]}
    (hc : op.check = .ok ()) (hr : op.rule? (α := α) = some rule)
    (hv : rule.validate = fun _ => .ok ())
    {a : Tensor α σ₁} {b : Tensor α σ₂}
    (ha : requireValue (s := σ₁) t aId = .ok a) (hb : requireValue (s := σ₂) t bId = .ok b) :
    ∃ node : Tape.Node (SomeTensor α),
      CpuTape.binary t name op aId bId = .ok ((t.addNode node).1, t.size) ∧
      node.name = some name ∧ (rule.alias? = none → node.parents = #[aId, bId]) ∧
      node.value = SomeTensor.ofTensor (rule.forward (a, b, ())).1 := by
  have hread : Args.read t [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] (aId, bId, ()) = .ok (a, b, ()) := by
    simp [Args.read, Arg.read, ha, hb, bind, Except.bind, pure, Except.pure]
  have hpv := prepared_value rule
    (Args.ids [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] (show Args α [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] from (aId, bId, ()))) (a, b, ())
    (Args.flags t [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] (aId, bId, ()))
  unfold CpuTape.binary Tape.apply
  simp only [hc, hr, hread, hv, bind, Except.bind, record, valuePorts,
    List.countP_singleton, beq_self_eq_true, ite_true, gt_iff_lt, Nat.lt_irrefl, ite_false, pure,
    Except.pure]
  exact ⟨_, _root_.rfl, _root_.rfl,
    fun hal => by simp [recordedNode, Args.ids, Arg.id?, prepared, aliasOf, hal, List.finRange],
    congrArg (fun v : Values α [⟨.value, τ⟩] => SomeTensor.ofTensor v.1) hpv⟩

/-- Generic binary forward-value: the recorded node stores the rule's forward map. -/
theorem binary_value {σ₁ σ₂ τ : Shape}
    (t : CpuTape α) (name : String) (op : Op [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] [⟨.value, τ⟩])
    (aId bId : Nat) {rule : Op.Rule α [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] [⟨.value, τ⟩]}
    (hc : op.check = .ok ()) (hr : op.rule? (α := α) = some rule)
    (hv : rule.validate = fun _ => .ok ())
    {a : Tensor α σ₁} {b : Tensor α σ₂}
    (ha : requireValue (s := σ₁) t aId = .ok a) (hb : requireValue (s := σ₂) t bId = .ok b) :
    ∃ t', CpuTape.binary t name op aId bId = .ok (t', t.size) ∧
          requireValue (s := τ) t' t.size = .ok (rule.forward (a, b, ())).1 ∧ FrameOver t' t := by
  obtain ⟨node, hrun, -, -, hval⟩ := binary_node t name op aId bId hc hr hv ha hb
  exact ⟨_, hrun, requireValue_addNode_self t node hval, frameOver_addNode t node⟩

/-- The node a unary table operator appends: its name, its value parent and the rule's forward
value. -/
theorem unary_node {σ τ : Shape}
    (t : CpuTape α) (name : String) (op : Op [⟨.value, σ⟩] [⟨.value, τ⟩])
    (xId : Nat) {rule : Op.Rule α [⟨.value, σ⟩] [⟨.value, τ⟩]}
    (hc : op.check = .ok ()) (hr : op.rule? (α := α) = some rule)
    (hv : rule.validate = fun _ => .ok ())
    {x : Tensor α σ} (hx : requireValue (s := σ) t xId = .ok x) :
    ∃ node : Tape.Node (SomeTensor α),
      CpuTape.unary t name op xId = .ok ((t.addNode node).1, t.size) ∧
      node.name = some name ∧ (rule.alias? = none → node.parents = #[xId]) ∧
      node.value = SomeTensor.ofTensor (rule.forward (x, ())).1 := by
  have hread : Args.read t [⟨.value, σ⟩] (xId, ()) = .ok (x, ()) := by
    simp [Args.read, Arg.read, hx, bind, Except.bind, pure, Except.pure]
  have hpv := prepared_value rule
    (Args.ids [⟨.value, σ⟩] (show Args α [⟨.value, σ⟩] from (xId, ()))) (x, ())
    (Args.flags t [⟨.value, σ⟩] (xId, ()))
  unfold CpuTape.unary Tape.apply
  simp only [hc, hr, hread, hv, bind, Except.bind, record, valuePorts,
    List.countP_singleton, beq_self_eq_true, ite_true, gt_iff_lt, Nat.lt_irrefl, ite_false, pure,
    Except.pure]
  exact ⟨_, _root_.rfl, _root_.rfl,
    fun hal => by simp [recordedNode, Args.ids, Arg.id?, prepared, aliasOf, hal, List.finRange],
    congrArg (fun v : Values α [⟨.value, τ⟩] => SomeTensor.ofTensor v.1) hpv⟩

/-- Generic unary forward-value: the recorded node stores the rule's forward map. -/
theorem unary_value {σ τ : Shape}
    (t : CpuTape α) (name : String) (op : Op [⟨.value, σ⟩] [⟨.value, τ⟩])
    (xId : Nat) {rule : Op.Rule α [⟨.value, σ⟩] [⟨.value, τ⟩]}
    (hc : op.check = .ok ()) (hr : op.rule? (α := α) = some rule)
    (hv : rule.validate = fun _ => .ok ())
    {x : Tensor α σ} (hx : requireValue (s := σ) t xId = .ok x) :
    ∃ t', CpuTape.unary t name op xId = .ok (t', t.size) ∧
          requireValue (s := τ) t' t.size = .ok (rule.forward (x, ())).1 ∧ FrameOver t' t := by
  obtain ⟨node, hrun, -, -, hval⟩ := unary_node t name op xId hc hr hv hx
  exact ⟨_, hrun, requireValue_addNode_self t node hval, frameOver_addNode t node⟩

variable {s : Shape}

/-- `CpuTape.add` stores `a + b`. -/
theorem add_value (t : CpuTape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : requireValue (s := s) t aId = .ok a) (hb : requireValue (s := s) t bId = .ok b) :
    ∃ t', CpuTape.add (s := s) t aId bId = .ok (t', t.size) ∧
          requireValue (s := s) t' t.size = .ok (a + b) ∧ FrameOver t' t :=
  binary_value t _ _ aId bId _root_.rfl Op.rule?_add _root_.rfl ha hb

/-- `CpuTape.sub` stores `a - b`. -/
theorem sub_value (t : CpuTape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : requireValue (s := s) t aId = .ok a) (hb : requireValue (s := s) t bId = .ok b) :
    ∃ t', CpuTape.sub (s := s) t aId bId = .ok (t', t.size) ∧
          requireValue (s := s) t' t.size = .ok (a - b) ∧ FrameOver t' t :=
  binary_value t _ _ aId bId _root_.rfl Op.rule?_sub _root_.rfl ha hb

/-- `CpuTape.mul` stores `a * b`. -/
theorem mul_value (t : CpuTape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : requireValue (s := s) t aId = .ok a) (hb : requireValue (s := s) t bId = .ok b) :
    ∃ t', CpuTape.mul (s := s) t aId bId = .ok (t', t.size) ∧
          requireValue (s := s) t' t.size = .ok (a * b) ∧ FrameOver t' t :=
  binary_value t _ _ aId bId _root_.rfl Op.rule?_mul _root_.rfl ha hb

/-- `CpuTape.div` stores `a / b`. -/
theorem div_value (t : CpuTape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : requireValue (s := s) t aId = .ok a) (hb : requireValue (s := s) t bId = .ok b) :
    ∃ t', CpuTape.div (s := s) t aId bId = .ok (t', t.size) ∧
          requireValue (s := s) t' t.size = .ok (a / b) ∧ FrameOver t' t :=
  binary_value t _ _ aId bId _root_.rfl Op.rule?_div _root_.rfl ha hb

/-- `CpuTape.pow` stores `Tensor.pow a b`, the exponent read from the tape. -/
theorem pow_value (t : CpuTape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : requireValue (s := s) t aId = .ok a) (hb : requireValue (s := s) t bId = .ok b) :
    ∃ t', CpuTape.pow (s := s) t aId bId = .ok (t', t.size) ∧
          requireValue (s := s) t' t.size = .ok (Tensor.pow a b) ∧ FrameOver t' t :=
  binary_value t _ _ aId bId _root_.rfl Op.rule?_powValue _root_.rfl ha hb

/-- `CpuTape.min` stores `Tensor.minimum a b`. -/
theorem min_value (t : CpuTape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : requireValue (s := s) t aId = .ok a) (hb : requireValue (s := s) t bId = .ok b) :
    ∃ t', CpuTape.min (s := s) t aId bId = .ok (t', t.size) ∧
          requireValue (s := s) t' t.size = .ok (Tensor.minimum a b) ∧ FrameOver t' t :=
  binary_value t _ _ aId bId _root_.rfl Op.rule?_min _root_.rfl ha hb

/-- `CpuTape.max` stores `Tensor.maximum a b`. -/
theorem max_value (t : CpuTape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : requireValue (s := s) t aId = .ok a) (hb : requireValue (s := s) t bId = .ok b) :
    ∃ t', CpuTape.max (s := s) t aId bId = .ok (t', t.size) ∧
          requireValue (s := s) t' t.size = .ok (Tensor.maximum a b) ∧ FrameOver t' t :=
  binary_value t _ _ aId bId _root_.rfl Op.rule?_max _root_.rfl ha hb

/-- `CpuTape.fmin` stores `Tensor.fmin a b`. -/
theorem fmin_value (t : CpuTape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : requireValue (s := s) t aId = .ok a) (hb : requireValue (s := s) t bId = .ok b) :
    ∃ t', CpuTape.fmin (s := s) t aId bId = .ok (t', t.size) ∧
          requireValue (s := s) t' t.size = .ok (Tensor.fmin a b) ∧ FrameOver t' t :=
  binary_value t _ _ aId bId _root_.rfl Op.rule?_fmin _root_.rfl ha hb

/-- `CpuTape.fmax` stores `Tensor.fmax a b`. -/
theorem fmax_value (t : CpuTape α) (aId bId : Nat) {a b : Tensor α s}
    (ha : requireValue (s := s) t aId = .ok a) (hb : requireValue (s := s) t bId = .ok b) :
    ∃ t', CpuTape.fmax (s := s) t aId bId = .ok (t', t.size) ∧
          requireValue (s := s) t' t.size = .ok (Tensor.fmax a b) ∧ FrameOver t' t :=
  binary_value t _ _ aId bId _root_.rfl Op.rule?_fmax _root_.rfl ha hb

/-- `CpuTape.abs` stores `Tensor.abs x`. -/
theorem abs_value (t : CpuTape α) (xId : Nat) {x : Tensor α s}
    (hx : requireValue (s := s) t xId = .ok x) :
    ∃ t', CpuTape.abs (s := s) t xId = .ok (t', t.size) ∧
          requireValue (s := s) t' t.size = .ok (Tensor.abs x) ∧ FrameOver t' t :=
  unary_value t _ _ xId _root_.rfl Op.rule?_abs _root_.rfl hx

/-- `CpuTape.sqrt` stores the clamped root `Tensor.sqrt x .clampNegative`. -/
theorem sqrt_value (t : CpuTape α) (xId : Nat) {x : Tensor α s}
    (hx : requireValue (s := s) t xId = .ok x) :
    ∃ t', CpuTape.sqrt (s := s) t xId = .ok (t', t.size) ∧
          requireValue (s := s) t' t.size = .ok (Tensor.sqrt x .clampNegative) ∧
          FrameOver t' t :=
  unary_value t _ _ xId _root_.rfl Op.rule?_sqrt_clampNegative _root_.rfl hx

/-- `CpuTape.exp` stores `Tensor.exp x`. -/
theorem exp_value (t : CpuTape α) (xId : Nat) {x : Tensor α s}
    (hx : requireValue (s := s) t xId = .ok x) :
    ∃ t', CpuTape.exp (s := s) t xId = .ok (t', t.size) ∧
          requireValue (s := s) t' t.size = .ok (Tensor.exp x) ∧ FrameOver t' t :=
  unary_value t _ _ xId _root_.rfl Op.rule?_exp _root_.rfl hx

/-- `CpuTape.log` stores `Tensor.log x`. -/
theorem log_value (t : CpuTape α) (xId : Nat) {x : Tensor α s}
    (hx : requireValue (s := s) t xId = .ok x) :
    ∃ t', CpuTape.log (s := s) t xId = .ok (t', t.size) ∧
          requireValue (s := s) t' t.size = .ok (Tensor.log x) ∧ FrameOver t' t :=
  unary_value t _ _ xId _root_.rfl Op.rule?_log _root_.rfl hx

/-! ## Faithfulness-by-construction demonstrator

A symbolic kernel `g(a,b) = (a / b) + b` recorded on the tape, proved equal to `a / b + b` with
**no execution**: the inputs are abstract `Tensor α s`. Every intermediate value rewrites through a
`*_value` lemma, and the re-read of the earlier leaf `b` survives the `div` by `FrameOver`. -/

namespace Demo

/-- Leaf tape holding only `a` (node id `0`). -/
def ta (a : Tensor α s) : CpuTape α := (CpuTape.leaf (Tape.empty : CpuTape α) a).1

/-- Leaf tape holding `a` (id `0`) then `b` (id `1`). -/
def tab (a b : Tensor α s) : CpuTape α := (CpuTape.leaf (ta a) b).1

/-- The kernel `g(a,b) = (a / b) + b`: `div 0 1` (id 2), then `add 2 1` (id 3), re-reading leaf
`b` across the `div`. Returns the final node's value. -/
def kernel (a b : Tensor α s) : Result (Tensor α s) :=
  let t2 := tab a b
  do
    let (t3, id2) ← CpuTape.div (s := s) t2 0 1
    let (t4, id3) ← CpuTape.add (s := s) t3 id2 1
    requireValue (s := s) t4 id3

/-- **Faithfulness by construction**: the symbolic tape kernel equals its tensor term. -/
theorem kernel_eq_spec (a b : Tensor α s) :
    kernel a b = .ok (a / b + b) := by
  have hsz_e : (Tape.empty : CpuTape α).size = 0 := by simp [Tape.empty, Tape.size]
  have hsz_a : (ta a).size = 1 := by
    simp [ta, CpuTape.leaf, Tape.leaf, Tape.addNode, Tape.size, Tape.empty]
  have hsz_ab : (tab a b).size = 2 := by
    simp [tab, ta, CpuTape.leaf, Tape.leaf, Tape.addNode, Tape.size, Tape.empty]
  have hA_a : requireValue (s := s) (ta a) 0 = .ok a := by
    have h := leaf_value (Tape.empty : CpuTape α) a none true
    rwa [hsz_e] at h
  have hB_ab : requireValue (s := s) (tab a b) 1 = .ok b := by
    have h := leaf_value (ta a) b none true
    rwa [hsz_a] at h
  have hA_ab : requireValue (s := s) (tab a b) 0 = .ok a := by
    unfold tab CpuTape.leaf Tape.leaf
    rw [requireValue_addNode_of_lt (ta a) _ 0 (by rw [hsz_a]; decide)]
    exact hA_a
  obtain ⟨t3, hdiv, hv3, hf3⟩ := div_value (tab a b) 0 1 hA_ab hB_ab
  have hB_3 : requireValue (s := s) t3 1 = .ok b := by
    rw [hf3 (s := s) 1 (by rw [hsz_ab]; decide)]; exact hB_ab
  obtain ⟨t4, hadd, hv4, _⟩ := add_value t3 (tab a b).size 1 hv3 hB_3
  show (let t2 := tab a b;
        CpuTape.div (s := s) t2 0 1 >>= fun r3 =>
          CpuTape.add (s := s) r3.1 r3.2 1 >>= fun r4 =>
            requireValue (s := s) r4.1 r4.2) = _
  simp only []
  rw [hdiv]
  simp only [bind, Except.bind]
  rw [hadd]
  exact hv4

end Demo

end PropertyKindCalculus.Paradigm.TapeFaithful

end Blanket
