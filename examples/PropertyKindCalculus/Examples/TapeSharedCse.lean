/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import PropertyKindCalculus.Examples.TapeCseStructural
public import PropertyKindCalculus.Torch.Paradigm.TapeSharedCarrier
public import PropertyKindCalculus.Torch.Paradigm.TapeFaithful
public import Batteries.Data.Float.Lemmas

@[expose] public section Blanket

open TorchLean
open PropertyKindCalculus.Paradigm
open PropertyKindCalculus.Paradigm.TapeCSE (nodeKey cseCompact)
open PropertyKindCalculus.Examples.TapeCseStructural

namespace PropertyKindCalculus.Examples.TapeSharedCse

/-! ## Forward content and the pure emit step -/

/-- The forward content of a node: its name, operands and stored value (not its `backward`). -/
def fwd (n : CpuNode Float) : Option String × Array Nat × SomeTensor Float :=
  (n.name, n.parents, n.value)

/-- Two stored values with one shape and the same value bits are equal. -/
theorem value_eq_of_bits {v w : SomeTensor Float} (hs : v.shape = w.shape)
    (hb : (Storage.toArray v.tensor.buffer).toList.map Float.toBits
        = (Storage.toArray w.tensor.buffer).toList.map Float.toBits) : v = w := by
  obtain ⟨sv, ⟨bv, hv⟩⟩ := v
  obtain ⟨sw, ⟨bw, hw⟩⟩ := w
  cases hs
  have hinj : Function.Injective Float.toBits := fun _ _ h => Float.toBits_inj.mp h
  have hl := List.map_injective_iff.mpr hinj hb
  have hbuf : bv = bw := Storage.toArray_injective (Array.toList_inj.mp hl)
  subst hbuf
  rfl

/-- `SharedTapeM.emit` after its recorder has run: look `node` up, or append it. -/
def emitPure (σ : SharedTape) (node : CpuNode Float) : Nat × SharedTape :=
  match σ.memo[(node.value.shape, nodeKey #[] node)]? with
  | some id => (id, σ)
  | none =>
    (σ.tape.nodes.size,
      ⟨{ nodes := σ.tape.nodes.push node },
        σ.memo.insert (node.value.shape, nodeKey #[] node) σ.tape.nodes.size, σ.seen⟩)

/-- `emit` is `emitPure` on the node its recorder appended, with the operands set to `ps`. -/
theorem emit_eq (σ : SharedTape) (ps : Array Nat) (raw : TapeM Float Nat) (n' : CpuNode Float)
    (i : Nat) (h : raw σ.tape = .ok (i, (σ.tape.addNode n').1)) :
    SharedTapeM.emit ps raw σ = .ok (emitPure σ { n' with parents := ps }) := by
  obtain ⟨tape, memo, seen⟩ := σ
  simp only [SharedTapeM.emit, emitPure, h, bind, Except.bind, Tape.addNode, Array.back?_push,
    Array.pop_push, Array.size_push]
  cases memo[(n'.value.shape, nodeKey #[] { n' with parents := ps })]? <;> rfl

/-- `cseCompact`'s fold on a tape with one more node is one more step. -/
theorem cseFold_addNode (t : CpuTape Float) (n : CpuNode Float) :
    cseFold (t.addNode n).1 = cseStep (cseFold t) n := by
  simp [cseFold, Tape.addNode, cseInit]

/-- A key over operands that are already canonical. -/
theorem map_getD_empty (ps : Array Nat) : ps.map (fun p => (#[] : Array Nat).getD p p) = ps := by
  simp

/-! ## The simulation relation -/

/-- The sharing state `σ` holds the state `st` of `cseCompact`'s fold over the raw tape `t`, all
at shape `s`: the same forward content, the same memo, and the fold's invariants. -/
structure RelSt (s : Shape) (t : CpuTape Float) (st : CseState) (σ : SharedTape) : Prop where
  /-- The sharing tape has the forward content of the compacted tape. -/
  tape : σ.tape.nodes.map fwd = st.1.nodes.map fwd
  /-- The sharing memo at shape `s` is `cseCompact`'s memo. -/
  memo : ∀ k : Key, σ.memo[(s, k)]? = st.2.2[k]?
  /-- Every raw node has shape `s`. -/
  shape : ∀ n ∈ t.nodes, n.value.shape = s
  /-- Every compacted node has shape `s`. -/
  shapeC : ∀ n ∈ st.1.nodes, n.value.shape = s
  /-- The remap covers the raw tape. -/
  size : st.2.1.size = t.nodes.size
  /-- A raw node's image holds its value. -/
  value : ∀ id (h : id < t.nodes.size), ∃ nc,
    st.1.nodes[st.2.1.getD id id]? = some nc ∧ nc.value = t.nodes[id].value
  /-- A memo entry names a compacted node with that key. -/
  key : ∀ k nid, st.2.2[k]? = some nid → ∃ nc, st.1.nodes[nid]? = some nc ∧ nodeKey #[] nc = k

/-- The sharing state `σ` holds what `cseCompact` leaves of the raw tape `t`, at shape `s`. -/
abbrev Rel (s : Shape) (t : CpuTape Float) (σ : SharedTape) : Prop := RelSt s t (cseFold t) σ

/-- The sharing tape and the compacted tape have the same size. -/
theorem RelSt.tape_size {s : Shape} {t : CpuTape Float} {st : CseState} {σ : SharedTape}
    (h : RelSt s t st σ) : σ.tape.nodes.size = st.1.nodes.size := by
  simpa using congrArg Array.size h.tape

/-- The empty recordings are related. -/
theorem Rel.empty (s : Shape) : Rel s Tape.empty {} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [cseFold, cseInit, Tape.empty]

theorem RelSt.step {s : Shape} {t : CpuTape Float} {st : CseState} {σ : SharedTape}
    (h : RelSt s t st σ)
    {n node : CpuNode Float} (hs : n.value.shape = s) (hn : node.name = n.name)
    (hv : node.value = n.value)
    (hp : node.parents = n.parents.map (fun p => st.2.1.getD p p)) :
    RelSt s (t.addNode n).1 (cseStep st n) (emitPure σ node).2 ∧
    (emitPure σ node).1 = (cseStep st n).2.1.getD t.nodes.size t.nodes.size ∧
    ∀ i, i < t.nodes.size → (cseStep st n).2.1.getD i i = st.2.1.getD i i := by
  obtain ⟨c, rm, m⟩ := st
  simp only at h hp ⊢
  have hkey : nodeKey #[] node = nodeKey rm n := by
    unfold nodeKey
    rw [hn, hv, hp]
    simp
  have hsz := h.tape_size
  have hlook : σ.memo[(node.value.shape, nodeKey #[] node)]? = m[nodeKey rm n]? := by
    rw [hv, hs, hkey]; exact h.memo _
  have hshape : ∀ x ∈ (t.addNode n).1.nodes, x.value.shape = s := by
    intro x hmem
    simp only [Tape.addNode, Array.mem_push] at hmem
    rcases hmem with hmem | rfl
    · exact h.shape x hmem
    · exact hs
  cases hm : m[nodeKey rm n]? with
  | some nid =>
    have e1 : cseStep (c, rm, m) n = (c, rm.push nid, m) := by simp [cseStep, hm]
    have e2 : emitPure σ node = (nid, σ) := by simp [emitPure, hlook, hm]
    rw [e1, e2]
    obtain ⟨nc, hnc, hk⟩ := h.key _ _ hm
    have hncs : nc.value.shape = s := h.shapeC nc (Array.mem_of_getElem? hnc)
    have hval : nc.value = n.value := by
      apply value_eq_of_bits (hncs.trans hs.symm)
      have := congrArg (fun k => k.2.2) hk
      simpa [nodeKey] using this
    refine ⟨⟨h.tape, h.memo, hshape, h.shapeC, ?_, ?_, h.key⟩, ?_, ?_⟩
    · simpa [Tape.addNode] using h.size
    · intro id hid
      simp only [Tape.addNode, Array.size_push] at hid
      by_cases hlt : id < t.nodes.size
      · obtain ⟨nc', h1, h2⟩ := h.value id hlt
        refine ⟨nc', ?_, ?_⟩
        · show c.nodes[(rm.push nid).getD id id]? = some nc'
          rw [getD_push_lt _ _ _ _ (h.size ▸ hlt)]; exact h1
        · simpa [Tape.addNode, Array.getElem_push_lt hlt] using h2
      · have hid' : id = t.nodes.size := by omega
        subst hid'
        refine ⟨nc, ?_, ?_⟩
        · show c.nodes[(rm.push nid).getD t.nodes.size t.nodes.size]? = some nc
          rw [getD_push_at _ _ _ _ h.size.symm]; exact hnc
        · simpa [Tape.addNode] using hval
    · show nid = (rm.push nid).getD t.nodes.size t.nodes.size
      rw [getD_push_at _ _ _ _ h.size.symm]
    · intro i hi
      show (rm.push nid).getD i i = rm.getD i i
      exact getD_push_lt _ _ _ _ (h.size ▸ hi)
  | none =>
    have e1 : cseStep (c, rm, m) n =
        ((c.addNode { n with parents := n.parents.map (fun p => rm.getD p p) }).1,
         rm.push c.nodes.size, m.insert (nodeKey rm n) c.nodes.size) := by
      simp [cseStep, hm, Tape.addNode]
    have e2 : emitPure σ node = (σ.tape.nodes.size,
        ⟨{ nodes := σ.tape.nodes.push node },
          σ.memo.insert (s, nodeKey rm n) σ.tape.nodes.size, σ.seen⟩) := by
      have hl2 : σ.memo[(s, nodeKey rm n)]? = none := (h.memo _).trans hm
      simp [emitPure, hv, hs, hkey, hl2]
    rw [e1, e2]
    have hsz' : σ.tape.nodes.size = c.nodes.size := hsz
    have hne : ∀ {i : Nat} {x : CpuNode Float}, c.nodes[i]? = some x → i ≠ c.nodes.size := by
      intro i x hx hi
      subst hi
      simp at hx
    refine ⟨⟨?_, ?_, hshape, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp only [Tape.addNode, Array.map_push, h.tape]
      congr 1
      simp [fwd, hn, hv, hp]
    · intro k
      simp only [Std.HashMap.getElem?_insert, hsz', h.memo k]
      by_cases hk : nodeKey rm n = k <;> simp [hk]
    · intro x hmem
      simp only [Tape.addNode, Array.mem_push] at hmem
      rcases hmem with hmem | rfl
      · exact h.shapeC x hmem
      · exact hs
    · simpa [Tape.addNode] using h.size
    · intro id hid
      simp only [Tape.addNode, Array.size_push] at hid
      by_cases hlt : id < t.nodes.size
      · obtain ⟨nc', h1, h2⟩ := h.value id hlt
        refine ⟨nc', ?_, ?_⟩
        · show (c.nodes.push _)[(rm.push c.nodes.size).getD id id]? = some nc'
          rw [getD_push_lt _ _ _ _ (h.size ▸ hlt), Array.getElem?_push, if_neg (hne h1)]
          exact h1
        · simpa [Tape.addNode, Array.getElem_push_lt hlt] using h2
      · have hid' : id = t.nodes.size := by omega
        subst hid'
        refine ⟨{ n with parents := n.parents.map (fun p => rm.getD p p) }, ?_, ?_⟩
        · show (c.nodes.push _)[(rm.push c.nodes.size).getD t.nodes.size t.nodes.size]? = some _
          rw [getD_push_at _ _ _ _ h.size.symm, Array.getElem?_push_size]
        · simp [Tape.addNode]
    · intro k nid hk
      rw [Std.HashMap.getElem?_insert] at hk
      by_cases hkk : nodeKey rm n = k
      · simp only [hkk, beq_self_eq_true, if_true, Option.some.injEq] at hk
        subst hk
        refine ⟨{ n with parents := n.parents.map (fun p => rm.getD p p) },
          by simp [Tape.addNode], ?_⟩
        rw [← hkk]
        simp [nodeKey]
      · simp only [beq_iff_eq, hkk, if_false] at hk
        obtain ⟨nc, h1, h2⟩ := h.key k nid hk
        refine ⟨nc, ?_, h2⟩
        show (c.nodes.push _)[nid]? = some nc
        rw [Array.getElem?_push, if_neg (hne h1)]
        exact h1
    · show σ.tape.nodes.size = (rm.push c.nodes.size).getD t.nodes.size t.nodes.size
      rw [getD_push_at _ _ _ _ h.size.symm, hsz']
    · intro i hi
      show (rm.push c.nodes.size).getD i i = rm.getD i i
      exact getD_push_lt _ _ _ _ (h.size ▸ hi)

/-- **One recorded node.** If the raw recorder appends `n` and the sharing recorder emits a
`node` with `n`'s name and value and `n`'s operands remapped, the relation is kept, the sharing id
is the remap of the raw id, and earlier remaps do not move. -/
theorem Rel.step {s : Shape} {t : CpuTape Float} {σ : SharedTape} (h : Rel s t σ)
    {n node : CpuNode Float} (hs : n.value.shape = s) (hn : node.name = n.name)
    (hv : node.value = n.value)
    (hp : node.parents = n.parents.map (fun p => (cseFold t).2.1.getD p p)) :
    Rel s (t.addNode n).1 (emitPure σ node).2 ∧
    (emitPure σ node).1 = (cseFold (t.addNode n).1).2.1.getD t.nodes.size t.nodes.size ∧
    ∀ i, i < t.nodes.size →
      (cseFold (t.addNode n).1).2.1.getD i i = (cseFold t).2.1.getD i i := by
  unfold Rel
  rw [cseFold_addNode]
  exact RelSt.step h hs hn hv hp

/-! ## The recorders read only their operands' values -/

open TorchLean.Tape in
/-- The node a binary table operator appends, with its operands when they are two nodes: an alias
rule on positions 0 and 1 fires only when both name one node. -/
theorem binary_node_ne {σ₁ σ₂ τ : Shape}
    (t : CpuTape Float) (name : String) (op : Op [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] [⟨.value, τ⟩])
    (aId bId : Nat) {rule : Op.Rule Float [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] [⟨.value, τ⟩]}
    (hc : op.check = .ok ()) (hr : op.rule? (α := Float) = some rule)
    (hv : rule.validate = fun _ => .ok ())
    (hal : ∀ r, rule.alias? = some r → r.first.val = 0 ∧ r.second.val = 1)
    {a : Tensor Float σ₁} {b : Tensor Float σ₂}
    (ha : requireValue (s := σ₁) t aId = .ok a) (hb : requireValue (s := σ₂) t bId = .ok b) :
    ∃ node : CpuNode Float,
      CpuTape.binary t name op aId bId = .ok ((t.addNode node).1, t.size) ∧
      node.name = some name ∧ (aId ≠ bId → node.parents = #[aId, bId]) ∧
      node.value = SomeTensor.ofTensor (rule.forward (a, b, ())).1 := by
  have hread : Args.read t [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] (aId, bId, ()) = .ok (a, b, ()) := by
    simp [Args.read, Arg.read, ha, hb, bind, Except.bind, pure, Except.pure]
  have hpv := prepared_value rule
    (Args.ids [⟨.value, σ₁⟩, ⟨.value, σ₂⟩]
      (show Args Float [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] from (aId, bId, ()))) (a, b, ())
    (Args.flags t [⟨.value, σ₁⟩, ⟨.value, σ₂⟩] (aId, bId, ()))
  unfold CpuTape.binary Tape.apply
  simp only [hc, hr, hread, hv, bind, Except.bind, record, valuePorts,
    List.countP_singleton, beq_self_eq_true, ite_true, gt_iff_lt, Nat.lt_irrefl, ite_false, pure,
    Except.pure]
  refine ⟨_, _root_.rfl, _root_.rfl, fun hab => ?_,
    congrArg (fun v : Values Float [⟨.value, τ⟩] => SomeTensor.ofTensor v.1) hpv⟩
  cases hr' : rule.alias? with
  | none => simp [recordedNode, Args.ids, Arg.id?, prepared, aliasOf, hr', List.finRange]
  | some r =>
    obtain ⟨h0, h1⟩ := hal r hr'
    simp [recordedNode, Args.ids, Arg.id?, prepared, aliasOf, hr', List.finRange, h0, h1, hab]

/-- A binary recorder on two tapes whose operands read the same values appends nodes with the
same name and value. -/
theorem bin_natural {s : Shape} (name : String)
    (op : Op [⟨.value, s⟩, ⟨.value, s⟩] [⟨.value, s⟩])
    {rule : Op.Rule Float [⟨.value, s⟩, ⟨.value, s⟩] [⟨.value, s⟩]}
    (hc : op.check = .ok ()) (hr : op.rule? (α := Float) = some rule)
    (hv : rule.validate = fun _ => .ok ())
    (hal : ∀ r, rule.alias? = some r → r.first.val = 0 ∧ r.second.val = 1)
    (T T' : CpuTape Float) (a b a' b' : Nat) {va vb : Tensor Float s}
    (ha : Tape.requireValue (s := s) T a = .ok va) (hb : Tape.requireValue (s := s) T b = .ok vb)
    (ha' : Tape.requireValue (s := s) T' a' = .ok va)
    (hb' : Tape.requireValue (s := s) T' b' = .ok vb) :
    ∃ n n' : CpuNode Float,
      (TapeM.record fun t => CpuTape.binary t name op a b) T
        = .ok (T.nodes.size, (T.addNode n).1) ∧
      (TapeM.record fun t => CpuTape.binary t name op a' b') T'
        = .ok (T'.nodes.size, (T'.addNode n').1) ∧
      n'.name = n.name ∧ n'.value = n.value ∧ n.value.shape = s ∧
      (a ≠ b → n.parents = #[a, b]) := by
  obtain ⟨n, h1, h2, h3, h4⟩ := binary_node_ne T name op a b hc hr hv hal ha hb
  obtain ⟨n', h1', h2', -, h4'⟩ := binary_node_ne T' name op a' b' hc hr hv hal ha' hb'
  refine ⟨n, n', ?_, ?_, h2'.trans h2.symm, h4'.trans h4.symm, by rw [h4]; rfl, h3⟩
  · simp [TapeM.record, h1, Except.map, Tape.size]
  · simp [TapeM.record, h1', Except.map, Tape.size]

/-- A unary recorder on two tapes whose operand reads the same value appends nodes with the same
name and value. -/
theorem un_natural {s : Shape} (name : String) (op : Op [⟨.value, s⟩] [⟨.value, s⟩])
    {rule : Op.Rule Float [⟨.value, s⟩] [⟨.value, s⟩]}
    (hc : op.check = .ok ()) (hr : op.rule? (α := Float) = some rule)
    (hv : rule.validate = fun _ => .ok ()) (hal : rule.alias? = none)
    (T T' : CpuTape Float) (a a' : Nat) {va : Tensor Float s}
    (ha : Tape.requireValue (s := s) T a = .ok va)
    (ha' : Tape.requireValue (s := s) T' a' = .ok va) :
    ∃ n n' : CpuNode Float,
      (TapeM.record fun t => CpuTape.unary t name op a) T
        = .ok (T.nodes.size, (T.addNode n).1) ∧
      (TapeM.record fun t => CpuTape.unary t name op a') T'
        = .ok (T'.nodes.size, (T'.addNode n').1) ∧
      n'.name = n.name ∧ n'.value = n.value ∧ n.value.shape = s ∧ n.parents = #[a] := by
  obtain ⟨n, h1, h2, h3, h4⟩ := TapeFaithful.unary_node T name op a hc hr hv ha
  obtain ⟨n', h1', h2', -, h4'⟩ := TapeFaithful.unary_node T' name op a' hc hr hv ha'
  refine ⟨n, n', ?_, ?_, h2'.trans h2.symm, h4'.trans h4.symm, by rw [h4]; rfl, h3 hal⟩
  · simp [TapeM.record, h1, Except.map, Tape.size]
  · simp [TapeM.record, h1', Except.map, Tape.size]

/-- Whether a `SharedOp` takes two operands. -/
def binary : SharedOp → Bool
  | .exp | .log | .abs | .sqrt => false
  | _ => true

/-- **A `SharedOp` reads only its operands' values.** On two tapes whose operands read the same
values, its recorder appends nodes with the same name and value; on the first tape the node's
operands are the ids it was given, when a binary op is given two nodes. -/
theorem raw_natural (o : SharedOp) (s : Shape) (T T' : CpuTape Float) (ps ps' : Array Nat)
    {v0 v1 : Tensor Float s}
    (h0 : Tape.requireValue (s := s) T (ps.getD 0 0) = .ok v0)
    (h1 : Tape.requireValue (s := s) T (ps.getD 1 0) = .ok v1)
    (h0' : Tape.requireValue (s := s) T' (ps'.getD 0 0) = .ok v0)
    (h1' : Tape.requireValue (s := s) T' (ps'.getD 1 0) = .ok v1) :
    ∃ n n' : CpuNode Float,
      (o.raw s ps) T = .ok (T.nodes.size, (T.addNode n).1) ∧
      (o.raw s ps') T' = .ok (T'.nodes.size, (T'.addNode n').1) ∧
      n'.name = n.name ∧ n'.value = n.value ∧ n.value.shape = s ∧
      (if binary o then ps.getD 0 0 ≠ ps.getD 1 0 → n.parents = #[ps.getD 0 0, ps.getD 1 0]
       else n.parents = #[ps.getD 0 0]) := by
  cases o
  case add => exact bin_natural _ _ rfl Op.rule?_add rfl (by simp) T T' _ _ _ _ h0 h1 h0' h1'
  case sub => exact bin_natural _ _ rfl Op.rule?_sub rfl (by simp) T T' _ _ _ _ h0 h1 h0' h1'
  case mul => exact bin_natural _ _ rfl Op.rule?_mul rfl (by simp) T T' _ _ _ _ h0 h1 h0' h1'
  case div => exact bin_natural _ _ rfl Op.rule?_div rfl (by simp) T T' _ _ _ _ h0 h1 h0' h1'
  case min => exact bin_natural _ _ rfl Op.rule?_min rfl (by simp) T T' _ _ _ _ h0 h1 h0' h1'
  case max => exact bin_natural _ _ rfl Op.rule?_max rfl (by simp) T T' _ _ _ _ h0 h1 h0' h1'
  case fmin => exact bin_natural _ _ rfl Op.rule?_fmin rfl (by simp) T T' _ _ _ _ h0 h1 h0' h1'
  case fmax => exact bin_natural _ _ rfl Op.rule?_fmax rfl (by simp) T T' _ _ _ _ h0 h1 h0' h1'
  case exp => exact un_natural _ _ rfl Op.rule?_exp rfl rfl T T' _ _ h0 h0'
  case log => exact un_natural _ _ rfl Op.rule?_log rfl rfl T T' _ _ h0 h0'
  case abs => exact un_natural _ _ rfl Op.rule?_abs rfl rfl T T' _ _ h0 h0'
  case sqrt =>
    exact un_natural _ _ rfl Op.rule?_sqrt_clampNegative rfl rfl T T' _ _ h0 h0'

/-! ## Reading an operand on both tapes -/

/-- A node of shape `s` reads back as a tensor of shape `s`. -/
theorem read_of_node {s : Shape} {T : CpuTape Float} {id : Nat} {n : CpuNode Float}
    (hn : T.nodes[id]? = some n) (hs : n.value.shape = s) :
    Tape.requireValue (s := s) T id = .ok (n.value.cast hs) := by
  unfold Tape.requireValue
  simp [Tape.getValue?, Tape.getNode?, hn, hs]

/-- Equal stored values cast to equal tensors. -/
theorem cast_congr {s : Shape} {v w : SomeTensor Float} (h : v = w) (hv : v.shape = s)
    (hw : w.shape = s) : v.cast hv = w.cast hw := by
  subst h
  rfl

/-- A raw id and its remap read the same tensor, on the raw tape and on the sharing tape. -/
theorem RelSt.read {s : Shape} {t : CpuTape Float} {st : CseState} {σ : SharedTape}
    (h : RelSt s t st σ) {id : Nat} (hid : id < t.nodes.size) :
    ∃ v : Tensor Float s, Tape.requireValue (s := s) t id = .ok v ∧
      Tape.requireValue (s := s) σ.tape (st.2.1.getD id id) = .ok v ∧
      st.2.1.getD id id < σ.tape.nodes.size := by
  obtain ⟨nc, hnc, hval⟩ := h.value id hid
  have hsh : t.nodes[id].value.shape = s := h.shape _ (Array.getElem_mem hid)
  have hlt : st.2.1.getD id id < st.1.nodes.size := by
    by_contra hge
    rw [Array.getElem?_eq_none (by omega)] at hnc
    cases hnc
  have hlt' : st.2.1.getD id id < σ.tape.nodes.size := h.tape_size ▸ hlt
  have hσ : fwd σ.tape.nodes[st.2.1.getD id id] = fwd nc := by
    have h1 := congrArg (fun a => a[st.2.1.getD id id]?) h.tape
    simp only [Array.getElem?_map, hnc, Array.getElem?_eq_getElem hlt', Option.map_some,
      Option.some.injEq] at h1
    exact h1
  have hσv : σ.tape.nodes[st.2.1.getD id id].value = t.nodes[id].value := by
    have := congrArg (fun a => a.2.2) hσ
    exact this.trans hval
  refine ⟨t.nodes[id].value.cast hsh, read_of_node (Array.getElem?_eq_getElem hid) hsh, ?_, hlt'⟩
  rw [read_of_node (Array.getElem?_eq_getElem hlt') (hσv ▸ hsh)]
  exact congrArg _ (cast_congr hσv _ _)

end PropertyKindCalculus.Examples.TapeSharedCse

end Blanket
