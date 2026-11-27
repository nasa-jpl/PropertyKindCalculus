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

/-- The id a `SharedOp` reads as its second operand (a unary op reads its only operand). -/
def snd (o : SharedOp) (ps : Array Nat) : Nat :=
  match binary o with
  | true => ps.getD 1 0
  | false => ps.getD 0 0

/-- **A `SharedOp` reads only its operands' values.** On two tapes whose operands read the same
values, its recorder appends nodes with the same name and value; on the first tape the node's
operands are the ids it was given, when a binary op is given two nodes. -/
theorem raw_natural (o : SharedOp) (s : Shape) (T T' : CpuTape Float) (ps ps' : Array Nat)
    {v0 v1 : Tensor Float s}
    (h0 : Tape.requireValue (s := s) T (ps.getD 0 0) = .ok v0)
    (h1 : Tape.requireValue (s := s) T (snd o ps) = .ok v1)
    (h0' : Tape.requireValue (s := s) T' (ps'.getD 0 0) = .ok v0)
    (h1' : Tape.requireValue (s := s) T' (snd o ps') = .ok v1) :
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

/-! ## The lookup-before-run table -/

/-- What an op at shape `s` appends on operands reading `v0` and `v1`, on any tape: a node named
`nm` storing `val`. -/
def Spec (o : SharedOp) (s : Shape) (v0 v1 : Tensor Float s) (nm : Option String)
    (val : SomeTensor Float) : Prop :=
  val.shape = s ∧ ∀ (T : CpuTape Float) (ps : Array Nat),
    Tape.requireValue (s := s) T (ps.getD 0 0) = .ok v0 →
    Tape.requireValue (s := s) T (snd o ps) = .ok v1 →
    ∃ n : CpuNode Float, (o.raw s ps) T = .ok (T.nodes.size, (T.addNode n).1) ∧
      n.name = nm ∧ n.value = val ∧
      (if binary o then ps.getD 0 0 ≠ ps.getD 1 0 → n.parents = #[ps.getD 0 0, ps.getD 1 0]
       else n.parents = #[ps.getD 0 0])

/-- Every op has a `Spec` at the values its operands read. -/
theorem raw_spec (o : SharedOp) (s : Shape) (T : CpuTape Float) (ps : Array Nat)
    {v0 v1 : Tensor Float s}
    (h0 : Tape.requireValue (s := s) T (ps.getD 0 0) = .ok v0)
    (h1 : Tape.requireValue (s := s) T (snd o ps) = .ok v1) :
    ∃ nm val, Spec o s v0 v1 nm val := by
  obtain ⟨n, -, hr, -, -, -, hsh, -⟩ := raw_natural o s T T ps ps h0 h1 h0 h1
  refine ⟨n.name, n.value, hsh, fun T' ps' g0 g1 => ?_⟩
  obtain ⟨m, m', k, k', kn, kv, -, kp⟩ := raw_natural o s T' T ps' ps g0 g1 h0 h1
  have e : (T.addNode n).1 = (T.addNode m').1 :=
    (Prod.mk.inj (Except.ok.inj (hr.symm.trans k'))).2
  have e' := congrArg (fun t : CpuTape Float => t.nodes.back?) e
  simp only [Tape.addNode, Array.back?_push, Option.some.injEq] at e'
  subst e'
  exact ⟨m, k, kn.symm, kv.symm, kp⟩

/-- The key depends on a node's name, operands and value only. -/
theorem nodeKey_congr {a b : CpuNode Float} (hn : a.name = b.name) (hp : a.parents = b.parents)
    (hv : a.value = b.value) : nodeKey #[] a = nodeKey #[] b := by
  unfold nodeKey
  rw [hn, hp, hv]

/-- **The lookup table is sound.** Each entry names the node the memo holds for what the op
would append: running the op and looking its node up returns the entry. -/
def Seen (s : Shape) (σ : SharedTape) : Prop :=
  ∀ (o : SharedOp) (ps : Array Nat) (id : Nat), σ.seen[(o, s, ps)]? = some id →
    ∃ (v0 v1 : Tensor Float s) (node : CpuNode Float),
      ps.getD 0 0 < σ.tape.nodes.size ∧ snd o ps < σ.tape.nodes.size ∧
      Tape.requireValue (s := s) σ.tape (ps.getD 0 0) = .ok v0 ∧
      Tape.requireValue (s := s) σ.tape (snd o ps) = .ok v1 ∧
      Spec o s v0 v1 node.name node.value ∧ node.parents = ps ∧
      σ.memo[(s, nodeKey #[] node)]? = some id

theorem Seen.empty (s : Shape) : Seen s {} := by
  intro o ps id h
  simp at h

/-- Emitting a node keeps the lookup table sound: the tape and the memo only grow. -/
theorem Seen.emitPure {s : Shape} {σ : SharedTape} (h : Seen s σ) (node : CpuNode Float) :
    Seen s (emitPure σ node).2 := by
  unfold TapeSharedCse.emitPure
  split
  · exact h
  · rename_i hnone
    intro o ps id hseen
    obtain ⟨v0, v1, nd, b0, b1, r0, r1, sp, hps, hm⟩ := h o ps id hseen
    refine ⟨v0, v1, nd, ?_, ?_, ?_, ?_, sp, hps, ?_⟩
    · simp only [Array.size_push]; omega
    · simp only [Array.size_push]; omega
    · exact (TapeFaithful.requireValue_addNode_of_lt σ.tape node _ b0).trans r0
    · exact (TapeFaithful.requireValue_addNode_of_lt σ.tape node _ b1).trans r1
    · show (σ.memo.insert _ _)[(s, nodeKey #[] nd)]? = some id
      rw [Std.HashMap.getElem?_insert]
      split
      · rename_i heq
        rw [← beq_iff_eq.mp heq, hnone] at hm
        cases hm
      · exact hm

/-- The relation does not read the lookup table. -/
theorem RelSt.withSeen {s : Shape} {t : CpuTape Float} {st : CseState} {σ : SharedTape}
    (h : RelSt s t st σ) (seen : Std.HashMap (SharedOp × Shape × Array Nat) Nat) :
    RelSt s t st { σ with seen := seen } :=
  ⟨h.tape, h.memo, h.shape, h.shapeC, h.size, h.value, h.key⟩

/-- After emitting a node, the memo holds its key at the id returned. -/
theorem emitPure_memo {s : Shape} (σ : SharedTape) (node : CpuNode Float)
    (hs : node.value.shape = s) :
    (emitPure σ node).2.memo[(s, nodeKey #[] node)]? = some (emitPure σ node).1 := by
  subst hs
  unfold emitPure
  split
  · rename_i h; exact h
  · exact Std.HashMap.getElem?_insert_self

/-- Emitting a node keeps what earlier ids read. -/
theorem emitPure_read {s : Shape} (σ : SharedTape) (node : CpuNode Float) {i : Nat}
    {v : Tensor Float s} (hi : i < σ.tape.nodes.size)
    (h : Tape.requireValue (s := s) σ.tape i = .ok v) :
    i < (emitPure σ node).2.tape.nodes.size ∧
      Tape.requireValue (s := s) (emitPure σ node).2.tape i = .ok v := by
  unfold emitPure
  split
  · exact ⟨hi, h⟩
  · refine ⟨?_, (TapeFaithful.requireValue_addNode_of_lt σ.tape node _ hi).trans h⟩
    simp only [Array.size_push]; omega

/-- **One op, both recorders.** On raw operands `ps` and their remaps `ps'`, the raw recorder
appends a node and `SharedTapeM.op` returns the remap of its id, keeping the relation and the
lookup table. -/
theorem op_step {s : Shape} {t : CpuTape Float} {σ : SharedTape} (hR : Rel s t σ)
    (hS : Seen s σ) (o : SharedOp) (ps ps' : Array Nat)
    (h0 : ps.getD 0 0 < t.nodes.size) (h1 : snd o ps < t.nodes.size)
    (e0 : ps'.getD 0 0 = (cseFold t).2.1.getD (ps.getD 0 0) (ps.getD 0 0))
    (e1 : snd o ps' = (cseFold t).2.1.getD (snd o ps) (snd o ps))
    (hne : binary o = true → ps.getD 0 0 ≠ ps.getD 1 0)
    (hpar : ps' = (if binary o then #[ps.getD 0 0, ps.getD 1 0] else #[ps.getD 0 0]).map
      (fun p => (cseFold t).2.1.getD p p)) :
    ∃ (n : CpuNode Float) (σ' : SharedTape),
      (o.raw s ps) t = .ok (t.nodes.size, (t.addNode n).1) ∧
      SharedTapeM.op o s ps' σ
        = .ok ((cseFold (t.addNode n).1).2.1.getD t.nodes.size t.nodes.size, σ') ∧
      Rel s (t.addNode n).1 σ' ∧ Seen s σ' ∧
      ∀ i, i < t.nodes.size →
        (cseFold (t.addNode n).1).2.1.getD i i = (cseFold t).2.1.getD i i := by
  obtain ⟨v0, r0, r0', b0⟩ := hR.read h0
  obtain ⟨v1, r1, r1', b1⟩ := hR.read h1
  rw [← e0] at r0' b0
  rw [← e1] at r1' b1
  have parents : ∀ n : CpuNode Float,
      (if binary o then ps.getD 0 0 ≠ ps.getD 1 0 → n.parents = #[ps.getD 0 0, ps.getD 1 0]
        else n.parents = #[ps.getD 0 0]) →
      ps' = n.parents.map (fun p => (cseFold t).2.1.getD p p) := by
    intro n hn
    rw [hpar]
    cases hb : binary o
    · simp only [hb, Bool.false_eq_true, ite_false] at hn; rw [hn]; simp
    · simp only [hb, ite_true] at hn; rw [hn (hne hb)]; simp
  cases hseen : σ.seen[(o, s, ps')]? with
  | some id =>
    obtain ⟨w0, w1, nd, -, -, q0, q1, sp, hps, hm⟩ := hS o ps' id hseen
    obtain rfl : w0 = v0 := Except.ok.inj (q0.symm.trans r0')
    obtain rfl : w1 = v1 := Except.ok.inj (q1.symm.trans r1')
    obtain ⟨n, hrun, hnm, hval, hpar'⟩ := sp.2 t ps r0 r1
    have step := Rel.step hR (n := n) (node := nd) (hval ▸ sp.1) hnm.symm hval.symm
      (hps.trans (parents n hpar'))
    have hemit : emitPure σ nd = (id, σ) := by
      unfold emitPure
      rw [sp.1, hm]
    rw [hemit] at step
    refine ⟨n, σ, hrun, ?_, step.1, hS, step.2.2⟩
    rw [← step.2.1]
    simp [SharedTapeM.op, hseen, pure, Except.pure]
  | none =>
    obtain ⟨nm, val, sp⟩ := raw_spec o s t ps r0 r1
    obtain ⟨n, hrun, hnm, hval, hpar'⟩ := sp.2 t ps r0 r1
    obtain ⟨n', hrun', hnm', hval', -⟩ := sp.2 σ.tape ps' r0' r1'
    have hsh : ({ n' with parents := ps' } : CpuNode Float).value.shape = s := hval' ▸ sp.1
    have step := Rel.step hR (n := n) (node := { n' with parents := ps' }) (hval ▸ sp.1)
      (hnm'.trans hnm.symm) (hval'.trans hval.symm) (parents n hpar')
    have hemit := emit_eq σ ps' (o.raw s ps') n' _ hrun'
    generalize hE : emitPure σ { n' with parents := ps' } = E at step hemit
    refine ⟨n, { E.2 with seen := E.2.seen.insert (o, s, ps') E.1 }, hrun, ?_,
      step.1.withSeen _, ?_, step.2.2⟩
    · rw [← step.2.1]
      simp [SharedTapeM.op, hseen, hemit, bind, Except.bind, pure, Except.pure]
    · intro o2 ps2 id2 hs2
      simp only [Std.HashMap.getElem?_insert] at hs2
      split at hs2
      · rename_i heq
        have heq' := beq_iff_eq.mp heq
        obtain ⟨rfl, hh⟩ := Prod.mk.inj heq'
        obtain rfl : ps' = ps2 := (Prod.mk.inj hh).2
        obtain rfl := Option.some.inj hs2
        have m0 := emitPure_read σ { n' with parents := ps' } b0 r0'
        have m1 := emitPure_read σ { n' with parents := ps' } b1 r1'
        rw [hE] at m0 m1
        refine ⟨v0, v1, { n' with parents := ps' }, m0.1, m1.1, m0.2, m1.2, ?_, rfl, ?_⟩
        · show Spec o s v0 v1 n'.name n'.value
          rw [hnm', hval']; exact sp
        · have := emitPure_memo σ { n' with parents := ps' } hsh
          rw [hE] at this
          exact this
      · have := Seen.emitPure hS { n' with parents := ps' }
        rw [hE] at this
        exact this o2 ps2 id2 hs2

end PropertyKindCalculus.Examples.TapeSharedCse

end Blanket
