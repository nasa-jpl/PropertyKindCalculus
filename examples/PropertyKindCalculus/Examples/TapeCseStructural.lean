/-
`examples.tape_cse_structural` — **`cseCompact` preserves every node's structure and value across the
whole hash-cons pass**, for an *arbitrary* well-formed tape. This is the whole-pass lift of
`examples.tape_codegen_end_to_end`'s node-local `cseKey_denotation_sound`, and the general form of its
machine-checked `#guard cse_preserves_resJac`.

`paradigm.tape_cse.cseCompact` walks a recorded tape in id order, hash-consing structurally-identical
nodes onto one surviving node (`paradigm.tape_cse`). `cseKey_denotation_sound` showed the *merge key*
is denotation-sound node-locally (two nodes sharing a key are interchangeable under `evalTape`); the
`#guard` checked, on the one deployed `resJac` tape, that every node's stored value survives
bit-identically. The gap both leave open is the **whole pass**: does the surviving node that
`cseCompact` picks for *each* original id actually carry the same op, the same (remapped) inputs, and
the same value — for every id, on every tape?

This module closes that gap with a `Std.HashMap`/remap/newTape **loop invariant** (`Inv`). Reformulating
`cseCompact`'s `Id.run` `for`-loop as a left fold (`cseCompact_eq_foldl`), the invariant — preserved at
each node (`inv_step`) and established by `Array.foldl_induction` (`cseFold_inv`) — states that after
processing `k` nodes:

* the compacted tape stays **well-formed** (parents precede children), and
* for every processed original id, its remapped id is in range and the stored node there has the
  **same op name**, **parents remapped by the same map**, and a **bit-identical stored value**, and
* every memo entry is backed by such a node (the bookkeeping that makes merges sound).

From it: `cseCompact_structural` (the per-node correspondence over the whole tape),
`cseCompact_wellFormed` (the compacted tape is well-formed), and `cseCompact_preserves_stored` (the
value-bit half — the arbitrary-tape generalisation of `cse_preserves_resJac`). Since `evalTape`/`cOp`
reads exactly a node's op name and remapped parents (op nodes) or its stored value (const leaves), the
correspondence is precisely the data an `evalTape`-denotation preservation theorem consumes. No
`Float.toBits` injectivity is used anywhere here — the invariant is about op names, ids, and bit
patterns.

Plain leaf module (nothing imports it). Builds under the `Examples` glob, so CI checks it, and the
axiom audit at the end certifies it sorry-free.
-/
import PropertyKindCalculus.Torch.Paradigm.TapeCse

open Spec
open Spec.Tensor
open Runtime.Autograd (Tape Node TapeM)
open PropertyKindCalculus.Paradigm.TapeCSE (nodeKey cseCompact)

namespace PropertyKindCalculus.Examples.TapeCseStructural

abbrev Key := Option String × List Nat × List UInt64
abbrev CseState := Tape Float × Array Nat × Std.HashMap Key Nat

/-! ## `cseCompact` as a left fold

`cseCompact` is an `Id.run` `for`-loop over the nodes with three `mut` cells `(newTape, remap, memo)`.
We name one iteration (`cseStep`) and reformulate the loop as `Array.foldl cseStep` so the invariant can
be established by `Array.foldl_induction`. -/

/-- One iteration of the `cseCompact` loop, as a pure state step (matching the source verbatim). -/
def cseStep (st : CseState) (node : Node Float) : CseState :=
  match st.2.2[nodeKey st.2.1 node]? with
  | some nid => (st.1, st.2.1.push nid, st.2.2)
  | none =>
      ((st.1.addNode { node with parents := node.parents.map (fun p => st.2.1.getD p p) }).1,
       st.2.1.push (st.1.addNode { node with parents := node.parents.map (fun p => st.2.1.getD p p) }).2,
       st.2.2.insert (nodeKey st.2.1 node)
         (st.1.addNode { node with parents := node.parents.map (fun p => st.2.1.getD p p) }).2)

/-- The initial loop state. -/
def cseInit (t : Tape Float) : CseState :=
  (Tape.empty, Array.mkEmpty t.size, (∅ : Std.HashMap Key Nat))

/-- `cseCompact`'s loop as a fold. -/
def cseFold (t : Tape Float) : CseState :=
  t.nodes.foldl cseStep (cseInit t)

/-- Generic: any `forIn` whose body is pointwise `pure (.yield (cseStep st node))` is a fold. The
pointwise hypothesis is discharged by `split`, sidestepping the fact that the source `match` and
`cseStep`'s `match` are distinct matcher constants. -/
theorem forIn_list_foldl (body : Node Float → CseState → Id (ForInStep CseState))
    (hbody : ∀ node st, body node st = pure (ForInStep.yield (cseStep st node)))
    (l : List (Node Float)) (st : CseState) :
    (forIn l st body : Id CseState) = pure (l.foldl (fun s n => cseStep s n) st) := by
  induction l generalizing st with
  | nil => simp
  | cons hd tl ih =>
      rw [List.forIn_cons, hbody]
      simp only [pure_bind]
      rw [ih (cseStep st hd)]
      rfl

/-- **`cseCompact` is the fold `cseStep` over its nodes.** -/
theorem cseCompact_eq_foldl (t : Tape Float) :
    cseCompact t = ((cseFold t).1, (cseFold t).2.1) := by
  unfold cseCompact cseFold cseInit
  simp only [Id.run, bind_pure_comp]
  rw [← Array.forIn_toList, forIn_list_foldl _ (by intro node st; unfold cseStep; split <;> simp_all)]
  simp only [Array.foldl_toList]
  rfl

/-! ## Small tape/array helpers -/

theorem getNode?_addNode_self (t : Tape Float) (n : Node Float) :
    (t.addNode n).1.getNode? t.size
      = some { n with value := Runtime.Autograd.AnyTensor.materialize n.value } := by
  simp [Tape.getNode?, Tape.addNode, Tape.size]

theorem getNode?_addNode_lt (t : Tape Float) (n : Node Float) (id : Nat) (h : id < t.size) :
    (t.addNode n).1.getNode? id = t.getNode? id := by
  have h' : id < t.nodes.size := h
  simp only [Tape.getNode?, Tape.addNode]
  rw [Array.getElem?_push_lt h']
  exact (Array.getElem?_eq_getElem h').symm

theorem getD_push_self {α} (xs : Array α) (x d : α) : (xs.push x).getD xs.size d = x := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]; simp

theorem getD_push_lt {α} (xs : Array α) (x d : α) (i : Nat) (h : i < xs.size) :
    (xs.push x).getD i d = xs.getD i d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt h, Array.getElem?_eq_getElem h]

theorem getD_push_at {α} (xs : Array α) (x d : α) (k : Nat) (hk : k = xs.size) :
    (xs.push x).getD k d = x := by subst hk; exact getD_push_self xs x d

/-- Mapping parents through `rm.push x` equals mapping through `rm`, when every parent is in bounds —
the fact that lets a later `remap` growth leave an already-recorded node's remapped parents fixed. -/
theorem map_getD_push {ps : List Nat} {rm : Array Nat} {x : Nat}
    (hps : ∀ p ∈ ps, p < rm.size) :
    ps.map (fun p => (rm.push x).getD p p) = ps.map (fun p => rm.getD p p) :=
  List.map_congr_left (fun p hp => getD_push_lt rm x p p (hps p hp))

theorem key_name (rm : Array Nat) (n : Node Float) : (nodeKey rm n).1 = n.name := rfl
theorem key_parents (rm : Array Nat) (n : Node Float) :
    (nodeKey rm n).2.1 = n.parents.map (fun p => rm.getD p p) := rfl
theorem key_bits (rm : Array Nat) (n : Node Float) :
    (nodeKey rm n).2.2 = (Spec.toList n.value.t).map Float.toBits := rfl

/-! ## Well-formedness and the loop invariant -/

/-- A recorded tape is **well-formed** when every node's parents are strictly earlier ids (the usual
tape build invariant: every op appends after its operands). Every tape a `[NumCarrier]` kernel records
is well-formed by construction. -/
def WF (t : Tape Float) : Prop :=
  ∀ id nd, t.getNode? id = some nd → ∀ p ∈ nd.parents, p < id

/-- **The loop invariant.** After `cseCompact` has processed `k` nodes with state `(newTape, remap,
memo)`:
* `remap` has `k` entries;
* `newTape` is well-formed;
* every processed original id `id < k` has `remap[id]` in range and the node stored there matching the
  original node's **op name**, **parents (remapped by the current `remap`)**, and **value bits**;
* every `memo` entry is backed by a stored node matching the key's name / parents / value-bits. -/
def Inv (t : Tape Float) (k : Nat) (st : CseState) : Prop :=
  st.2.1.size = k ∧
  (∀ id nd, st.1.getNode? id = some nd → ∀ p ∈ nd.parents, p < id) ∧
  (∀ id, id < k → st.2.1.getD id id < st.1.size ∧
     ∃ nNew nOld, st.1.getNode? (st.2.1.getD id id) = some nNew ∧ t.getNode? id = some nOld ∧
       nNew.name = nOld.name ∧
       nNew.parents = nOld.parents.map (fun p => st.2.1.getD p p) ∧
       (Spec.toList nNew.value.t).map Float.toBits = (Spec.toList nOld.value.t).map Float.toBits) ∧
  (∀ (key : Key) (nid : Nat), st.2.2[key]? = some nid → nid < st.1.size ∧
     ∃ nNew, st.1.getNode? nid = some nNew ∧
       nNew.name = key.1 ∧ nNew.parents = key.2.1 ∧
       (Spec.toList nNew.value.t).map Float.toBits = key.2.2)

theorem inv_base (t : Tape Float) : Inv t 0 (cseInit t) := by
  refine ⟨by simp [cseInit, Array.mkEmpty], ?_, ?_, ?_⟩
  · intro id nd h; simp [cseInit, Tape.getNode?, Tape.empty] at h
  · intro id h; exact absurd h (Nat.not_lt_zero id)
  · intro key nid h; simp [cseInit] at h

theorem inv_step (t : Tape Float) (hwf : WF t) (i : Fin t.nodes.size) (st : CseState)
    (H : Inv t i.1 st) : Inv t (i.1 + 1) (cseStep st t.nodes[i]) := by
  obtain ⟨hsz, hwfNew, hcorr, hmemo⟩ := H
  set node := t.nodes[i] with hnode
  have hOldNode : t.getNode? i.1 = some node := by
    simp only [Tape.getNode?]; exact Array.getElem?_eq_getElem i.2
  have hpar_lt : ∀ p ∈ node.parents, p < i.1 := hwf i.1 node hOldNode
  have hpar_ltsz : ∀ p ∈ node.parents, p < st.2.1.size := fun p hp => hsz ▸ hpar_lt p hp
  unfold cseStep
  split
  · -- merge case: memo hit (newTape unchanged, remap grows by the memoized id)
    rename_i nid hhit
    obtain ⟨hnidlt, nNew, hnNew, hnName, hnPar, hnbits⟩ := hmemo _ _ hhit
    refine ⟨by dsimp only; rw [Array.size_push, hsz], by dsimp only; exact hwfNew, ?_,
      by dsimp only; exact hmemo⟩
    intro id hid
    dsimp only
    rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hlt | heq
    · rw [getD_push_lt _ _ _ _ (hsz ▸ hlt)]
      obtain ⟨hlt', a, b, ha, hb, hname, hpar, hbits⟩ := hcorr id hlt
      have hb_par : ∀ p ∈ b.parents, p < st.2.1.size := by
        intro p hp; have := hwf id b hb p hp; omega
      exact ⟨hlt', a, b, ha, hb, hname, by rw [hpar, map_getD_push hb_par], hbits⟩
    · subst heq
      rw [getD_push_at _ _ _ _ hsz.symm]
      refine ⟨hnidlt, nNew, node, hnNew, hOldNode, ?_, ?_, ?_⟩
      · rw [hnName, key_name]
      · rw [hnPar, key_parents, map_getD_push hpar_ltsz]
      · rw [hnbits, key_bits]
  · -- fresh case: a new node is appended, remap and memo grow
    rename_i hmiss
    set node' : Node Float := { node with parents := node.parents.map (fun p => st.2.1.getD p p) }
      with hnode'
    have hself := getNode?_addNode_self st.1 node'
    have hnode'_par : node'.parents = node.parents.map (fun p => st.2.1.getD p p) := by rw [hnode']
    have hnode'_name : node'.name = node.name := by rw [hnode']
    have hnode'_val : node'.value = node.value := by rw [hnode']
    have hpar_valid : ∀ p ∈ node.parents, st.2.1.getD p p < st.1.size :=
      fun p hp => (hcorr p (hpar_lt p hp)).1
    refine ⟨by dsimp only; rw [Array.size_push, hsz], ?_, ?_, ?_⟩
    · -- newTape' is well-formed
      intro id nd hnd
      dsimp only at hnd
      rw [Tape.getNode?, Tape.addNode, Array.getElem?_push] at hnd
      split at hnd
      · rename_i hid_eq
        simp only [Option.some.injEq] at hnd
        subst hnd
        intro p hp
        rw [hnode'_par] at hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        rw [hid_eq]; exact hpar_valid q hq
      · have hidlt : id < st.1.size := by
          rcases Nat.lt_or_ge id st.1.nodes.size with h | h
          · exact h
          · rw [Array.getElem?_eq_none_iff.mpr h] at hnd; exact absurd hnd (by simp)
        exact hwfNew id nd (by rw [Tape.getNode?]; exact hnd)
    · -- correspondence
      intro id hid
      dsimp only
      rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hlt | heq
      · rw [getD_push_lt _ _ _ _ (hsz ▸ hlt)]
        obtain ⟨hlt', a, b, ha, hb, hname, hpar, hbits⟩ := hcorr id hlt
        have hb_par : ∀ p ∈ b.parents, p < st.2.1.size := by
          intro p hp; have := hwf id b hb p hp; omega
        refine ⟨by rw [Tape.size_addNode]; exact Nat.lt_succ_of_lt hlt', a, b,
          by rw [getNode?_addNode_lt _ _ _ hlt']; exact ha, hb, hname,
          by rw [hpar, map_getD_push hb_par], hbits⟩
      · subst heq
        rw [getD_push_at _ _ _ _ hsz.symm]
        refine ⟨by rw [Tape.size_addNode]; exact Nat.lt_succ_self _, _, node, hself, hOldNode,
          ?_, ?_, ?_⟩
        · simp only [hnode'_name]
        · simp only [hnode'_par]; rw [map_getD_push hpar_ltsz]
        · rw [hnode'_val, Runtime.Autograd.AnyTensor.materialize_eq]
    · -- memo soundness (insert)
      intro key nid hkey
      dsimp only at hkey ⊢
      rw [Std.HashMap.getElem?_insert] at hkey
      split at hkey
      · rename_i hbeq
        simp only [Option.some.injEq] at hkey
        subst hkey
        have hkeq : nodeKey st.2.1 node = key := eq_of_beq hbeq
        refine ⟨by rw [Tape.size_addNode]; exact Nat.lt_succ_self _, _, hself, ?_, ?_, ?_⟩
        · rw [← hkeq, key_name]
        · rw [← hkeq, key_parents]
        · rw [← hkeq, key_bits, hnode'_val, Runtime.Autograd.AnyTensor.materialize_eq]
      · obtain ⟨hnidlt, nNew, hnNew, hnName, hnPar, hnbits⟩ := hmemo _ _ hkey
        exact ⟨by rw [Tape.size_addNode]; exact Nat.lt_succ_of_lt hnidlt, nNew,
          by rw [getNode?_addNode_lt _ _ _ hnidlt]; exact hnNew, hnName, hnPar, hnbits⟩

/-- **The invariant holds after the whole pass.** -/
theorem cseFold_inv (t : Tape Float) (hwf : WF t) : Inv t t.nodes.size (cseFold t) :=
  Array.foldl_induction (Inv t) (inv_base t) (inv_step t hwf)

/-! ## Whole-pass corollaries -/

/-- **Structural correspondence — the whole-pass lift of `cseKey_denotation_sound`.** For a
well-formed tape, every original node `id` maps under `cseCompact`'s remap to an in-range node of the
compacted tape carrying the **same op name**, its **parents remapped by the same remap**, and a
**bit-identical stored value**. Because `evalTape`/`cOp` reads exactly (op-name, remapped-parents) for
an op node and the stored value for a const leaf, the compacted DAG computes node-for-node what the
original does — this is `cseKey_denotation_sound` promoted from one merge to the entire pass. -/
theorem cseCompact_structural (t : Tape Float) (hwf : WF t) (id : Nat) (h : id < t.size) :
    (cseCompact t).2.getD id id < (cseCompact t).1.size ∧
    ∃ nNew nOld, (cseCompact t).1.getNode? ((cseCompact t).2.getD id id) = some nNew ∧
      t.getNode? id = some nOld ∧ nNew.name = nOld.name ∧
      nNew.parents = nOld.parents.map (fun p => (cseCompact t).2.getD p p) ∧
      (Spec.toList nNew.value.t).map Float.toBits = (Spec.toList nOld.value.t).map Float.toBits := by
  obtain ⟨_, _, hcorr, _⟩ := cseFold_inv t hwf
  rw [cseCompact_eq_foldl]
  exact hcorr id h

/-- **The compacted tape is well-formed** (parents precede children), so it is itself a legal tape to
re-interpret with `evalTape`. -/
theorem cseCompact_wellFormed (t : Tape Float) (hwf : WF t) : WF (cseCompact t).1 := by
  obtain ⟨_, hwfNew, _, _⟩ := cseFold_inv t hwf
  rw [cseCompact_eq_foldl]
  exact hwfNew

/-- **Stored-value preservation, for an arbitrary well-formed tape** — the general form of the
machine-checked `cse_preserves_resJac`: every original node's stored forward value is bit-identical to
the value stored at its CSE-remapped node. The read-back never moves; only the node count shrinks. -/
theorem cseCompact_preserves_stored (t : Tape Float) (hwf : WF t) (id : Nat) (h : id < t.size) :
    ∃ nNew nOld, (cseCompact t).1.getNode? ((cseCompact t).2.getD id id) = some nNew ∧
      t.getNode? id = some nOld ∧
      (Spec.toList nNew.value.t).map Float.toBits = (Spec.toList nOld.value.t).map Float.toBits := by
  obtain ⟨_, nNew, nOld, ha, hb, _, _, hbits⟩ := cseCompact_structural t hwf id h
  exact ⟨nNew, nOld, ha, hb, hbits⟩

/-! ## Inhabitation — the theorems are non-vacuous

The corollaries are hypothetical (`WF t`, `id < t.size`); a witness confirms those hypotheses are
jointly satisfiable by a real tape *with an op node*, so nothing above is vacuously true. Every tape a
`[NumCarrier]` kernel records is well-formed by construction — here is a minimal concrete one. -/

/-- Well-formedness of a concrete tape reduces to a decidable bounded check. -/
theorem wf_of_bounded (t : Tape Float)
    (h : ∀ id, (hid : id < t.size) → ∀ p ∈ (t.nodes[id]'hid).parents, p < id) : WF t := by
  intro id nd hnd p hp
  rw [Tape.getNode?] at hnd
  obtain ⟨hid, heq⟩ := Array.getElem?_eq_some_iff.mp hnd
  exact h id hid p (by rw [heq]; exact hp)

/-- A concrete well-formed tape: two named input leaves and one `add` op reading both. -/
def demoTape : Tape Float :=
  let t0 := Tape.empty
  let t1 := (t0.leaf (fill (0.0 : Float) Shape.scalar) (name := some "a")).1
  let t2 := (t1.leaf (fill (0.0 : Float) Shape.scalar) (name := some "b")).1
  (t2.addNode { name := some "add",
                value := Runtime.Autograd.AnyTensor.mk (fill (0.0 : Float) Shape.scalar),
                parents := [0, 1], backward := fun _ => .ok [] }).1

theorem demoTape_size : demoTape.size = 3 := by decide
theorem demoTape_wf : WF demoTape := wf_of_bounded demoTape (by decide)

-- The corollaries apply non-vacuously to a real op node (id = 2) and a real leaf (id = 0):
example := cseCompact_structural demoTape demoTape_wf 2 (by rw [demoTape_size]; decide)
example := cseCompact_structural demoTape demoTape_wf 0 (by rw [demoTape_size]; decide)
example := cseCompact_preserves_stored demoTape demoTape_wf 2 (by rw [demoTape_size]; decide)
example : WF (cseCompact demoTape).1 := cseCompact_wellFormed demoTape demoTape_wf

/-- Executable confirmation that the structural claim is genuinely satisfied (not vacuously): on
`demoTape`, node 2's CSE-remapped node really carries op `"add"` with two parents. -/
def demoStructuralCheck : Bool :=
  let (t', rm) := cseCompact demoTape
  match t'.getNode? (rm.getD 2 2) with
  | some nd => nd.name == some "add" && nd.parents.length == 2
  | none => false

#guard demoStructuralCheck

/-! ## Axiom audit — these rest only on the standard axioms (no `sorryAx`). -/

/-- info: 'PropertyKindCalculus.Examples.TapeCseStructural.cseCompact_structural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cseCompact_structural

/-- info: 'PropertyKindCalculus.Examples.TapeCseStructural.cseCompact_preserves_stored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cseCompact_preserves_stored

/-- info: 'PropertyKindCalculus.Examples.TapeCseStructural.cseCompact_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cseCompact_wellFormed

end PropertyKindCalculus.Examples.TapeCseStructural
