/-
# A direct P↔R simulation for TorchLean reverse-mode AD

Relates TorchLean's **runtime tape** (R) to its **fderiv proof model** (P) by a simulation
relation. Typecheck standalone with:

    lake env lean uncertainty/PropertyKindCalculus/Uncertainty/Experiments/PRSimulation.lean

Two worlds:

* **P** (`TorchLean.Tape.Graph`, ℝ-only): a snoc-list of lawful typed nodes, with
  `GraphData.evalVec` and the reverse program `GraphData.backpropAllCtx`.
* **R** (`TorchLean.Tape (SomeTensor ℝ)`): shape-erased values, nodes with an *opaque*
  `backward` closure, and the total reverse pass `Tape.backwardDenseFrom{,Loop,Step}`.

Contents:

1. `ForwardSim` (§1): the tape stores, slot by slot, the values of `evalVec`. The lowered tape
   `GraphData.toTape` inhabits it (`forwardSim_toTape`).
2. `direct_PR_soundness_compiled` (§2): on the lowered tape the dense reverse pass succeeds and
   the `Γ`-prefix of its output realises `(fderiv ℝ evalVec x)† seed`. It is the prefix
   projection of `Tape.Graph.backwardDenseFrom_eq_fderiv`, in this file's `ArrCorr` phrasing.
3. `backwardDenseFrom_ok` (§3): `ForwardSim` pins the stored **values** only, so a tape with a
   closure `fun _ => .error …` refutes success from `ForwardSim` alone. The hypothesis that
   suffices is `BackwardShapeWF`: every closure is *shape-total*. Under it the invariant
   `AccShapeAligned` threads through the fold, value-free. Leaves provide `BackwardShapeWF`.

The closure provenance of tapes recorded with `Tape.apply` is supplied by
`Experiments/EagerProvenance.lean` (`EagerBuilds` / `direct_PR_soundness_eager`).
-/

module

public import TorchLean.NN.Tape.RealNode.Arm
public import TorchLean.NN.Tape.Lowering.FDeriv
public import TorchLean.NN.Tape.Apply.Correctness
public import PropertyKindCalculus.Torch.Paradigm.TapeM

@[expose] public noncomputable section Blanket

open TorchLean TorchLean.Tensor TorchLean.Tape PropertyKindCalculus.Paradigm

namespace PRSim

-- R-side abbreviations.
abbrev Any    := SomeTensor ℝ
abbrev RTape  := Tape (SomeTensor ℝ)
abbrev RNode  := Tape.Node (SomeTensor ℝ)
abbrev Res    := Result
/-- A P graph: lawful real nodes over the trivial environment. -/
abbrev PGraph (Γ ss : List Shape) := Tape.Graph (α := ℝ) Unit Γ ss
@[reducible] def mkAny {s : Shape} (t : Tensor ℝ s) : Any := SomeTensor.ofTensor t

/-! ## §1. The forward simulation relation -/

/-- The value P assigns to context slot `i`, shape-erased. -/
def ctxSlotValue {Γ ss : List Shape} (g : PGraph Γ ss) (xV : CtxVec Γ)
    (i : Fin (Γ ++ ss).length) : Any :=
  mkAny (Tensor.ofVec (s := (Γ ++ ss).get i)
    (CtxVec.getBlock (Γ := Γ ++ ss) i (g.toData.evalVec () xV)))

/-- The tape stores, slot by slot, the values of `evalVec`. -/
def ForwardSim {Γ ss : List Shape} (g : PGraph Γ ss) (xV : CtxVec Γ) (t : RTape) : Prop :=
  t.nodes.size = (Γ ++ ss).length ∧
  ∀ i : Fin (Γ ++ ss).length, t.getValue? i.val = some (ctxSlotValue g xV i)

/-- Entry `i` of an erased pack is the typed entry, shape-erased. -/
theorem toAnyArray_getElem? {ss : List Shape} (xs : TensorPack ℝ ss) (i : Fin ss.length) :
    (TensorPack.erase xs)[i.val]? = some (mkAny (Pack.get xs i)) := by
  have hlt : i.val < (TensorPack.erase xs).size := by simp
  rw [Array.getElem?_eq_getElem hlt]
  exact congrArg some (TensorPack.get_erase xs i)

/-- The lowered tape forward-simulates its graph. -/
theorem forwardSim_toTape {Γ ss : List Shape} (g : PGraph Γ ss) (x : TensorPack ℝ Γ) :
    ForwardSim g (TensorPack.toVec x) (GraphData.toTape g.toData x ()).1 := by
  have hsize := GraphData.toTape_nodes_size g.toData x ()
  have hvals := GraphData.toTape_values_eq g.toData x ()
  have hctx := GraphData.toTape_ctx_eq_eval g.toData x ()
  refine ⟨by simp [hsize], ?_⟩
  intro i
  have hread : (GraphData.toTape g.toData x ()).1.getValue? i.val
      = (TensorPack.erase (g.toData.eval x ()))[i.val]? := by
    have hmap : ((GraphData.toTape g.toData x ()).1.nodes.map (fun node => node.value))[i.val]?
        = (TensorPack.erase (g.toData.eval x ()))[i.val]? := by rw [hvals, hctx]
    simpa [Tape.getValue?, Tape.getNode?, Array.getElem?_map] using hmap
  rw [hread, toAnyArray_getElem?]
  unfold ctxSlotValue
  rw [GraphData.evalVec_flattenCtx, CtxVec.getBlock_toVec, Tensor.ofVec_toVec]

/-! ## §2. The fderiv endpoint on the lowered tape -/

/-- `arr` is the shape-erased reading of the cotangent context `v`. -/
def ArrCorr {Γ' : List Shape} (v : CtxVec Γ') (arr : Array Any) : Prop :=
  arr.size = Γ'.length ∧
  ∀ i : Fin Γ'.length,
    arr[i.val]? = some (mkAny (Tensor.ofVec (s := Γ'.get i) (CtxVec.getBlock (Γ := Γ') i v)))

/-- The `Γ`-prefix of an erased pack is the erased `Γ`-part. -/
theorem toAnyArray_extract_takeLeft {Γ ss : List Shape} (w : TensorPack ℝ (Γ ++ ss)) :
    (TensorPack.erase w).extract 0 Γ.length = TensorPack.erase (Pack.split (ss₁ := Γ) w).1 := by
  have hlist : ∀ (Γ' : List Shape) (w' : TensorPack ℝ (Γ' ++ ss)),
      (TensorPack.erase (Pack.split (ss₁ := Γ') w').1).toList
        = (TensorPack.erase w').toList.take Γ'.length := by
    intro Γ'
    induction Γ' with
    | nil => intro w'; simp [Pack.split, TensorPack.erase]
    | cons s Γ' ih =>
      intro w'
      cases w' with
      | cons x xs => simp [Pack.split, TensorPack.erase, List.take_succ_cons, ih xs]
  apply Array.ext'
  simp [hlist Γ w]

/-- An erased pack realises its own vectorization. -/
theorem arrCorr_toVec {Γ : List Shape} (u : TensorPack ℝ Γ) :
    ArrCorr (TensorPack.toVec u) (TensorPack.erase u) := by
  refine ⟨by simp, ?_⟩
  intro i
  rw [toAnyArray_getElem?, CtxVec.getBlock_toVec, Tensor.ofVec_toVec]

/-- Pointwise endpoint: on the lowered tape the dense reverse pass succeeds and its `Γ`-prefix
    realises `(fderiv ℝ evalVec x)† seed`. -/
theorem direct_PR_soundness_compiled_at {Γ ss : List Shape}
    (g : PGraph Γ ss) (x : TensorPack ℝ Γ)
    (hg : RealGraph.FDerivCorrectAt (Γ := Γ) g.toData () (TensorPack.toVec x))
    (seed : TensorPack ℝ (Γ ++ ss)) :
    ∃ out : Array Any,
      Tape.backwardDenseFrom (t := (GraphData.toTape g.toData x ()).1)
          (grads0 := TensorPack.erase seed) = .ok out ∧
      ArrCorr ((fderiv ℝ (g.toData.evalVec ()) (TensorPack.toVec x)).adjoint
          (TensorPack.toVec seed)) (out.extract 0 Γ.length) := by
  obtain ⟨h1, h2⟩ := Tape.Graph.backwardDenseFrom_eq_fderiv g x () seed hg
  refine ⟨_, h1, ?_⟩
  rw [toAnyArray_extract_takeLeft, ← h2]
  exact arrCorr_toVec _

/-- The endpoint for an everywhere-differentiable graph. -/
theorem direct_PR_soundness_compiled {Γ ss : List Shape}
    (g : PGraph Γ ss) (hg : RealGraph.FDerivCorrect (Γ := Γ) g.toData ())
    (x : TensorPack ℝ Γ) (seed : TensorPack ℝ (Γ ++ ss)) :
    ∃ out : Array Any,
      Tape.backwardDenseFrom (t := (GraphData.toTape g.toData x ()).1)
          (grads0 := TensorPack.erase seed) = .ok out ∧
      ArrCorr ((fderiv ℝ (g.toData.evalVec ()) (TensorPack.toVec x)).adjoint
          (TensorPack.toVec seed)) (out.extract 0 Γ.length) :=
  direct_PR_soundness_compiled_at g x (hg.at _) seed
/-- Every accumulator slot carries its node's shape (and the sizes agree). -/
def AccShapeAligned (t : RTape) (acc : Array Any) : Prop :=
  acc.size = t.nodes.size ∧
  ∀ (i : Nat) (node : RNode) (g : Any),
    t.getNode? i = some node → acc[i]? = some g → g.shape = node.value.shape

/-- Backward closures are *shape-total*: fed a cotangent of the node's own shape (which is what
    `backwardDenseFromStep` always passes), the closure succeeds, and every contribution targets
    an existing node at that node's shape. -/
def BackwardShapeWF (t : RTape) : Prop :=
  ∀ (i : Nat) (node : RNode), t.getNode? i = some node →
    ∀ d : Tensor ℝ node.value.shape,
      ∃ contribs, node.backward ⟨node.value.shape, d⟩ = .ok contribs ∧
        ∀ pc ∈ contribs, ∃ pnode : RNode,
          t.getNode? pc.1 = some pnode ∧ pc.2.shape = pnode.value.shape

/-- A `getNode?` hit bounds the id by the tape size. -/
theorem lt_of_getNode?_eq_some {t : RTape} {i : Nat} {node : RNode}
    (h : t.getNode? i = some node) : i < t.nodes.size := by
  by_contra hge
  have hnone : t.getNode? i = none := by
    simp [Tape.getNode?, Array.getElem?_eq_none (Nat.le_of_not_lt hge)]
  simp [hnone] at h

/-- `SomeTensor.add` succeeds on equal shapes, and the sum keeps the left shape. -/
theorem anyAdd_ok_of_shape_eq (a b : Any) (h : a.shape = b.shape) :
    ∃ c : Any, SomeTensor.add a b = .ok c ∧ c.shape = a.shape := by
  refine ⟨⟨a.shape, a.tensor + b.cast h.symm⟩, ?_, rfl⟩
  simp [SomeTensor.add, h, SomeTensor.cast]

/-- One `addGradAll` accumulation preserves the shape-alignment invariant and succeeds,
    provided the contribution targets an existing node at that node's shape. -/
theorem addGradAll_ok (t : RTape) (acc : Array Any) (hacc : AccShapeAligned t acc)
    (pid : Nat) (g : Any) (pnode : RNode)
    (hp : t.getNode? pid = some pnode) (hs : g.shape = pnode.value.shape) :
    ∃ acc', Tape.addGradAll (t := t) acc pid g = .ok acc' ∧
      AccShapeAligned t acc' := by
  obtain ⟨hsize, hslots⟩ := hacc
  by_cases hreq : pnode.requiresGrad = false
  · refine ⟨acc, ?_, hsize, hslots⟩
    simp [Tape.addGradAll, hp, hreq, bind, Except.bind, pure, Except.pure]
  · have hreq' : pnode.requiresGrad = true := by
      cases hb : pnode.requiresGrad
      · exact absurd hb hreq
      · rfl
    have hpid_lt : pid < t.nodes.size := lt_of_getNode?_eq_some hp
    have hpid_acc : pid < acc.size := by rw [hsize]; exact hpid_lt
    have hex : (acc[pid]'hpid_acc).shape = pnode.value.shape :=
      hslots pid pnode _ hp (Array.getElem?_eq_getElem hpid_acc)
    obtain ⟨summed, hsummed, hsummed_s⟩ :=
      anyAdd_ok_of_shape_eq
        ⟨pnode.value.shape, (acc[pid]'hpid_acc).cast hex⟩
        ⟨pnode.value.shape, g.cast hs⟩ rfl
    refine ⟨acc.set pid summed hpid_acc, ?_, ?_, ?_⟩
    · -- `addGradAll` matches on `acc[pid]?` with a dependent equation, so after the
      -- surrounding plumbing is simplified away the lookup is split by cases rather than
      -- rewritten under the match.
      simp [Tape.addGradAll, hp, hreq', hs, SomeTensor.cast, bind,
        Except.bind, pure, Except.pure]
      split
      · next hnone =>
        rw [Array.getElem?_eq_getElem hpid_acc] at hnone
        cases hnone
      · next existing hsome =>
        have hx : existing = acc[pid]'hpid_acc := by
          rw [Array.getElem?_eq_getElem hpid_acc] at hsome
          exact (Option.some.inj hsome).symm
        subst hx
        simp only [SomeTensor.cast] at hsummed; simp [hex, hsummed]
    · simpa using hsize
    · intro i node gi hnode hgi
      by_cases hi : pid = i
      · subst hi
        rw [hp] at hnode
        have hnodeeq : pnode = node := Option.some.inj hnode
        subst hnodeeq
        rw [Array.getElem?_set_self hpid_acc] at hgi
        have hgieq : summed = gi := Option.some.inj hgi
        subst hgieq
        exact hsummed_s
      · rw [Array.getElem?_set_ne hpid_acc hi] at hgi
        exact hslots i node gi hnode hgi

/-- Folding a list of well-targeted contributions through `addGradAll` succeeds and preserves
    the invariant.  (The fold function is written exactly as in `backwardDenseFromStep`.) -/
theorem foldContribs_ok (t : RTape) :
    ∀ (contribs : List (Nat × Any)) (acc : Array Any), AccShapeAligned t acc →
      (∀ pc ∈ contribs, ∃ pnode : RNode,
          t.getNode? pc.1 = some pnode ∧ pc.2.shape = pnode.value.shape) →
      ∃ acc',
        contribs.foldlM
            (fun acc2 (pid, pg) => Tape.addGradAll (t := t) acc2 pid pg) acc
          = .ok acc' ∧ AccShapeAligned t acc'
  | [], acc, hacc, _ => ⟨acc, rfl, hacc⟩
  | (pid, pg) :: rest, acc, hacc, htargets => by
      obtain ⟨pnode, hp, hs⟩ := htargets (pid, pg) List.mem_cons_self
      obtain ⟨acc1, hstep, hacc1⟩ := addGradAll_ok t acc hacc pid pg pnode hp hs
      obtain ⟨acc', hrest, hacc'⟩ :=
        foldContribs_ok t rest acc1 hacc1 (fun q hq => htargets q (List.mem_cons_of_mem _ hq))
      exact ⟨acc', by simp [List.foldlM_cons, hstep, hrest, bind, Except.bind], hacc'⟩

/-- The `Array` form of `foldContribs_ok`.  `backwardDenseFromStep` folds an `Array` of
    contributions; `Array.foldlM_toList` identifies that with the list fold above. -/
theorem foldContribsArray_ok (t : RTape) (contribs : Array (Nat × Any)) (acc : Array Any)
    (hacc : AccShapeAligned t acc)
    (htargets : ∀ pc ∈ contribs, ∃ pnode : RNode,
        t.getNode? pc.1 = some pnode ∧ pc.2.shape = pnode.value.shape) :
    ∃ acc',
      contribs.foldlM
          (fun acc2 (pid, pg) => Tape.addGradAll (t := t) acc2 pid pg) acc
        = .ok acc' ∧ AccShapeAligned t acc' := by
  obtain ⟨acc', hfold, hacc'⟩ :=
    foldContribs_ok t contribs.toList acc hacc (fun q hq => htargets q (by simpa using hq))
  exact ⟨acc', by rwa [Array.foldlM_toList] at hfold, hacc'⟩

/-- One reverse step succeeds and preserves the invariant.-/
theorem backwardDenseFromStep_ok (t : RTape) (hwf : BackwardShapeWF t)
    (acc : Array Any) (hacc : AccShapeAligned t acc) (id : Nat) (hid : id < t.nodes.size) :
    ∃ acc', Tape.backwardDenseFromStep (t := t) acc id = .ok acc' ∧
      AccShapeAligned t acc' := by
  obtain ⟨hsize, hslots⟩ := hacc
  have hnode : t.getNode? id = some (t.nodes[id]'hid) := by
    simp [Tape.getNode?, Array.getElem?_eq_getElem hid]
  set node := t.nodes[id]'hid with hnode_def
  by_cases hreq : node.requiresGrad = false
  · refine ⟨acc, ?_, hsize, hslots⟩
    simp [Tape.backwardDenseFromStep, hnode, hreq,
      bind, Except.bind, pure, Except.pure]
  · have hreq' : node.requiresGrad = true := by
      cases hb : node.requiresGrad
      · exact absurd hb hreq
      · rfl
    have hid_acc : id < acc.size := by rw [hsize]; exact hid
    have hg : acc[id]? = some (acc[id]'hid_acc) := Array.getElem?_eq_getElem hid_acc
    set g := acc[id]'hid_acc with hg_def
    have hshape : g.shape = node.value.shape := hslots id node g hnode hg
    obtain ⟨contribs, hbackward, htargets⟩ :=
      hwf id node hnode (g.cast hshape)
    obtain ⟨acc', hfold, hacc'⟩ :=
      foldContribsArray_ok t contribs acc ⟨hsize, hslots⟩ htargets
    refine ⟨acc', ?_, hacc'⟩
    simp only [SomeTensor.cast] at hbackward
    have hfold' : Array.foldlM (fun x y => Tape.addGradAll t x y.1 y.2) acc contribs = .ok acc' := hfold
    simp [Tape.backwardDenseFromStep, hnode, hreq', hg, hshape,
      SomeTensor.cast, hbackward, hfold', bind, Except.bind, pure, Except.pure]

/-- The reverse loop over the first `n` ids succeeds and preserves the invariant. -/
theorem backwardDenseFromLoop_ok (t : RTape) (hwf : BackwardShapeWF t) :
    ∀ (n : Nat), n ≤ t.nodes.size → ∀ acc, AccShapeAligned t acc →
      ∃ out, Tape.backwardDenseFromLoop (t := t) n acc = .ok out ∧
        AccShapeAligned t out
  | 0, _, acc, hacc => ⟨acc, rfl, hacc⟩
  | n + 1, hn, acc, hacc => by
      obtain ⟨acc', hstep, hacc'⟩ :=
        backwardDenseFromStep_ok t hwf acc hacc n (Nat.lt_of_succ_le hn)
      obtain ⟨out, hloop, hout⟩ :=
        backwardDenseFromLoop_ok t hwf n (Nat.le_of_succ_le hn) acc' hacc'
      exact ⟨out, by
        simp [Tape.backwardDenseFromLoop, hstep, hloop,
          bind, Except.bind], hout⟩

/-! ## §3. Partiality: R returns `.ok` under `BackwardShapeWF`

`ForwardSim` pins the stored values, but the reverse pass runs the opaque `backward` closures, so
success needs `BackwardShapeWF`. R never inspects values, so `.ok` is independent of
differentiability. -/

/-- `ForwardSim` + a seed realising some cotangent context give the fold invariant. -/
theorem accShapeAligned_of_sim {Γ ss : List Shape} {g : PGraph Γ ss} {xV : CtxVec Γ}
    {t : RTape} (hsim : ForwardSim g xV t)
    {seedFull : CtxVec (Γ ++ ss)} {seedArr : Array Any}
    (hseed : ArrCorr seedFull seedArr) :
    AccShapeAligned t seedArr := by
  obtain ⟨hts, hvals⟩ := hsim
  obtain ⟨hss, hslots⟩ := hseed
  refine ⟨by rw [hss, hts], ?_⟩
  intro i node gi hnode hgi
  have hi : i < (Γ ++ ss).length := by
    have h := lt_of_getNode?_eq_some hnode
    rwa [hts] at h
  -- The node's stored value is the slot value, so its shape is the slot shape.
  have hval : t.getValue? i = some (ctxSlotValue g xV ⟨i, hi⟩) := hvals ⟨i, hi⟩
  have hvalue : node.value = ctxSlotValue g xV ⟨i, hi⟩ := by
    simp only [Tape.getValue?, hnode, Option.map_some] at hval
    exact Option.some.inj hval
  have hnode_s : node.value.shape = (Γ ++ ss).get ⟨i, hi⟩ := by
    rw [hvalue]; rfl
  -- The seed slot's shape is also the slot shape.
  have hslot : seedArr[i]? = some (mkAny (Tensor.ofVec (s := (Γ ++ ss).get ⟨i, hi⟩)
      (CtxVec.getBlock (Γ := Γ ++ ss) ⟨i, hi⟩ seedFull))) := hslots ⟨i, hi⟩
  rw [hgi] at hslot
  have hgieq : gi = mkAny (Tensor.ofVec (s := (Γ ++ ss).get ⟨i, hi⟩)
      (CtxVec.getBlock (Γ := Γ ++ ss) ⟨i, hi⟩ seedFull)) := Option.some.inj hslot
  rw [hgieq, hnode_s]
  rfl

/-- **The total reverse pass returns `.ok`** on a `ForwardSim`-well-formed tape with shape-total
    closures, from any seed realising a cotangent context.  (Original obligation, CLOSED with
    the `BackwardShapeWF` refinement; the invariant on the output comes for free.) -/
theorem backwardDenseFrom_ok
    {Γ ss : List Shape} (g : PGraph Γ ss) (xV : CtxVec Γ)
    (t : RTape) (hsim : ForwardSim g xV t) (hwf : BackwardShapeWF t)
    (seedFull : CtxVec (Γ ++ ss)) (seedArr : Array Any) (hseed : ArrCorr seedFull seedArr) :
    ∃ out : Array Any, Tape.backwardDenseFrom (t := t) seedArr = .ok out ∧
      AccShapeAligned t out := by
  have hacc := accShapeAligned_of_sim hsim hseed
  obtain ⟨out, hloop, hout⟩ :=
    backwardDenseFromLoop_ok t hwf t.nodes.size (Nat.le_refl _) seedArr hacc
  refine ⟨out, ?_, hout⟩
  simp [Tape.backwardDenseFrom, hacc.1, hloop]

/- The eager constructors provide `BackwardShapeWF`, node by node. -/

/-- The empty tape is (vacuously) shape-total. -/
theorem backwardShapeWF_empty : BackwardShapeWF ((Tape.empty : RTape)) := by
  intro i node hnode
  simp [Tape.empty, Tape.getNode?] at hnode

/-- Pushing a node whose closure is shape-total w.r.t. the *old* tape preserves
    `BackwardShapeWF` (old closures never see the new id; targets persist under push). -/
theorem backwardShapeWF_addNode (t : RTape) (hwf : BackwardShapeWF t) (node : RNode)
    (hnode : ∀ d : Tensor ℝ node.value.shape,
      ∃ contribs, node.backward ⟨node.value.shape, d⟩ = .ok contribs ∧
        ∀ pc ∈ contribs, ∃ pnode : RNode,
          t.getNode? pc.1 = some pnode ∧ pc.2.shape = pnode.value.shape) :
    BackwardShapeWF (t.addNode node).1 := by
  -- `addNode` materializes the stored value, which is the identity on `SomeTensor`.
  have hpush : (t.addNode node).1.nodes = t.nodes.push node := by
    simp [Tape.addNode]
  have hmono : ∀ (j : Nat) (pnode : RNode), t.getNode? j = some pnode →
      (t.addNode node).1.getNode? j = some pnode := by
    intro j pnode hj
    have hjlt : j < t.nodes.size := lt_of_getNode?_eq_some hj
    have hj' : t.nodes[j]? = some pnode := hj
    have hval : t.nodes[j]'hjlt = pnode :=
      Option.some.inj ((Array.getElem?_eq_getElem hjlt).symm.trans hj')
    simp only [Tape.getNode?, hpush]
    rw [Array.getElem?_push_lt hjlt, hval]
  intro i inode hi d
  by_cases hilt : i < t.nodes.size
  · -- an old node: its closure and its targets are untouched
    have hi_old : t.getNode? i = some inode := by
      have h := hi
      simp only [Tape.getNode?, hpush] at h
      rw [Array.getElem?_push_lt hilt] at h
      have hval : t.nodes[i]'hilt = inode := Option.some.inj h
      show t.nodes[i]? = some inode
      rw [Array.getElem?_eq_getElem hilt, hval]
    obtain ⟨contribs, hok, htargets⟩ := hwf i inode hi_old d
    exact ⟨contribs, hok, fun pc hpc =>
      let ⟨pnode, hp, hs⟩ := htargets pc hpc
      ⟨pnode, hmono pc.1 pnode hp, hs⟩⟩
  · -- the new node: `hnode` gives the closure fact against `t`, transported by `hmono`
    have hi_eq : i = t.nodes.size := by
      have hi_lt : i < (t.addNode node).1.nodes.size := lt_of_getNode?_eq_some hi
      rw [hpush, Array.size_push] at hi_lt
      omega
    subst hi_eq
    have hi_new : inode = node := by
      have h := hi
      simp only [Tape.getNode?, hpush] at h
      rw [Array.getElem?_push_size] at h
      exact (Option.some.inj h).symm
    subst hi_new
    obtain ⟨contribs, hok, htargets⟩ := hnode d
    exact ⟨contribs, hok, fun pc hpc =>
      let ⟨pnode, hp, hs⟩ := htargets pc hpc
      ⟨pnode, hmono pc.1 pnode hp, hs⟩⟩

/-- Leaves are shape-total (their closure returns no contributions). -/
theorem backwardShapeWF_leaf {s : Shape} (t : RTape) (hwf : BackwardShapeWF t)
    (v : Tensor ℝ s) (name : Option String) (rg : Bool) :
    BackwardShapeWF (CpuTape.leaf t v name rg).1 := by
  exact backwardShapeWF_addNode t hwf _ (fun d => ⟨#[], rfl, by simp⟩)

end PRSim
