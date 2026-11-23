/-
# Eager-tape provenance: the fderiv endpoint for tapes recorded with `Tape.apply`

`PRSimulation.lean` proves the fderiv endpoint for the *lowered* tape `GraphData.toTape`. This
module proves it for the tape a program actually records, one `Tape.apply` at a time.

* `TapeInv t ctx bp` is what the reverse-pass induction carries: the tape has one live node per
  context entry, stores `ctx`, sends contributions only to earlier nodes, and its dense reverse
  pass computes `bp`.
* `TapeInv.apply` is the step for one recorded operator with a single value output and no alias
  rule in effect. `TapeInv.unary` and `TapeInv.binary` instantiate it for `CpuTape.unary` and
  `CpuTape.binary`, with the VJP of the operator's `LawfulNode.ofArm` node.
* `EagerBuilds g x t` relates the recorded tape `t` to the graph `g` of `ofArm` nodes.
* `direct_PR_soundness_eager`: on such a tape the dense reverse pass succeeds and the `Γ`-prefix
  of its output realises `(fderiv ℝ evalVec x)† seed`. `forwardSim_eager` is the forward half.

Each recorded operator carries two hypotheses about its rule: no alias applies at its parents
(`min x x` and `max x x` record one parent, which is a different node), and the rule emits its
contributions in port order.
-/

module

public import PropertyKindCalculus.Uncertainty.Experiments.PRSimulation

@[expose] public noncomputable section Blanket

open TorchLean TorchLean.Tensor TorchLean.Tape PropertyKindCalculus.Paradigm

namespace PRSim

/-- Context addition is associative (through vectorization). -/
theorem tensorPack_add_assoc {Γ' : List Shape} (a b c : TensorPack ℝ Γ') :
    TensorPack.add (TensorPack.add a b) c = TensorPack.add a (TensorPack.add b c) := by
  have h : TensorPack.toVec (TensorPack.add (TensorPack.add a b) c)
      = TensorPack.toVec (TensorPack.add a (TensorPack.add b c)) := by
    simp only [TensorPack.toVec_add, add_assoc]
  simpa using congrArg (TensorPack.ofVec (Γ := Γ')) h

/-- The reverse step at a freshly appended node whose contributions fold to a context addition. -/
theorem backwardDenseFromStep_addNode {ss : List Shape} {τ : Shape}
    (t : RTape) (nd : RNode) (seedPrev contrib : TensorPack ℝ ss) (seedOut : Tensor ℝ τ)
    (hsize : t.nodes.size = ss.length)
    (hreqNd : nd.requiresGrad = true) (hshape : nd.value.shape = τ)
    {cs : Array (Nat × Any)}
    (hback : nd.backward (mkAny seedOut) = .ok cs)
    (hlt : ∀ {pid : Nat} {pg : Any}, (pid, pg) ∈ cs → pid < t.nodes.size)
    (hfold : cs.foldlM (fun acc2 (pid, pg) => Tape.addGradAll (t := t) acc2 pid pg)
        (TensorPack.erase seedPrev) = .ok (TensorPack.erase (TensorPack.add seedPrev contrib))) :
    Tape.backwardDenseFromStep (t := (t.addNode nd).1)
        ((TensorPack.erase seedPrev).push (mkAny seedOut)) t.nodes.size =
      .ok ((TensorPack.erase (TensorPack.add seedPrev contrib)).push (mkAny seedOut)) := by
  have hsizeArr : (TensorPack.erase seedPrev).size = t.nodes.size := by
    rw [TensorPack.size_erase, hsize]
  have hnodeLast : Tape.getNode? (t := (t.addNode nd).1) t.nodes.size = some nd := by
    simp [Tape.getNode?, Tape.addNode]
  have haccLast : ((TensorPack.erase seedPrev).push (mkAny seedOut))[t.nodes.size]?
      = some (mkAny seedOut) := by
    rw [← hsizeArr, Array.getElem?_push, ite_eq_left rfl]
  have hshapeNode : (mkAny seedOut).shape = nd.value.shape := hshape.symm
  have hfoldLast :
      cs.foldlM (fun acc2 (pid, pg) => Tape.addGradAll (t := (t.addNode nd).1) acc2 pid pg)
        ((TensorPack.erase seedPrev).push (mkAny seedOut)) =
      .ok ((TensorPack.erase (TensorPack.add seedPrev contrib)).push (mkAny seedOut)) := by
    rw [← Array.foldlM_toList] at hfold ⊢
    rw [foldlM_addGradAll_addNode_push t nd (mkAny seedOut) cs.toList _ hsizeArr
      (fun h => hlt (by simpa using h)), hfold]
    rfl
  subst hshape
  simp only [GradValue.shape_someTensor, GradValue.retag_someTensor, GradValue.check_someTensor,
      Tape.backwardDenseFromStep, hnodeLast, haccLast, hreqNd, Result.pure_eq_ok, Result.bind_ok,
      Bool.true_eq_false, ite_false]
  rw [dite_eq_left hshapeNode, SomeTensor.ofTensor_cast, hback, Result.bind_ok]
  exact hfoldLast

/-- **Inductive step of the eager link**, for any appended node whose contributions fold to the
    context addition of `vjp`. -/
theorem backwardDenseFrom_addNode {ss : List Shape} {τ : Shape}
    (t : RTape) (nd : RNode) (vjp : Tensor ℝ τ → TensorPack ℝ ss)
    (bp : TensorPack ℝ ss → TensorPack ℝ ss)
    (hsize : t.nodes.size = ss.length)
    (hreqNd : nd.requiresGrad = true) (hshape : nd.value.shape = τ)
    (hpids : BackwardPidsLt t)
    (hbp : ∀ s : TensorPack ℝ ss,
      Tape.backwardDenseFrom (t := t) (TensorPack.erase s) = .ok (TensorPack.erase (bp s)))
    (hnd : ∀ (seedPrev : TensorPack ℝ ss) (seedOut : Tensor ℝ τ), ∃ cs,
      nd.backward (mkAny seedOut) = .ok cs ∧
      (∀ {pid : Nat} {pg : Any}, (pid, pg) ∈ cs → pid < t.nodes.size) ∧
      cs.foldlM (fun acc2 (pid, pg) => Tape.addGradAll (t := t) acc2 pid pg)
        (TensorPack.erase seedPrev) =
          .ok (TensorPack.erase (TensorPack.add seedPrev (vjp seedOut))))
    (seedPrev : TensorPack ℝ ss) (seedOut : Tensor ℝ τ) :
    Tape.backwardDenseFrom (t := (t.addNode nd).1)
        (TensorPack.erase (Pack.snoc seedPrev seedOut)) =
      .ok (TensorPack.erase (Pack.snoc (bp (TensorPack.add seedPrev (vjp seedOut))) seedOut)) := by
  obtain ⟨cs, hback, hlt, hfold⟩ := hnd seedPrev seedOut
  have hstepLast := backwardDenseFromStep_addNode t nd seedPrev (vjp seedOut) seedOut hsize
    hreqNd hshape hback hlt hfold
  generalize hsp : TensorPack.add seedPrev (vjp seedOut) = seedPrev' at hstepLast ⊢
  have htNextSize : (t.addNode nd).1.nodes.size = t.nodes.size + 1 := by simp [Tape.addNode]
  have hsizeCheck : (TensorPack.erase (Pack.snoc seedPrev seedOut)).size
      = (t.addNode nd).1.nodes.size := by
    simp [htNextSize, hsize, TensorPack.size_erase]
  have hsizePrev' : (TensorPack.erase seedPrev').size = t.nodes.size := by
    simp [hsize, TensorPack.size_erase]
  have hloopPrev : Tape.backwardDenseFromLoop (t := t) t.nodes.size (TensorPack.erase seedPrev')
      = .ok (TensorPack.erase (bp seedPrev')) := by
    have h := hbp seedPrev'
    unfold Tape.backwardDenseFrom at h
    rwa [ite_eq_left hsizePrev'] at h
  have hloopFinal : Tape.backwardDenseFromLoop (t := (t.addNode nd).1) t.nodes.size
        ((TensorPack.erase seedPrev').push (mkAny seedOut)) =
      .ok ((TensorPack.erase (bp seedPrev')).push (mkAny seedOut)) := by
    rw [backwardDenseFromLoop_addNode_push t nd (mkAny seedOut) hpids t.nodes.size le_rfl _
      hsizePrev', hloopPrev]
    rfl
  unfold Tape.backwardDenseFrom
  rw [ite_eq_left hsizeCheck, htNextSize, TensorPack.erase_snoc,
    Tape.backwardDenseFromLoop, hstepLast, Result.bind_ok, hloopFinal, TensorPack.erase_snoc]

/-- The shape-erased *list* view of a typed context. -/
def toAnyList : {Γ' : List Shape} → TensorPack ℝ Γ' → List Any
  | [], .nil => []
  | _ :: _, .cons x xs => mkAny x :: toAnyList xs

/-- The list view is the `toList` of the array view. -/
@[simp] theorem toList_erase :
    ∀ {Γ' : List Shape} (w : TensorPack ℝ Γ'), (TensorPack.erase w).toList = toAnyList w
  | [], .nil => rfl
  | _ :: Γ', .cons x xs => by
      simp [TensorPack.erase, toAnyList, mkAny, toList_erase xs]

/-- Adding the zero context changes nothing. -/
theorem tensorPack_add_zero :
    ∀ {Γ' : List Shape} (w : TensorPack ℝ Γ'), TensorPack.add w TensorPack.zero = w
  | [], .nil => rfl
  | s :: Γ', .cons x xs => by
      show Pack.cons (x + Tensor.full s (0 : ℝ)) (TensorPack.add xs TensorPack.zero) = _
      rw [tensorPack_add_zero xs]
      simp

/-- List-level: adding a one-hot context is a `List.set` at its slot. -/
theorem toAnyList_add_single :
    ∀ {Γ' : List Shape} {s : Shape} (w : TensorPack ℝ Γ') (c : Idx Γ' s) (u : Tensor ℝ s),
      toAnyList (TensorPack.add w (TensorPack.single c u))
        = (toAnyList w).set c.i.val
            (mkAny (Pack.get w c.i + Tensor.castShape u c.h.symm))
  | s0 :: Γ', s, .cons x xs, ⟨⟨0, h0⟩, h⟩, u => by
      show toAnyList (Pack.cons (x + (Tensor.castShape u h.symm : Tensor ℝ s0))
              (TensorPack.add xs TensorPack.zero))
          = (mkAny x :: toAnyList xs).set 0 (mkAny (x + (Tensor.castShape u h.symm : Tensor ℝ s0)))
      rw [tensorPack_add_zero]
      rfl
  | s0 :: Γ', s, .cons x xs, ⟨⟨Nat.succ j, hj⟩, h⟩, u => by
      show toAnyList (Pack.cons (x + Tensor.full s0 (0 : ℝ))
              (TensorPack.add xs
                (TensorPack.single ⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, by simpa using h⟩ u)))
          = (mkAny x :: toAnyList xs).set (j + 1) _
      have hx : x + Tensor.full s0 (0 : ℝ) = x := by simp
      rw [hx]
      show mkAny x :: toAnyList _ = mkAny x :: (toAnyList xs).set j _
      rw [toAnyList_add_single xs ⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, by simpa using h⟩ u]
      rfl

/-- **The sparse accumulate**: one `addGradAll` at slot `c` of an erased context performs the
    one-hot context addition, when the node at `c` is live and carries the slot's shape. -/
theorem addGradAll_erase_single {Γ' : List Shape} {s : Shape} (t : RTape)
    (c : Idx Γ' s) (u : Tensor ℝ s) (node : RNode)
    (hn : t.getNode? c.i.val = some node) (hrg : node.requiresGrad = true)
    (hs : node.value.shape = Γ'.get c.i) (w : TensorPack ℝ Γ') :
    Tape.addGradAll (t := t) (TensorPack.erase w) c.i.val (mkAny u)
      = .ok (TensorPack.erase (TensorPack.add w (TensorPack.single c u))) := by
  obtain ⟨i, h⟩ := c
  subst h
  obtain ⟨nm, ⟨vs, vt⟩, own, rg, ps, cl, bk⟩ := node
  have hs' : vs = Γ'.get i := hs
  subst hs'
  have hrg' : rg = true := hrg
  subst hrg'
  have hlt : i.val < (TensorPack.erase w).size := by simp
  have harr : (TensorPack.erase w)[i.val]? = some (mkAny (Pack.get w i)) :=
    toAnyArray_getElem? w i
  have hres : TensorPack.erase (TensorPack.add w (TensorPack.single ⟨i, rfl⟩ u))
      = (TensorPack.erase w).set i.val (mkAny (Pack.get w i + u)) hlt := by
    apply Array.ext'
    simp [toAnyList_add_single]
  rw [hres]
  simp only [Tape.addGradAll, hn, bind, Except.bind, pure, Except.pure, Bool.true_eq_false,
    ↓reduceIte, GradValue.shape_someTensor, GradValue.retag_someTensor,
    GradValue.check_someTensor, GradValue.add_someTensor, mkAny, SomeTensor.ofTensor, ↓reduceDIte]
  split
  · next hnone => rw [harr] at hnone; cases hnone
  · next existing hsome =>
    rw [harr] at hsome
    cases hsome
    simp [mkAny, SomeTensor.add, SomeTensor.cast, SomeTensor.ofTensor]


/-- What the reverse-pass induction carries about a tape recording the context `ctx`. -/
structure TapeInv {ss : List Shape} (t : RTape) (ctx : TensorPack ℝ ss)
    (bp : TensorPack ℝ ss → TensorPack ℝ ss) : Prop where
  size : t.nodes.size = ss.length
  req : ∀ i (hi : i < t.nodes.size), (t.nodes[i]'hi).requiresGrad = true
  vals : t.nodes.map (fun n => n.value) = TensorPack.erase ctx
  pids : BackwardPidsLt t
  bp_eq : ∀ s : TensorPack ℝ ss,
    Tape.backwardDenseFrom (t := t) (TensorPack.erase s) = .ok (TensorPack.erase (bp s))

/-- Appending a live node whose contributions fold to the context addition of `vjp` keeps the
    invariant, with the `snoc` reverse program. -/
theorem TapeInv.addNode {ss : List Shape} {τ : Shape} {t : RTape} {ctx : TensorPack ℝ ss}
    {bp : TensorPack ℝ ss → TensorPack ℝ ss} (h : TapeInv t ctx bp)
    (nd : RNode) (y : Tensor ℝ τ) (vjp : Tensor ℝ τ → TensorPack ℝ ss)
    (hreqNd : nd.requiresGrad = true) (hval : nd.value = mkAny y)
    (hlt : ∀ (d : Any) (cs : Array (Nat × Any)), nd.backward d = .ok cs →
      ∀ {pid : Nat} {pg : Any}, (pid, pg) ∈ cs → pid < t.nodes.size)
    (hnd : ∀ (seedPrev : TensorPack ℝ ss) (seedOut : Tensor ℝ τ), ∃ cs,
      nd.backward (mkAny seedOut) = .ok cs ∧
      cs.foldlM (fun acc2 (pid, pg) => Tape.addGradAll (t := t) acc2 pid pg)
        (TensorPack.erase seedPrev) =
          .ok (TensorPack.erase (TensorPack.add seedPrev (vjp seedOut)))) :
    TapeInv (t.addNode nd).1 (Pack.snoc ctx y)
      (fun seed => Pack.snoc
        (bp (TensorPack.add (Pack.unsnoc seed).1 (vjp (Pack.unsnoc seed).2)))
        (Pack.unsnoc seed).2) := by
  have hnodes : (t.addNode nd).1.nodes = t.nodes.push nd := by simp [Tape.addNode]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hnodes, h.size]
  · intro i hi
    simp only [hnodes, Array.getElem_push]
    split
    · exact h.req i _
    · exact hreqNd
  · simp [hnodes, h.vals, hval, TensorPack.erase_snoc, mkAny]
  · intro id n hn d cs hback pid pg hmem
    by_cases hid : id < t.nodes.size
    · have hn' : t.getNode? id = some n := by
        simpa [Tape.getNode?, hnodes, Array.getElem?_push, Nat.ne_of_lt hid] using hn
      exact h.pids id n hn' d cs hback hmem
    · have hsz : id < t.nodes.size + 1 := by
        have := lt_of_getNode?_eq_some hn
        simpa [hnodes] using this
      have hidEq : id = t.nodes.size := by omega
      subst hidEq
      have hn' : n = nd := by
        simpa [Tape.getNode?, hnodes] using hn.symm
      subst hn'
      exact hlt d cs hback hmem
  · intro s
    have hs : s = Pack.snoc (Pack.unsnoc s).1 (Pack.unsnoc s).2 := (Pack.snoc_unsnoc s).symm
    conv_lhs => rw [hs]
    exact backwardDenseFrom_addNode t nd vjp bp h.size hreqNd (by rw [hval]; rfl) h.pids h.bp_eq
      (fun sp so => by
        obtain ⟨cs, hb, hf⟩ := hnd sp so
        exact ⟨cs, hb, fun hm => hlt _ cs hb hm, hf⟩) _ _


/-- The leaves of `x` satisfy the invariant with the identity reverse program. -/
theorem tapeInv_leaves {Γ : List Shape} (x : TensorPack ℝ Γ) :
    TapeInv (Tape.addLeaves (t := (Tape.empty : RTape)) x) x id := by
  have h1 := Tape.GraphData.toTape_nodes_size (Δ := Unit) (.nil : GraphData ℝ Unit Γ []) x ()
  have h2 := Tape.GraphData.requiresGrad_toTape (Δ := Unit) (.nil : GraphData ℝ Unit Γ []) x ()
  have h4 := Tape.GraphData.backwardPidsLt_toTape (Δ := Unit) (.nil : GraphData ℝ Unit Γ []) x ()
  refine ⟨by simpa [GraphData.toTape] using h1, h2, ?_, h4, ?_⟩
  · simp [Tape.addLeaves_values, Tape.empty]
  · intro s
    exact Tape.backwardDenseFrom_addLeaves_empty x s


/-- **One recorded operator.** A successful `Tape.apply` of a one-output operator without an
    alias keeps the invariant, once its emitted contributions fold to the addition of `vjp`. -/
theorem TapeInv.apply {ss : List Shape} {τ : Shape} {ins : List Port} {t t' : RTape}
    {ctx : TensorPack ℝ ss} {bp : TensorPack ℝ ss → TensorPack ℝ ss} (h : TapeInv t ctx bp)
    {name : String} {op : Op ins [.value τ]} {args : Tape.Args ℝ ins}
    {o : Tape.Outs ℝ [.value τ]} {rule : Op.Rule ℝ ins [.value τ]} {xs : Values ℝ ins}
    (hop : Tape.apply t name op args = .ok (t', o))
    (hspec : op.rule? (α := ℝ) = some rule) (hxs : Tape.Args.read t ins args = .ok xs)
    (halias : Tape.aliasOf rule (Tape.Args.ids ins args) = none)
    (hflag : ((List.finRange ins.length).any fun i =>
      Flags.get ins (Tape.Args.flags t ins args) i) = true)
    (vjp : Tensor ℝ τ → TensorPack ℝ ss)
    (hfold : ∀ (seedPrev : TensorPack ℝ ss) (seedOut : Tensor ℝ τ),
      (Tape.emit rule (Tape.Args.ids ins args)
          (Tangents.select ins (Tape.Args.flags t ins args)
            (rule.backward xs (seedOut, ())))).foldlM
        (fun acc2 (pid, pg) => Tape.addGradAll (t := t) acc2 pid pg)
        (TensorPack.erase seedPrev) =
          .ok (TensorPack.erase (TensorPack.add seedPrev (vjp seedOut)))) :
    TapeInv t' (Pack.snoc ctx (rule.forward xs).1)
      (fun seed => Pack.snoc
        (bp (TensorPack.add (Pack.unsnoc seed).1 (vjp (Pack.unsnoc seed).2)))
        (Pack.unsnoc seed).2) := by
  have hy : Tape.Values.value? [.value τ] (rule.forward xs)
      = some (mkAny (rule.forward xs).1) := rfl
  obtain ⟨-, -, ht⟩ := Tape.record_eq_ok (Tape.apply_eq_record hop hspec hxs)
  rw [Tape.prepared_value, hy, Tape.prepared_of_aliasOf_eq_none halias] at ht
  subst ht
  refine h.addNode _ _ vjp hflag rfl ?_ ?_
  · intro d cs hback pid pg hmem
    simp only [Tape.recordedNode, bind, Except.bind] at hback
    cases hs : Tape.seed d [Port.value τ] with
    | error e => rw [hs] at hback; cases hback
    | ok gs =>
      rw [hs] at hback
      cases hback
      obtain ⟨n, hn⟩ := Tape.exists_getNode?_of_read_eq_ok ins args xs hxs _ (pid, pg)
        (Tape.mem_contributions_of_mem_emit (Array.mem_toList_iff.mpr hmem))
      exact lt_of_getNode?_eq_some hn
  · intro sp so
    refine ⟨_, ?_, hfold sp so⟩
    simp [Tape.recordedNode, Tape.seed, Tape.requireGrad, mkAny, SomeTensor.ofTensor,
      SomeTensor.cast, bind, Except.bind, pure, Except.pure]
    exact congrArg _ (rule.prepare_eq _ _ _)


/-- Under the invariant, slot `idx` of the tape stores the context entry. -/
theorem TapeInv.getNode? {ss : List Shape} {t : RTape} {ctx : TensorPack ℝ ss}
    {bp : TensorPack ℝ ss → TensorPack ℝ ss} (h : TapeInv t ctx bp) (i : Fin ss.length) :
    ∃ node : RNode, t.getNode? i.val = some node ∧ node.requiresGrad = true ∧
      node.value = mkAny (Pack.get ctx i) := by
  have hi : i.val < t.nodes.size := by rw [h.size]; exact i.isLt
  refine ⟨t.nodes[i.val], by simp [Tape.getNode?, hi], h.req _ hi, ?_⟩
  have hv := congrArg (fun a => a[i.val]?) h.vals
  simp only [Array.getElem?_map, toAnyArray_getElem?] at hv
  simpa [hi] using hv

/-- Under the invariant, a value port reads the context entry. -/
theorem TapeInv.requireValue {ss : List Shape} {s : Shape} {t : RTape} {ctx : TensorPack ℝ ss}
    {bp : TensorPack ℝ ss → TensorPack ℝ ss} (h : TapeInv t ctx bp) (idx : Idx ss s) :
    Tape.requireValue (s := s) t idx.i.val = .ok (TensorPack.getIdx ctx idx) := by
  obtain ⟨node, hn, -, hv⟩ := h.getNode? idx.i
  obtain ⟨i, hi⟩ := idx
  subst hi
  simp [Tape.requireValue, Tape.getValue?, hn, hv, mkAny, SomeTensor.ofTensor, SomeTensor.cast,
    TensorPack.getIdx]

/-- Under the invariant, every parent needs a gradient. -/
theorem TapeInv.flag {ss : List Shape} {t : RTape} {ctx : TensorPack ℝ ss}
    {bp : TensorPack ℝ ss → TensorPack ℝ ss} (h : TapeInv t ctx bp) (i : Fin ss.length) :
    (t.getNode? i.val).any (·.requiresGrad) = true := by
  obtain ⟨node, hn, hr, -⟩ := h.getNode? i
  simp [hn, hr]

/-- Under the invariant, one accumulate at `idx` is the one-hot context addition. -/
theorem TapeInv.addGradAll {ss : List Shape} {s : Shape} {t : RTape} {ctx : TensorPack ℝ ss}
    {bp : TensorPack ℝ ss → TensorPack ℝ ss} (h : TapeInv t ctx bp) (idx : Idx ss s)
    (u : Tensor ℝ s) (w : TensorPack ℝ ss) :
    Tape.addGradAll (t := t) (TensorPack.erase w) idx.i.val (mkAny u)
      = .ok (TensorPack.erase (TensorPack.add w (TensorPack.single idx u))) := by
  obtain ⟨node, hn, hr, hv⟩ := h.getNode? idx.i
  exact addGradAll_erase_single t idx u node hn hr (by rw [hv]; rfl) w

/-- **A recorded unary operator** keeps the invariant with the `ofArm` node's VJP. -/
theorem TapeInv.unary {ss : List Shape} {σ τ : Shape} {t t' : RTape}
    {ctx : TensorPack ℝ ss} {bp : TensorPack ℝ ss → TensorPack ℝ ss} (h : TapeInv t ctx bp)
    {name : String} {op : Op [.value σ] [.value τ]} {id : Nat}
    (hr : (op.rule? (α := ℝ)).isSome = true) (idx : Idx ss σ)
    (hop : CpuTape.unary t name op idx.i.val = .ok (t', id))
    (halias : Tape.aliasOf ((op.rule? (α := ℝ)).get hr) [some idx.i.val] = none)
    (horder : ((op.rule? (α := ℝ)).get hr).order = List.finRange 1) :
    TapeInv t'
      (Pack.snoc ctx ((((op.rule? (α := ℝ)).get hr).forward (TensorPack.getIdx ctx idx, ())).1))
      (fun seed => Pack.snoc
        (bp (TensorPack.add (Pack.unsnoc seed).1
          (ArmArgs.scatter (Γ := ss) (ins := [.value σ]) (idx, ())
            (((op.rule? (α := ℝ)).get hr).backward (TensorPack.getIdx ctx idx, ())
              ((Pack.unsnoc seed).2, ())))))
        (Pack.unsnoc seed).2) := by
  have hspec : op.rule? (α := ℝ) = some ((op.rule? (α := ℝ)).get hr) := by simp
  have hxs : Tape.Args.read t [.value σ] (idx.i.val, ()) = .ok (TensorPack.getIdx ctx idx, ()) := by
    simp [Tape.Args.read, Tape.Arg.read, h.requireValue idx, bind, Except.bind, pure, Except.pure]
  simp only [CpuTape.unary, bind, Except.bind] at hop
  cases hap : Tape.apply t name op (idx.i.val, ()) with
  | error e => rw [hap] at hop; cases hop
  | ok r =>
    obtain ⟨t'', o⟩ := r
    rw [hap] at hop
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    refine h.apply hap hspec hxs halias ?_
      (fun δ => ArmArgs.scatter (Γ := ss) (ins := [.value σ]) (idx, ())
        (((op.rule? (α := ℝ)).get hr).backward (TensorPack.getIdx ctx idx, ()) (δ, ()))) ?_
    · simp [Tape.Args.flags, Flags.get, h.flag idx.i, List.finRange]
    · intro sp so
      have hemit : ∀ gs : Tangents ℝ [.value σ], Tape.emit ((op.rule? (α := ℝ)).get hr) (Tape.Args.ids (α := ℝ) [.value σ] (idx.i.val, ()))
          (Tangents.select (α := ℝ) [.value σ] (Tape.Args.flags t [.value σ] (idx.i.val, ())) gs)
          = #[(idx.i.val, mkAny gs.1)] := by
        rintro ⟨g, ⟨⟩⟩
        simp [Tape.emit, horder, Tape.Args.ids, Tape.Arg.id?, Tape.Args.flags, h.flag idx.i,
          Tangents.select, Port.select, Tape.Grads.contributions, Tape.Grad.contribution?,
          List.finRange, mkAny]
      rw [hemit]
      simp only [List.foldlM_toArray, List.foldlM_cons, List.foldlM_nil, h.addGradAll,
        Result.bind_ok]
      show _ = Except.ok (TensorPack.erase (TensorPack.add sp
        (TensorPack.add (TensorPack.single idx _) TensorPack.zero)))
      rw [tensorPack_add_zero]
      rfl


/-- **A recorded binary operator** keeps the invariant with the `ofArm` node's VJP. -/
theorem TapeInv.binary {ss : List Shape} {σ₁ σ₂ τ : Shape} {t t' : RTape}
    {ctx : TensorPack ℝ ss} {bp : TensorPack ℝ ss → TensorPack ℝ ss} (h : TapeInv t ctx bp)
    {name : String} {op : Op [.value σ₁, .value σ₂] [.value τ]} {id : Nat}
    (hr : (op.rule? (α := ℝ)).isSome = true) (a : Idx ss σ₁) (b : Idx ss σ₂)
    (hop : CpuTape.binary t name op a.i.val b.i.val = .ok (t', id))
    (halias : Tape.aliasOf ((op.rule? (α := ℝ)).get hr) [some a.i.val, some b.i.val] = none)
    (horder : ((op.rule? (α := ℝ)).get hr).order = List.finRange 2) :
    TapeInv t'
      (Pack.snoc ctx ((((op.rule? (α := ℝ)).get hr).forward
        (TensorPack.getIdx ctx a, TensorPack.getIdx ctx b, ())).1))
      (fun seed => Pack.snoc
        (bp (TensorPack.add (Pack.unsnoc seed).1
          (ArmArgs.scatter (Γ := ss) (ins := [.value σ₁, .value σ₂]) (a, b, ())
            (((op.rule? (α := ℝ)).get hr).backward
              (TensorPack.getIdx ctx a, TensorPack.getIdx ctx b, ())
              ((Pack.unsnoc seed).2, ())))))
        (Pack.unsnoc seed).2) := by
  have hspec : op.rule? (α := ℝ) = some ((op.rule? (α := ℝ)).get hr) := by simp
  have hxs : Tape.Args.read t [.value σ₁, .value σ₂] (a.i.val, b.i.val, ())
      = .ok (TensorPack.getIdx ctx a, TensorPack.getIdx ctx b, ()) := by
    simp [Tape.Args.read, Tape.Arg.read, h.requireValue a, h.requireValue b, bind, Except.bind,
      pure, Except.pure]
  simp only [CpuTape.binary, bind, Except.bind] at hop
  cases hap : Tape.apply t name op (a.i.val, b.i.val, ()) with
  | error e => rw [hap] at hop; cases hop
  | ok r =>
    obtain ⟨t'', o⟩ := r
    rw [hap] at hop
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    refine h.apply hap hspec hxs halias ?_
      (fun δ => ArmArgs.scatter (Γ := ss) (ins := [.value σ₁, .value σ₂]) (a, b, ())
        (((op.rule? (α := ℝ)).get hr).backward
          (TensorPack.getIdx ctx a, TensorPack.getIdx ctx b, ()) (δ, ()))) ?_
    · simp [Tape.Args.flags, Flags.get, h.flag a.i, List.finRange]
    · intro sp so
      have hemit : ∀ gs : Tangents ℝ [.value σ₁, .value σ₂],
          Tape.emit ((op.rule? (α := ℝ)).get hr)
            (Tape.Args.ids (α := ℝ) [.value σ₁, .value σ₂] (a.i.val, b.i.val, ()))
            (Tangents.select (α := ℝ) [.value σ₁, .value σ₂]
              (Tape.Args.flags t [.value σ₁, .value σ₂] (a.i.val, b.i.val, ())) gs)
          = #[(a.i.val, mkAny gs.1), (b.i.val, mkAny gs.2.1)] := by
        rintro ⟨ga, gb, ⟨⟩⟩
        simp [Tape.emit, horder, Tape.Args.ids, Tape.Arg.id?, Tape.Args.flags, h.flag a.i,
          h.flag b.i, Tangents.select, Port.select, Tape.Grads.contributions,
          Tape.Grad.contribution?, List.finRange, mkAny]
      rw [hemit]
      simp only [List.foldlM_toArray, List.foldlM_cons, List.foldlM_nil, h.addGradAll,
        Result.bind_ok]
      show _ = Except.ok (TensorPack.erase (TensorPack.add sp
        (TensorPack.add (TensorPack.single a _)
          (TensorPack.add (TensorPack.single b _) TensorPack.zero))))
      rw [tensorPack_add_zero, ← tensorPack_add_assoc]
      rfl

/-- A rule without an alias rule never records an aliased node. -/
theorem aliasOf_eq_none {ins outs : List Port} {rule : Op.Rule ℝ ins outs}
    (h : rule.alias? = none) (ids : List (Option Nat)) : Tape.aliasOf rule ids = none := by
  simp [Tape.aliasOf, h]

/-- **Provenance**: `t` was recorded with `Tape.apply`, one node per graph node, from the leaves
    of `x`. Each recorded operator has no alias at its parents and emits in port order. -/
inductive EagerBuilds {Γ : List Shape} :
    {ss : List Shape} → PGraph Γ ss → TensorPack ℝ Γ → RTape → Prop
  | nil (x : TensorPack ℝ Γ) :
      EagerBuilds .nil x (Tape.addLeaves (t := (Tape.empty : RTape)) x)
  | unary {ss : List Shape} {σ τ : Shape} {g : PGraph Γ ss} {x : TensorPack ℝ Γ}
      {t t' : RTape} {id : Nat} {name : String} {op : Op [.value σ] [.value τ]}
      (hr : (op.rule? (α := ℝ)).isSome = true) (idx : Idx (Γ ++ ss) σ)
      {jvp : Values ℝ [.value σ] → Tangents ℝ [.value σ] → Tensor ℝ τ}
      (adj : ∀ xs dxs (δ : Tensor ℝ τ), Tensor.Rep.dot (jvp xs dxs) δ =
        Arm.tangentsDot [.value σ] dxs (((op.rule? (α := ℝ)).get hr).backward xs (δ, ())))
      (hg : EagerBuilds g x t)
      (hop : CpuTape.unary t name op idx.i.val = .ok (t', id))
      (halias : Tape.aliasOf ((op.rule? (α := ℝ)).get hr) [some idx.i.val] = none)
      (horder : ((op.rule? (α := ℝ)).get hr).order = List.finRange 1) :
      EagerBuilds (.snoc g (Tape.LawfulNode.ofArm op hr (idx, ()) adj)) x t'
  | binary {ss : List Shape} {σ₁ σ₂ τ : Shape} {g : PGraph Γ ss} {x : TensorPack ℝ Γ}
      {t t' : RTape} {id : Nat} {name : String} {op : Op [.value σ₁, .value σ₂] [.value τ]}
      (hr : (op.rule? (α := ℝ)).isSome = true) (a : Idx (Γ ++ ss) σ₁) (b : Idx (Γ ++ ss) σ₂)
      {jvp : Values ℝ [.value σ₁, .value σ₂] → Tangents ℝ [.value σ₁, .value σ₂] → Tensor ℝ τ}
      (adj : ∀ xs dxs (δ : Tensor ℝ τ), Tensor.Rep.dot (jvp xs dxs) δ =
        Arm.tangentsDot [.value σ₁, .value σ₂] dxs
          (((op.rule? (α := ℝ)).get hr).backward xs (δ, ())))
      (hg : EagerBuilds g x t)
      (hop : CpuTape.binary t name op a.i.val b.i.val = .ok (t', id))
      (halias : Tape.aliasOf ((op.rule? (α := ℝ)).get hr) [some a.i.val, some b.i.val] = none)
      (horder : ((op.rule? (α := ℝ)).get hr).order = List.finRange 2) :
      EagerBuilds (.snoc g (Tape.LawfulNode.ofArm op hr (a, b, ()) adj)) x t'

/-- The invariant transported along an equation of shape lists. -/
theorem TapeInv.cast {ss ss' : List Shape} (e : ss = ss') {t : RTape} {ctx : TensorPack ℝ ss}
    {bp : TensorPack ℝ ss → TensorPack ℝ ss} (h : TapeInv t ctx bp) :
    TapeInv t (Pack.cast e ctx) (fun s => Pack.cast e (bp (Pack.cast e.symm s))) := by
  subst e
  simpa using h

/-- An eagerly recorded tape satisfies the invariant of its graph. -/
theorem EagerBuilds.inv {Γ : List Shape} : ∀ {ss : List Shape} {g : PGraph Γ ss}
    {x : TensorPack ℝ Γ} {t : RTape}, EagerBuilds g x t →
    TapeInv t (g.toData.eval x ()) (g.toData.backpropAllCtx x ()) := by
  intro ss g x t hb
  induction hb with
  | nil x =>
    have h := (tapeInv_leaves x).cast (List.append_nil Γ).symm
    simpa [GraphData.eval, GraphData.backpropAllCtx] using h
  | unary hr idx adj hg hop halias horder ih =>
    exact (ih.unary hr idx hop halias horder).cast (List.append_assoc _ _ _)
  | binary hr a b adj hg hop halias horder ih =>
    exact (ih.binary hr a b hop halias horder).cast (List.append_assoc _ _ _)

/-- On an eagerly recorded tape the dense reverse pass is the graph's reverse program. -/
theorem backwardDenseFrom_eager {Γ ss : List Shape} {g : PGraph Γ ss} {x : TensorPack ℝ Γ}
    {t : RTape} (hb : EagerBuilds g x t) (seed : TensorPack ℝ (Γ ++ ss)) :
    Tape.backwardDenseFrom (t := t) (TensorPack.erase seed) =
      .ok (TensorPack.erase (g.toData.backpropAllCtx x () seed)) :=
  hb.inv.bp_eq seed

/-- An eagerly recorded tape forward-simulates its graph. -/
theorem forwardSim_eager {Γ ss : List Shape} {g : PGraph Γ ss} {x : TensorPack ℝ Γ}
    {t : RTape} (hb : EagerBuilds g x t) : ForwardSim g (TensorPack.toVec x) t := by
  refine ⟨hb.inv.size, ?_⟩
  intro i
  obtain ⟨node, hn, -, hv⟩ := hb.inv.getNode? i
  simp only [Tape.getValue?, hn, Option.map_some, hv, ctxSlotValue]
  rw [GraphData.evalVec_flattenCtx, CtxVec.getBlock_toVec, Tensor.ofVec_toVec]

/-- **Pointwise eager endpoint**: on an eagerly recorded tape the dense reverse pass succeeds and
    its `Γ`-prefix realises `(fderiv ℝ evalVec x)† seed`. -/
theorem direct_PR_soundness_eager_at {Γ ss : List Shape}
    (g : PGraph Γ ss) (x : TensorPack ℝ Γ)
    (hg : RealGraph.FDerivCorrectAt (Γ := Γ) g.toData () (TensorPack.toVec x))
    {t : RTape} (hb : EagerBuilds g x t) (seed : TensorPack ℝ (Γ ++ ss)) :
    ∃ out : Array Any,
      Tape.backwardDenseFrom (t := t) (grads0 := TensorPack.erase seed) = .ok out ∧
      ArrCorr ((fderiv ℝ (g.toData.evalVec ()) (TensorPack.toVec x)).adjoint
          (TensorPack.toVec seed))
        (out.extract 0 Γ.length) := by
  obtain ⟨-, h2⟩ := Tape.Graph.backwardDenseFrom_eq_fderiv g x () seed hg
  refine ⟨_, backwardDenseFrom_eager hb seed, ?_⟩
  rw [toAnyArray_extract_takeLeft, ← h2]
  exact arrCorr_toVec _

/-- **The eager endpoint** for an everywhere-differentiable graph. -/
theorem direct_PR_soundness_eager {Γ ss : List Shape}
    (g : PGraph Γ ss) (hg : RealGraph.FDerivCorrect (Γ := Γ) g.toData ())
    (x : TensorPack ℝ Γ) {t : RTape} (hb : EagerBuilds g x t)
    (seed : TensorPack ℝ (Γ ++ ss)) :
    ∃ out : Array Any,
      Tape.backwardDenseFrom (t := t) (grads0 := TensorPack.erase seed) = .ok out ∧
      ArrCorr ((fderiv ℝ (g.toData.evalVec ()) (TensorPack.toVec x)).adjoint
          (TensorPack.toVec seed))
        (out.extract 0 Γ.length) :=
  direct_PR_soundness_eager_at g x (hg.at _) hb seed

end PRSim
