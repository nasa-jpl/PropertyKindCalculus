/-
# Worked example — the `TapeM` bridge: `do`-block programs are eager-provenance-covered

`Runtime.Autograd.TapeM` (`StateT (Tape α) Result`) is the tape-builder monad TorchLean users
write eager programs in: each `TapeM.<op>` implicitly threads the tape around the pure
`Tape.<op>`. The eager-provenance closure (`Experiments/EagerProvenance.lean`) covers tapes
built by *explicit* `Tape.<op>` chains; this file closes the remaining gap to the monadic
style:

  * **The uniform reshuffle, reduced once** — every `TapeM` op wrapper is definitionally
    `opM g` (get; run `g`; set; return the id) for its pure op `g`. `opM_run_ok` /
    `opM_run_inv` reduce a successful run in one step, and the per-op corollaries
    (`run_mul_ok`, `run_scale_ok`, `run_div_ok`, …) are `opM_run_ok` at the op's `g` —
    definitional instantiations, no unfolding lemmas.
  * **Bind peeling** — `run_bind_inv` inverts a successful `run` of `m >>= f` into its two
    successful stages, so a `do`-block's `exec` hypothesis decomposes into per-op `.ok` facts.
  * **The demo** — `progMulScale`, the user-style program
    `do let a ← leaf x₀; let b ← leaf x₁; let m ← mul a b; scale m c`: a successful `exec`
    from the empty tape yields `EagerBuilds` for the 2-node P-graph `scale (mul x₀ x₁) c` by
    composing the constructors — so `direct_PR_soundness_eager` covers the tape the monadic
    program actually built, with no compilation and no hand-threading.

Axiom pins confirm the classical trio only.
-/
import PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim
import NN.Runtime.Autograd.Engine.TapeM

namespace PropertyKindCalculus.UncertaintyExamples.TapeMBridge

open Spec Tensor Proofs.Autograd
open PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim
open Runtime.Autograd (Tape TapeM Result)

noncomputable section

/-! ## The uniform builder pattern, reduced once -/

/-- The reshuffle every `TapeM` op wrapper is made of: get the tape, run the pure op, set the
    new tape, return the fresh node id. `TapeM.mul aId bId`, `TapeM.scale xId c`, … are each
    definitionally `opM g` at their pure op `g`. -/
def opM (g : Tape ℝ → Result (Tape ℝ × Nat)) : TapeM ℝ Nat := do
  let t ← get
  let (t', id) ← liftM (g t)
  set t'
  pure id

/-- A successful pure op gives the successful monadic run (the pair swaps: `run` returns
    value-then-state). -/
theorem opM_run_ok {g : Tape ℝ → Result (Tape ℝ × Nat)} {t t' : Tape ℝ} {id : Nat}
    (h : g t = .ok (t', id)) :
    (opM g).run t = .ok (id, t') := by
  simp only [opM, TapeM.run, StateT.run, bind, StateT.bind, StateT.lift, liftM, monadLift,
    MonadLift.monadLift, MonadState.get, MonadStateOf.get, getThe, StateT.get,
    set, MonadStateOf.set, StateT.set, pure, StateT.pure, Except.bind, Except.pure, h]

/-- A failing pure op gives the failing monadic run. -/
theorem opM_run_error {g : Tape ℝ → Result (Tape ℝ × Nat)} {t : Tape ℝ} {e : String}
    (h : g t = .error e) :
    (opM g).run t = .error e := by
  simp only [opM, TapeM.run, StateT.run, bind, StateT.bind, StateT.lift, liftM, monadLift,
    MonadLift.monadLift, MonadState.get, MonadStateOf.get, getThe, StateT.get,
    pure, Except.bind, Except.pure, h]

/-- Inversion: a successful monadic run means the pure op succeeded (with the pair swapped). -/
theorem opM_run_inv {g : Tape ℝ → Result (Tape ℝ × Nat)} {t t' : Tape ℝ} {id : Nat}
    (h : (opM g).run t = .ok (id, t')) :
    g t = .ok (t', id) := by
  cases hg : g t with
  | ok p =>
      obtain ⟨t1, i1⟩ := p
      have hrun := opM_run_ok (g := g) (t := t) (t' := t1) (id := i1) hg
      rw [hrun] at h
      injection h with h'
      have h1 : i1 = id := congrArg Prod.fst h'
      have h2 : t1 = t' := congrArg Prod.snd h'
      subst h1
      subst h2
      rfl
  | error e =>
      rw [opM_run_error (g := g) hg] at h
      cases h

/-! ## Bind peeling -/

/-- A successful run of `m >>= f` decomposes into its two successful stages. -/
theorem run_bind_inv {β γ : Type} {m : TapeM ℝ β} {f : β → TapeM ℝ γ}
    {t : Tape ℝ} {r : γ × Tape ℝ}
    (h : (m >>= f).run t = .ok r) :
    ∃ b t1, m.run t = .ok (b, t1) ∧ (f b).run t1 = .ok r := by
  have hb : (m >>= f).run t = (m.run t).bind fun bt => (f bt.1).run bt.2 := rfl
  rw [hb] at h
  cases hm : m.run t with
  | error e => rw [hm] at h; cases h
  | ok bt =>
      obtain ⟨b1, bt2⟩ := bt
      rw [hm] at h
      exact ⟨b1, bt2, rfl, h⟩

/-- `exec` inversion: a successful `exec` is a successful `run` with some returned value. -/
theorem exec_inv {β : Type} {m : TapeM ℝ β} {t t' : Tape ℝ}
    (h : TapeM.exec t m = .ok t') :
    ∃ b, m.run t = .ok (b, t') := by
  cases hm : StateT.run m t with
  | error e =>
      simp only [TapeM.exec, TapeM.run, bind, Except.bind, hm] at h
      cases h
  | ok bt =>
      obtain ⟨b1, b2⟩ := bt
      simp only [TapeM.exec, TapeM.run, bind, Except.bind, pure, Except.pure, hm] at h
      injection h with h'
      exact ⟨b1, by show StateT.run m t = _; rw [hm, h']⟩

/-! ## Per-op reductions: `opM_run_ok` at each op's pure `g` (definitional) -/

theorem run_leaf {s : Shape} (v : Tensor ℝ s) {t : Tape ℝ} :
    (TapeM.leaf (α := ℝ) v).run t
      = .ok ((Tape.leaf (t := t) v).2, (Tape.leaf (t := t) v).1) := by
  simp only [TapeM.leaf, TapeM.run, StateT.run, bind, StateT.bind, MonadState.get,
    MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set, pure, StateT.pure,
    Except.bind, Except.pure]

theorem run_add_ok {s : Shape} {aId bId : Nat} {t t' : Tape ℝ} {id : Nat}
    (h : Runtime.Autograd.Tape.add (α := ℝ) (s := s) t aId bId = .ok (t', id)) :
    (TapeM.add (α := ℝ) (s := s) aId bId).run t = .ok (id, t') :=
  opM_run_ok (g := fun tt => Runtime.Autograd.Tape.add (α := ℝ) (t := tt) (s := s) aId bId) h

theorem run_sub_ok {s : Shape} {aId bId : Nat} {t t' : Tape ℝ} {id : Nat}
    (h : Runtime.Autograd.Tape.sub (α := ℝ) (s := s) t aId bId = .ok (t', id)) :
    (TapeM.sub (α := ℝ) (s := s) aId bId).run t = .ok (id, t') :=
  opM_run_ok (g := fun tt => Runtime.Autograd.Tape.sub (α := ℝ) (t := tt) (s := s) aId bId) h

theorem run_mul_ok {s : Shape} {aId bId : Nat} {t t' : Tape ℝ} {id : Nat}
    (h : Runtime.Autograd.Tape.mul (α := ℝ) (s := s) t aId bId = .ok (t', id)) :
    (TapeM.mul (α := ℝ) (s := s) aId bId).run t = .ok (id, t') :=
  opM_run_ok (g := fun tt => Runtime.Autograd.Tape.mul (α := ℝ) (t := tt) (s := s) aId bId) h

theorem run_div_ok {s : Shape} {aId bId : Nat} {t t' : Tape ℝ} {id : Nat}
    (h : Runtime.Autograd.Tape.div (α := ℝ) (s := s) t aId bId = .ok (t', id)) :
    (TapeM.div (α := ℝ) (s := s) aId bId).run t = .ok (id, t') :=
  opM_run_ok (g := fun tt => Runtime.Autograd.Tape.div (α := ℝ) (t := tt) (s := s) aId bId) h

theorem run_scale_ok {s : Shape} {xId : Nat} {c : ℝ} {t t' : Tape ℝ} {id : Nat}
    (h : Runtime.Autograd.Tape.scale (α := ℝ) (s := s) t xId c = .ok (t', id)) :
    (TapeM.scale (α := ℝ) (s := s) xId c).run t = .ok (id, t') :=
  opM_run_ok (g := fun tt => Runtime.Autograd.Tape.scale (α := ℝ) (t := tt) (s := s) xId c) h

theorem run_exp_ok {s : Shape} {xId : Nat} {t t' : Tape ℝ} {id : Nat}
    (h : Runtime.Autograd.Tape.exp (α := ℝ) (s := s) t xId = .ok (t', id)) :
    (TapeM.exp (α := ℝ) (s := s) xId).run t = .ok (id, t') :=
  opM_run_ok (g := fun tt => Runtime.Autograd.Tape.exp (α := ℝ) (t := tt) (s := s) xId) h

theorem run_tanh_ok {s : Shape} {xId : Nat} {t t' : Tape ℝ} {id : Nat}
    (h : Runtime.Autograd.Tape.tanh (α := ℝ) (s := s) t xId = .ok (t', id)) :
    (TapeM.tanh (α := ℝ) (s := s) xId).run t = .ok (id, t') :=
  opM_run_ok (g := fun tt => Runtime.Autograd.Tape.tanh (α := ℝ) (t := tt) (s := s) xId) h

theorem run_sigmoid_ok {s : Shape} {xId : Nat} {t t' : Tape ℝ} {id : Nat}
    (h : Runtime.Autograd.Tape.sigmoid (α := ℝ) (s := s) t xId = .ok (t', id)) :
    (TapeM.sigmoid (α := ℝ) (s := s) xId).run t = .ok (id, t') :=
  opM_run_ok (g := fun tt => Runtime.Autograd.Tape.sigmoid (α := ℝ) (t := tt) (s := s) xId) h

theorem run_softplus_ok {s : Shape} {xId : Nat} {t t' : Tape ℝ} {id : Nat}
    (h : Runtime.Autograd.Tape.softplus (α := ℝ) (s := s) t xId = .ok (t', id)) :
    (TapeM.softplus (α := ℝ) (s := s) xId).run t = .ok (id, t') :=
  opM_run_ok (g := fun tt => Runtime.Autograd.Tape.softplus (α := ℝ) (t := tt) (s := s) xId) h

theorem run_log_ok {s : Shape} {xId : Nat} {t t' : Tape ℝ} {id : Nat}
    (h : Runtime.Autograd.Tape.log (α := ℝ) (s := s) t xId = .ok (t', id)) :
    (TapeM.log (α := ℝ) (s := s) xId).run t = .ok (id, t') :=
  opM_run_ok (g := fun tt => Runtime.Autograd.Tape.log (α := ℝ) (t := tt) (s := s) xId) h

theorem run_relu_ok {s : Shape} {xId : Nat} {t t' : Tape ℝ} {id : Nat}
    (h : Runtime.Autograd.Tape.relu (α := ℝ) (s := s) t xId = .ok (t', id)) :
    (TapeM.relu (α := ℝ) (s := s) xId).run t = .ok (id, t') :=
  opM_run_ok (g := fun tt => Runtime.Autograd.Tape.relu (α := ℝ) (t := tt) (s := s) xId) h

theorem run_abs_ok {s : Shape} {xId : Nat} {t t' : Tape ℝ} {id : Nat}
    (h : Runtime.Autograd.Tape.abs (α := ℝ) (s := s) t xId = .ok (t', id)) :
    (TapeM.abs (α := ℝ) (s := s) xId).run t = .ok (id, t') :=
  opM_run_ok (g := fun tt => Runtime.Autograd.Tape.abs (α := ℝ) (t := tt) (s := s) xId) h

theorem run_sqrt_ok {s : Shape} {xId : Nat} {t t' : Tape ℝ} {id : Nat}
    (h : Runtime.Autograd.Tape.sqrt (α := ℝ) (s := s) t xId = .ok (t', id)) :
    (TapeM.sqrt (α := ℝ) (s := s) xId).run t = .ok (id, t') :=
  opM_run_ok (g := fun tt => Runtime.Autograd.Tape.sqrt (α := ℝ) (t := tt) (s := s) xId) h

/-! ## The demo: a `do`-block program is eager-provenance-covered -/

/-- The fresh id a successful `Tape.mul` returns is the pre-append tape size (the
    `addNode` invariant, read back through the op's `do`-block). -/
theorem tape_mul_id {s : Shape} {t t' : Tape ℝ} {aId bId id : Nat}
    (h : Runtime.Autograd.Tape.mul (α := ℝ) (s := s) t aId bId = .ok (t', id)) :
    id = t.size := by
  cases hA : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) aId with
  | error e => simp [Runtime.Autograd.Tape.mul, hA, bind, Except.bind] at h
  | ok aT =>
    cases hB : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) bId with
    | error e => simp [Runtime.Autograd.Tape.mul, hA, hB, bind, Except.bind] at h
    | ok bT =>
      simp only [Runtime.Autograd.Tape.mul, hA, hB, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at h
      have h2 := congrArg Prod.snd h
      rw [Runtime.Autograd.Tape.addNode_id] at h2
      exact h2.symm

/-- User-style eager program: `(x₀ * x₁) * c`, written monadically. -/
def progMulScale (c : ℝ) (x0T x1T : Tensor ℝ Shape.scalar) : TapeM ℝ Nat := do
  let a ← TapeM.leaf x0T
  let b ← TapeM.leaf x1T
  let m ← TapeM.mul (α := ℝ) (s := Shape.scalar) a b
  TapeM.scale (α := ℝ) (s := Shape.scalar) m c

/-- Index of the `mul` output in the context extended by the first node. -/
def ixm : Idx (Γ2 ++ [Shape.scalar]) Shape.scalar := ⟨⟨2, by decide⟩, rfl⟩

/-- The 2-node P-graph the program realises: `scale (mul x₀ x₁) c`. -/
def mulScaleGraph (c : ℝ) : Graph Γ2 [Shape.scalar, Shape.scalar] :=
  .snoc (.snoc .nil (TapeNodes.mul ix0 ix1)) (TapeNodes.scale ixm c)

set_option maxHeartbeats 6400000 in
/-- The bridge demo: a successful monadic `exec` of `progMulScale` from the empty tape is
    covered by `EagerBuilds` at `mulScaleGraph` — the closure reaches `do`-block programs.

    The proof is pure peeling: `exec_inv` + three `run_bind_inv` decompose the `do`-block,
    `run_leaf` computes the two leaf stages (ids `0`, `1`; tape = the `addLeaves` fold),
    `opM_run_inv` turns the two monadic op stages back into pure `Tape.mul`/`Tape.scale`
    successes, and those are exactly the `hop` obligations of the `EagerBuilds.mul` and
    `EagerBuilds.scale` constructors. -/
theorem progMulScale_exec_eagerBuilds (c : ℝ) (x0T x1T : Tensor ℝ Shape.scalar)
    {t' : PRSim.RTape}
    (h : TapeM.exec (Runtime.Autograd.Tape.empty) (progMulScale c x0T x1T) = .ok t') :
    PRSim.EagerBuilds (mulScaleGraph c) (.cons x0T (.cons x1T .nil)) t' := by
  obtain ⟨idF, hrun⟩ := exec_inv h
  -- peel the four stages of the do-block
  obtain ⟨a, t1, hleaf0, hrest⟩ := run_bind_inv (m := TapeM.leaf x0T) hrun
  obtain ⟨b, t2, hleaf1, hrest2⟩ := run_bind_inv (m := TapeM.leaf x1T) hrest
  obtain ⟨m, t3, hmulM, hscaleM⟩ := run_bind_inv hrest2
  -- the two leaf stages are deterministic: extract ids and tapes
  rw [run_leaf] at hleaf0 hleaf1
  simp only [Except.ok.injEq, Prod.mk.injEq] at hleaf0 hleaf1
  obtain ⟨ha, ht1⟩ := hleaf0
  obtain ⟨hb, ht2⟩ := hleaf1
  subst ht1 ht2 ha hb
  -- the two op stages: back to pure `Tape` successes
  have hmul := opM_run_inv (g := fun tt =>
    Runtime.Autograd.Tape.mul (α := ℝ) (t := tt) (s := Shape.scalar)
      (Runtime.Autograd.Tape.leaf (t := Runtime.Autograd.Tape.empty) x0T).2
      (Runtime.Autograd.Tape.leaf
        (t := (Runtime.Autograd.Tape.leaf (t := Runtime.Autograd.Tape.empty) x0T).1) x1T).2)
    hmulM
  have hscale := opM_run_inv (g := fun tt =>
    Runtime.Autograd.Tape.scale (α := ℝ) (t := tt) (s := Shape.scalar) m c) hscaleM
  -- leaf ids are the pre-append sizes: 0 and 1
  have ha0 : (Runtime.Autograd.Tape.leaf (t := Runtime.Autograd.Tape.empty) x0T).2 = 0 := rfl
  have hb1 : (Runtime.Autograd.Tape.leaf
      (t := (Runtime.Autograd.Tape.leaf (t := Runtime.Autograd.Tape.empty) x0T).1) x1T).2
      = 1 := rfl
  rw [ha0, hb1] at hmul
  -- the two-leaf tape IS the `addLeaves` fold of the input list
  have htape :
      (Runtime.Autograd.Tape.leaf
        (t := (Runtime.Autograd.Tape.leaf (t := Runtime.Autograd.Tape.empty) x0T).1) x1T).1
      = Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty)
          (TList.cons x0T (TList.cons x1T TList.nil)) := rfl
  rw [htape] at hmul
  -- the mul id is the pre-append size of the two-leaf tape: 2
  have hm2 : m = 2 := by rw [tape_mul_id hmul]; rfl
  subst hm2
  -- assemble the two constructors
  exact PRSim.EagerBuilds.scale (g := .snoc .nil (TapeNodes.mul ix0 ix1)) ixm c
    (PRSim.EagerBuilds.mul (g := .nil) ix0 ix1
      (PRSim.EagerBuilds.nil (TList.cons x0T (TList.cons x1T TList.nil))) hmul)
    hscale

/-- Differentiability witness for the chained graph, from the upstream per-node facts. -/
def mulScaleCorrect (c : ℝ) : GraphFDerivCorrect (mulScaleGraph c) :=
  ⟨⟨PUnit.unit, TapeNodes.mulFderiv ix0 ix1⟩, TapeNodes.scaleFderiv ixm c⟩

set_option maxHeartbeats 6400000 in
/-- **The endpoint reaches `do`-block programs**: composing the bridge demo with
    `direct_PR_soundness_eager`, the reverse pass on the tape a monadic program built realises
    the adjoint of the Fréchet derivative of the program's own forward evaluation. -/
example (c : ℝ) (x0T x1T : Tensor ℝ Shape.scalar) {t' : PRSim.RTape}
    (h : TapeM.exec (Runtime.Autograd.Tape.empty) (progMulScale c x0T x1T) = .ok t')
    (seed : TList (Γ2 ++ [Shape.scalar, Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (Algebra.TList.toAnyArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr
        ((fderiv ℝ ((mulScaleGraph c).evalVec)
            (flattenCtx (TList.cons x0T (TList.cons x1T TList.nil)))).adjoint
          (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager (mulScaleGraph c) (mulScaleCorrect c)
    (TList.cons x0T (TList.cons x1T TList.nil))
    (progMulScale_exec_eagerBuilds c x0T x1T h) seed

/--
info: 'PropertyKindCalculus.UncertaintyExamples.TapeMBridge.progMulScale_exec_eagerBuilds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms progMulScale_exec_eagerBuilds

/--
info: 'PropertyKindCalculus.UncertaintyExamples.TapeMBridge.run_div_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms run_div_ok

end

end PropertyKindCalculus.UncertaintyExamples.TapeMBridge
