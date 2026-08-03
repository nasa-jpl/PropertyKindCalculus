/-
# Eager-tape provenance: the runtime-built tape is the compiled tape, observationally

Stage 3.6 closed the direct P↔R simulation for *compiled* tapes and left one residual: the tape
PKC's `Sensitivity.gradient` actually runs on is built *eagerly* by the runtime constructors
(`Tape.leaf`/`Tape.add`/`Tape.mul`, via the `TapeM` sugar), not by `compileAux` — and `ForwardSim`
alone cannot identify the two, because it does not pin the opaque backward closures
(`PRSimulation.lean` §6/§7). This module closes that identification for the `leaf`/`add`/`sub`/`mul`
fragment, as pure accounting:

* **`EagerBuilds g x t`** (§E) is the provenance relation: `t` is the tape the eager constructors
  build for the P-graph `g` at input `x` (leaves = `addLeaves`, which *is* the `Tape.leaf` fold;
  one `Tape.add`/`Tape.sub`/`Tape.mul` call per `TapeNodes.add`/`TapeNodes.sub`/`TapeNodes.mul`
  node).
* **`backwardDenseFrom_eager_eq_compiled`** (§F): on such a tape the total dense reverse pass
  computes *exactly* what it computes on `compileAux g.toAlgebra x ()` — same `Result`, same
  array. The proof never re-derives the reverse-pass fold: the compiled node's dense
  contribution list is folded by the upstream accumulation bridge
  (`foldlM_addGradAll_toIndexedAnyList_eq_add`), the eager node's sparse two-element list by the
  single-slot lemma `addGradAll_toAnyArray_single` (§C), and the two context updates coincide by
  the vectorization homomorphisms of Stage 3.6 (`toVecT_mulSpec` &c.) through flatten-injectivity
  (§B). Push-invariance lemmas (§D) restrict the loop over the extended tape to the prefix, so
  the induction consumes its hypothesis directly.
* **`direct_PR_soundness_eager`** (§F): therefore the Stage-3.5/3.6 endpoint transfers verbatim —
  on the eagerly built tape, the dense reverse pass succeeds and the input-prefix of its output
  realises `(fderiv ℝ eval x)† seed`. With `forwardSim_eager`, eager tapes also inhabit
  `ForwardSim`.

`sub` is the second binary crank (§B `sub_vjp_add_eq`, §E/§F `sub` cases): the same machine as
`add`, save that the runtime `Tape.sub` backward feeds the *negated* cotangent `subSpec (fill 0) δ`
to the right parent — closed by two extra facts, `toVecT_subSpec` (vectorization is subtractive)
and `single_neg` (the one-hot injection is odd). It demonstrates that a further op is genuinely
"one crank": nothing in §C/§D/§F's structure changed, only the per-op §B accounting.

`div` is the third binary crank (§B `div_vjp_add_eq`, §E/§F `div` cases): the runtime `Tape.div`
backward feeds the quotient-rule cotangents — `divSpec δ b` to the left parent and the negated
`subSpec (fill 0) (mulSpec δ (divSpec a (mulSpec b b)))` to the right — and the P node
`TapeNodes.div` stores exactly the matching `b⁻¹` / `-a·(b²)⁻¹` vjp blocks; the provenance
accounting is *unconditional* (it is pure bookkeeping over the totalized `0⁻¹ = 0` division), the
nonzero-denominator side condition only enters at the endpoint through the pointwise
`direct_PR_soundness_eager_at`/`divFderivAt` route. The extra fact is the pointwise
`toVecT_divSpec_apply` (vectorization divides coordinatewise); the rest is `ring` over ℝ.

`scale` is the first *unary* crank (§B `scale_vjp_add_eq`, §E/§F `scale` cases): one parent, one
contribution `scaleSpec δ c`, so it exercises the reduced (one-`addGradAll`) variant of the machine
— the shape every `Arithmetic`/`Elementwise` unary shares (activations included: each is
`[(xId, mulSpec (f'Spec x) δ)]`, structurally identical to `scale`). The extra fact is that `toVecT`
intertwines `scaleSpec` with the scalar action (`toVecT_scaleSpec`, via the unary `toVecT_mapSpec_apply`).

What this does *not* cover, honestly: the remaining named unary ops (the `TapeNodes.elemwise`
activation family — `exp`/`log`/`tanh`/`sigmoid`/…), each a `scale`-shaped instance of this unary
machine differing only in the per-op contribution `mulSpec (f'Spec x) δ` and its accounting;
the `TapeM` `StateT` sugar (each `TapeM` op is a one-line wrapper around the
corresponding `Tape` constructor; identifying a `TapeM.run` trace with an `EagerBuilds` derivation is
bookkeeping over that wrapper); and structural nodes (matmul/conv/softmax) whose non-sparse vjp is a
different machine, out of this file's frame.
-/

import PropertyKindCalculus.Uncertainty.Experiments.PRSimulation

open Spec Tensor Proofs.Autograd

noncomputable section

namespace PRSim

/- ===========================================================================================
   §A.  Erasure algebra: zeros, casts, and `flattenCtx` on `single`.
   =========================================================================================== -/

/-- `castVec` along a self-equality is the identity (proof-irrelevant). -/
theorem castVec_self {n : Nat} (h : n = n) (v : Vec n) : castVec h v = v := by
  ext i
  simp

/-- `toVecT` commutes with `castShape` (as a `castVec` on coordinates). -/
theorem toVecT_castShape {s₁ s₂ : Shape} (h : s₁ = s₂) (t : Tensor ℝ s₁) :
    toVecT (t := Tensor.castShape t h)
      = castVec (congrArg Spec.Shape.size h) (toVecT (t := t)) := by
  cases h
  rw [castVec_self]
  simp

/-- Pointwise: every coordinate of a `fill` tensor is the fill value. -/
theorem toVecT_fill_apply (c : ℝ) :
    ∀ {s : Shape} (i : Fin (Spec.Shape.size s)), toVecT (t := fill c s) i = c
  | .scalar, i => by
      rw [show fill c Shape.scalar = Tensor.scalar c from rfl]
      exact toVecT_scalar_apply c i
  | .dim n s, i => by
      by_cases hm : Spec.Shape.size s = 0
      · exact absurd i.isLt (by simp [Spec.Shape.size, hm])
      · have hmpos : 0 < Spec.Shape.size s := Nat.pos_of_ne_zero hm
        obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective i
        have hstep : fill c (Shape.dim n s) = Tensor.dim (fun _ => fill c s) := rfl
        rw [hstep, toVecT_dim_apply hmpos]
        exact toVecT_fill_apply c p.2

/-- The zero-filled tensor vectorizes to the zero vector. -/
theorem toVecT_fill_zero {s : Shape} : toVecT (t := fill (0 : ℝ) s) = 0 := by
  ext i
  simp [toVecT_fill_apply]

/-- `vecOfFun` of the constant-zero function is the zero vector. -/
theorem vecOfFun_zero {n : Nat} : vecOfFun (n := n) (fun _ => (0 : ℝ)) = 0 := by
  ext i
  simp

/-- Appending two zero vectors gives the zero vector. -/
theorem appendVec_zero {m n : Nat} :
    appendVec (m := m) (n := n) 0 0 = (0 : Vec (m + n)) := by
  ext i
  induction i using Fin.addCases with
  | left i => simp [appendVec, Fin.append_left]
  | right i => simp [appendVec, Fin.append_right]

/-- `flattenCtx` on a cons cell is `appendVec` of the vectorized head and flattened tail. -/
theorem flattenCtx_cons {s : Shape} {Γ' : List Shape} (x : Tensor ℝ s) (xs : TList Γ') :
    flattenCtx (Γ := s :: Γ') (TList.cons x xs)
      = appendVec (toVecT (t := x)) (flattenCtx xs) := rfl

/-- The all-zero context flattens to the zero vector. -/
theorem flattenCtx_zero :
    ∀ {Γ' : List Shape}, flattenCtx (Γ := Γ') (TList.zero) = 0
  | [] => rfl
  | s :: Γ' => by
      show flattenCtx (TList.cons (fill (0 : ℝ) s) TList.zero) = 0
      rw [flattenCtx_cons, toVecT_fill_zero, flattenCtx_zero (Γ' := Γ'), appendVec_zero]
      rfl

/-- Adding the all-zero context on the right is the identity. -/
theorem addSpec_fill_zero : ∀ {s : Shape} (t : Tensor ℝ s), addSpec t (fill (0 : ℝ) s) = t
  | .scalar, .scalar x => by
      show Tensor.scalar (x + 0) = Tensor.scalar x
      rw [add_zero]
  | .dim n s, .dim f => by
      show Tensor.dim (fun i => addSpec (f i) (fill (0 : ℝ) s)) = Tensor.dim f
      exact congrArg Tensor.dim (funext fun i => addSpec_fill_zero (f i))

/-- Adding the all-zero context on the right is the identity (context level). -/
theorem tlist_add_zero :
    ∀ {Γ' : List Shape} (w : TList Γ'), Algebra.TList.add (α := ℝ) w TList.zero = w
  | [], .nil => rfl
  | s :: Γ', .cons x xs => by
      show TList.cons (addSpec x (fill (0 : ℝ) s)) (Algebra.TList.add (α := ℝ) xs TList.zero)
          = TList.cons x xs
      rw [addSpec_fill_zero, tlist_add_zero xs]

/-- `flattenCtx` maps the one-hot context `TList.single` to the one-hot vector `CtxVec.single`. -/
theorem flattenCtx_single :
    ∀ {Γ' : List Shape} {s : Shape} (c : Idx Γ' s) (u : Tensor ℝ s),
      flattenCtx (TList.single c u) = CtxVec.single c (toVecT (t := u))
  | s0 :: Γ', s, ⟨⟨0, h0⟩, h⟩, u => by
      show flattenCtx (TList.cons (Tensor.castShape u h.symm) TList.zero)
          = CtxVec.singleRaw (Γ := s0 :: Γ') ⟨0, h0⟩
              (castVec (congrArg Spec.Shape.size h).symm (toVecT (t := u)))
      rw [flattenCtx_cons, flattenCtx_zero, toVecT_castShape]
      show appendVec (castVec (congrArg Spec.Shape.size h.symm) (toVecT (t := u))) 0
          = appendVec (castVec (congrArg Spec.Shape.size h).symm (toVecT (t := u)))
              (vecOfFun fun _ => (0 : ℝ))
      rw [vecOfFun_zero]
  | s0 :: Γ', s, ⟨⟨Nat.succ j, hj⟩, h⟩, u => by
      show flattenCtx (TList.cons (fill (0 : ℝ) s0)
            (TList.single (Γ := Γ') ⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, by simpa using h⟩ u))
          = CtxVec.singleRaw (Γ := s0 :: Γ') ⟨Nat.succ j, hj⟩
              (castVec (congrArg Spec.Shape.size h).symm (toVecT (t := u)))
      rw [flattenCtx_cons, toVecT_fill_zero,
        flattenCtx_single (Γ' := Γ') ⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, by simpa using h⟩ u]
      show appendVec 0
            (CtxVec.singleRaw (Γ := Γ') ⟨j, Nat.lt_of_succ_lt_succ hj⟩
              (castVec (congrArg Spec.Shape.size (by simpa using h :
                Γ'.get ⟨j, Nat.lt_of_succ_lt_succ hj⟩ = s)).symm (toVecT (t := u))))
          = appendVec (vecOfFun fun _ => (0 : ℝ))
              (CtxVec.singleRaw (Γ := Γ') ⟨j, Nat.lt_of_succ_lt_succ hj⟩
                (castVec (congrArg Spec.Shape.size h).symm (toVecT (t := u))))
      rw [vecOfFun_zero]

/-- Reading a block through `CtxVec.get` after flattening is the vectorized `getIdx`. -/
theorem getIdx_flattenCtx {Γ' : List Shape} {s : Shape} (c : Idx Γ' s) (w : TList Γ') :
    CtxVec.get c (flattenCtx w) = toVecT (t := getIdx w c) := by
  show castVec (congrArg Spec.Shape.size c.h) (CtxVec.getRaw c.i (flattenCtx w))
      = toVecT (t := Tensor.castShape (Algebra.TList.get (α := ℝ) w c.i) c.h)
  rw [getRaw_flattenCtx, toVecT_castShape]

/-- Contexts with equal flattenings are equal. -/
theorem flattenCtx_inj {Γ' : List Shape} {x y : TList Γ'}
    (h : flattenCtx x = flattenCtx y) : x = y := by
  rw [← unflattenCtx_flattenCtx (xs := x), h, unflattenCtx_flattenCtx]

/- ===========================================================================================
   §B.  Per-op identification: the eager forward value and the eager sparse context update are
        exactly the compiled node's forward value and vjp context update.
   =========================================================================================== -/

/-- The eager `mul` forward value is the P `mul` node's forward map. -/
theorem mul_forward_eq {Γ' : List Shape} {s : Shape} (a b : Idx Γ' s) (w : TList Γ') :
    (TapeNodes.mul (Γ := Γ') (s := s) a b).forward w = mulSpec (getIdx w a) (getIdx w b) := by
  have hvec : vecOfFun (n := Spec.Shape.size s)
        (fun i => toVecT (t := getIdx w a) i * toVecT (t := getIdx w b) i)
      = toVecT (t := mulSpec (getIdx w a) (getIdx w b)) :=
    (toVecT_mulSpec (getIdx w a) (getIdx w b)).symm
  show ofVecT (vecOfFun (n := Spec.Shape.size s)
        (fun i => CtxVec.get a (flattenCtx w) i * CtxVec.get b (flattenCtx w) i))
      = mulSpec (getIdx w a) (getIdx w b)
  rw [getIdx_flattenCtx, getIdx_flattenCtx, hvec, ofVecT_toVecT]

/-- The eager `add` forward value is the P `add` node's forward map. -/
theorem add_forward_eq {Γ' : List Shape} {s : Shape} (a b : Idx Γ' s) (w : TList Γ') :
    (TapeNodes.add (Γ := Γ') (s := s) a b).forward w = addSpec (getIdx w a) (getIdx w b) := by
  show ofVecT (CtxVec.get a (flattenCtx w) + CtxVec.get b (flattenCtx w))
      = addSpec (getIdx w a) (getIdx w b)
  rw [getIdx_flattenCtx, getIdx_flattenCtx, ← toVecT_addSpec, ofVecT_toVecT]

/-- **The `mul` accounting identity**: accumulating the eager sparse product-rule contributions
    is accumulating the compiled node's dense vjp context. -/
theorem mul_vjp_add_eq {Γ' : List Shape} {s : Shape} (a b : Idx Γ' s) (w : TList Γ')
    (d : Tensor ℝ s) (u : TList Γ') :
    Algebra.TList.add (α := ℝ)
        (Algebra.TList.add (α := ℝ) u (TList.single a (mulSpec d (getIdx w b))))
        (TList.single b (mulSpec d (getIdx w a)))
      = Algebra.TList.add (α := ℝ) u ((TapeNodes.mul (Γ := Γ') (s := s) a b).vjp w d) := by
  apply flattenCtx_inj
  have hA : vecOfFun (n := Spec.Shape.size s)
        (fun i => toVecT (t := d) i * CtxVec.get b (flattenCtx w) i)
      = toVecT (t := mulSpec d (getIdx w b)) := by
    rw [getIdx_flattenCtx]
    exact (toVecT_mulSpec d (getIdx w b)).symm
  have hB : vecOfFun (n := Spec.Shape.size s)
        (fun i => toVecT (t := d) i * CtxVec.get a (flattenCtx w) i)
      = toVecT (t := mulSpec d (getIdx w a)) := by
    rw [getIdx_flattenCtx]
    exact (toVecT_mulSpec d (getIdx w a)).symm
  show flattenCtx (Algebra.TList.add (α := ℝ)
        (Algebra.TList.add (α := ℝ) u (TList.single a (mulSpec d (getIdx w b))))
        (TList.single b (mulSpec d (getIdx w a))))
      = flattenCtx (Algebra.TList.add (α := ℝ) u
          (unflattenCtx
            (CtxVec.single a (vecOfFun (n := Spec.Shape.size s)
                (fun i => toVecT (t := d) i * CtxVec.get b (flattenCtx w) i))
              + CtxVec.single b (vecOfFun (n := Spec.Shape.size s)
                (fun i => toVecT (t := d) i * CtxVec.get a (flattenCtx w) i)))))
  rw [flattenCtx_add, flattenCtx_add, flattenCtx_add, flattenCtx_unflattenCtx,
    flattenCtx_single, flattenCtx_single, hA, hB, add_assoc]

/-- **The `add` accounting identity**: same statement for the copy rule of `add`. -/
theorem add_vjp_add_eq {Γ' : List Shape} {s : Shape} (a b : Idx Γ' s) (w : TList Γ')
    (d : Tensor ℝ s) (u : TList Γ') :
    Algebra.TList.add (α := ℝ)
        (Algebra.TList.add (α := ℝ) u (TList.single a d))
        (TList.single b d)
      = Algebra.TList.add (α := ℝ) u ((TapeNodes.add (Γ := Γ') (s := s) a b).vjp w d) := by
  apply flattenCtx_inj
  show flattenCtx (Algebra.TList.add (α := ℝ)
        (Algebra.TList.add (α := ℝ) u (TList.single a d)) (TList.single b d))
      = flattenCtx (Algebra.TList.add (α := ℝ) u
          (unflattenCtx (CtxVec.single a (toVecT (t := d)) + CtxVec.single b (toVecT (t := d)))))
  rw [flattenCtx_add, flattenCtx_add, flattenCtx_add, flattenCtx_unflattenCtx,
    flattenCtx_single, flattenCtx_single, add_assoc]

/- -------------------------------------------------------------------------------------------
   The `sub` op (second binary crank): identical machine to `add`, save that the runtime `Tape.sub`
   backward feeds the *negated* cotangent `subSpec (fill 0) δ` to the right parent.  Two extra
   facts close the gap: vectorization is subtractive (`toVecT_subSpec`, the `subSpec` analog of the
   upstream `toVecT_addSpec`) and the one-hot injection is odd (`single_neg`).
   ------------------------------------------------------------------------------------------- -/

/-- Vectorization is subtractive: `toVecT` maps `subSpec` to vector subtraction (the `subSpec`
    analog of `toVecT_addSpec`; proved coordinatewise through `toVecT_map2Spec_apply`). -/
theorem toVecT_subSpec {s : Shape} (a b : Tensor ℝ s) :
    toVecT (t := subSpec a b) = toVecT (t := a) - toVecT (t := b) := by
  have h : ∀ i, toVecT (t := subSpec a b) i = toVecT (t := a) i - toVecT (t := b) i :=
    fun i => toVecT_map2Spec_apply (f := (· - ·)) a b i
  calc toVecT (t := subSpec a b)
      = vecOfFun (fun i => toVecT (t := subSpec a b) i) := (vecOfFun_eta _).symm
    _ = vecOfFun (fun i => toVecT (t := a) i - toVecT (t := b) i) :=
        congrArg (vecOfFun (n := Spec.Shape.size s)) (funext h)
    _ = toVecT (t := a) - toVecT (t := b) := by ext i; simp [PiLp.sub_apply]

/-- The eager `sub` forward value is the P `sub` node's forward map. -/
theorem sub_forward_eq {Γ' : List Shape} {s : Shape} (a b : Idx Γ' s) (w : TList Γ') :
    (TapeNodes.sub (Γ := Γ') (s := s) a b).forward w = subSpec (getIdx w a) (getIdx w b) := by
  show ofVecT (CtxVec.get a (flattenCtx w) - CtxVec.get b (flattenCtx w))
      = subSpec (getIdx w a) (getIdx w b)
  rw [getIdx_flattenCtx, getIdx_flattenCtx, ← toVecT_subSpec, ofVecT_toVecT]

/-- The one-hot context injection is odd: `single c (-v) = - single c v`.  (Proved by
    inner-product extensionality through the `get`/`single` adjunction `inner_get_single`.) -/
theorem single_neg {Γ' : List Shape} {s : Shape} (c : Idx Γ' s) (v : Vec (Spec.Shape.size s)) :
    CtxVec.single c (-v) = - CtxVec.single c v := by
  refine ext_inner_left ℝ ?_
  intro w
  simp only [CtxVec.inner_get_single, inner_neg_right]

/-- **The `sub` accounting identity**: accumulating the eager sparse contributions — the cotangent
    `δ` to `a`, its negation `subSpec (fill 0) δ` to `b` — is accumulating the compiled node's dense
    vjp context. -/
theorem sub_vjp_add_eq {Γ' : List Shape} {s : Shape} (a b : Idx Γ' s) (w : TList Γ')
    (d : Tensor ℝ s) (u : TList Γ') :
    Algebra.TList.add (α := ℝ)
        (Algebra.TList.add (α := ℝ) u (TList.single a d))
        (TList.single b (subSpec (fill (0 : ℝ) s) d))
      = Algebra.TList.add (α := ℝ) u ((TapeNodes.sub (Γ := Γ') (s := s) a b).vjp w d) := by
  apply flattenCtx_inj
  have hneg : toVecT (t := subSpec (fill (0 : ℝ) s) d) = - toVecT (t := d) := by
    rw [toVecT_subSpec, toVecT_fill_zero, zero_sub]
  show flattenCtx (Algebra.TList.add (α := ℝ)
        (Algebra.TList.add (α := ℝ) u (TList.single a d))
        (TList.single b (subSpec (fill (0 : ℝ) s) d)))
      = flattenCtx (Algebra.TList.add (α := ℝ) u
          (unflattenCtx (CtxVec.single a (toVecT (t := d)) - CtxVec.single b (toVecT (t := d)))))
  rw [flattenCtx_add, flattenCtx_add, flattenCtx_add, flattenCtx_unflattenCtx,
    flattenCtx_single, flattenCtx_single, hneg, single_neg]
  abel

/- -------------------------------------------------------------------------------------------
   The `div` op (third binary crank): identical machine to `sub`, save that the runtime `Tape.div`
   backward feeds the quotient-rule cotangents — `divSpec δ b` to the left parent and the negated
   `subSpec (fill 0) (mulSpec δ (divSpec a (mulSpec b b)))` to the right parent — matching the
   `b⁻¹` / `-a·(b²)⁻¹` vjp blocks of the P node `TapeNodes.div`.  The extra fact is the pointwise
   `toVecT_divSpec_apply` (vectorization divides coordinatewise); the accounting is then `ring`
   over ℝ (unconditional under the totalized `0⁻¹ = 0` division).
   ------------------------------------------------------------------------------------------- -/

/-- Pointwise: vectorization intertwines `divSpec` with coordinatewise division (the `divSpec`
    analog of the pointwise reading of `toVecT_subSpec`, via `toVecT_map2Spec_apply`). -/
theorem toVecT_divSpec_apply {s : Shape} (a b : Tensor ℝ s) (i : Fin (Spec.Shape.size s)) :
    toVecT (t := divSpec a b) i = toVecT (t := a) i / toVecT (t := b) i := by
  simp only [divSpec]
  exact toVecT_map2Spec_apply (f := (· / ·)) a b i

/-- The eager `div` forward value is the P `div` node's forward map. -/
theorem div_forward_eq {Γ' : List Shape} {s : Shape} (a b : Idx Γ' s) (w : TList Γ') :
    (TapeNodes.div (Γ := Γ') (s := s) a b).forward w = divSpec (getIdx w a) (getIdx w b) := by
  have hvec : vecOfFun (n := Spec.Shape.size s)
        (fun i => toVecT (t := getIdx w a) i / toVecT (t := getIdx w b) i)
      = toVecT (t := divSpec (getIdx w a) (getIdx w b)) := by
    calc vecOfFun (n := Spec.Shape.size s)
          (fun i => toVecT (t := getIdx w a) i / toVecT (t := getIdx w b) i)
        = vecOfFun (fun i => toVecT (t := divSpec (getIdx w a) (getIdx w b)) i) :=
          congrArg (vecOfFun (n := Spec.Shape.size s))
            (funext fun i => (toVecT_divSpec_apply (getIdx w a) (getIdx w b) i).symm)
      _ = toVecT (t := divSpec (getIdx w a) (getIdx w b)) := vecOfFun_eta _
  show ofVecT (vecOfFun (n := Spec.Shape.size s)
        (fun i => CtxVec.get a (flattenCtx w) i / CtxVec.get b (flattenCtx w) i))
      = divSpec (getIdx w a) (getIdx w b)
  rw [getIdx_flattenCtx, getIdx_flattenCtx, hvec, ofVecT_toVecT]

/-- **The `div` accounting identity**: accumulating the eager sparse quotient-rule contributions —
    `divSpec δ b` to `a`, the negated `subSpec (fill 0) (mulSpec δ (divSpec a (mulSpec b b)))` to
    `b` — is accumulating the compiled node's dense vjp context. -/
theorem div_vjp_add_eq {Γ' : List Shape} {s : Shape} (a b : Idx Γ' s) (w : TList Γ')
    (d : Tensor ℝ s) (u : TList Γ') :
    Algebra.TList.add (α := ℝ)
        (Algebra.TList.add (α := ℝ) u (TList.single a (divSpec d (getIdx w b))))
        (TList.single b (subSpec (fill (0 : ℝ) s)
          (mulSpec d (divSpec (getIdx w a) (mulSpec (getIdx w b) (getIdx w b))))))
      = Algebra.TList.add (α := ℝ) u ((TapeNodes.div (Γ := Γ') (s := s) a b).vjp w d) := by
  apply flattenCtx_inj
  have hA : vecOfFun (n := Spec.Shape.size s)
        (fun i => toVecT (t := d) i * (CtxVec.get b (flattenCtx w) i)⁻¹)
      = toVecT (t := divSpec d (getIdx w b)) := by
    rw [getIdx_flattenCtx]
    calc vecOfFun (n := Spec.Shape.size s)
          (fun i => toVecT (t := d) i * (toVecT (t := getIdx w b) i)⁻¹)
        = vecOfFun (fun i => toVecT (t := divSpec d (getIdx w b)) i) :=
          congrArg (vecOfFun (n := Spec.Shape.size s)) (funext fun i => by
            rw [toVecT_divSpec_apply]
            ring)
      _ = toVecT (t := divSpec d (getIdx w b)) := vecOfFun_eta _
  have hB : vecOfFun (n := Spec.Shape.size s)
        (fun i => toVecT (t := d) i *
          (-(CtxVec.get a (flattenCtx w) i) * ((CtxVec.get b (flattenCtx w) i) ^ 2)⁻¹))
      = toVecT (t := subSpec (fill (0 : ℝ) s)
          (mulSpec d (divSpec (getIdx w a) (mulSpec (getIdx w b) (getIdx w b))))) := by
    rw [getIdx_flattenCtx, getIdx_flattenCtx]
    calc vecOfFun (n := Spec.Shape.size s)
          (fun i => toVecT (t := d) i *
            (-(toVecT (t := getIdx w a) i) * ((toVecT (t := getIdx w b) i) ^ 2)⁻¹))
        = vecOfFun (fun i => toVecT (t := subSpec (fill (0 : ℝ) s)
            (mulSpec d (divSpec (getIdx w a) (mulSpec (getIdx w b) (getIdx w b))))) i) :=
          congrArg (vecOfFun (n := Spec.Shape.size s)) (funext fun i => by
            simp only [subSpec, mulSpec, toVecT_map2Spec_apply, toVecT_divSpec_apply,
              toVecT_fill_apply]
            ring)
      _ = toVecT (t := subSpec (fill (0 : ℝ) s)
            (mulSpec d (divSpec (getIdx w a) (mulSpec (getIdx w b) (getIdx w b))))) :=
          vecOfFun_eta _
  show flattenCtx (Algebra.TList.add (α := ℝ)
        (Algebra.TList.add (α := ℝ) u (TList.single a (divSpec d (getIdx w b))))
        (TList.single b (subSpec (fill (0 : ℝ) s)
          (mulSpec d (divSpec (getIdx w a) (mulSpec (getIdx w b) (getIdx w b)))))))
      = flattenCtx (Algebra.TList.add (α := ℝ) u
          (unflattenCtx
            (CtxVec.single a (vecOfFun (n := Spec.Shape.size s)
                (fun i => toVecT (t := d) i * (CtxVec.get b (flattenCtx w) i)⁻¹))
              + CtxVec.single b (vecOfFun (n := Spec.Shape.size s)
                (fun i => toVecT (t := d) i *
                  (-(CtxVec.get a (flattenCtx w) i) * ((CtxVec.get b (flattenCtx w) i) ^ 2)⁻¹))))))
  rw [flattenCtx_add, flattenCtx_add, flattenCtx_add, flattenCtx_unflattenCtx,
    flattenCtx_single, flattenCtx_single, hA, hB, add_assoc]

/- -------------------------------------------------------------------------------------------
   The `scale` op (first *unary* crank): one parent, one contribution `scaleSpec δ c`.  This is the
   one-parent variant of the machine — the whole `Arithmetic`/`Elementwise` unary family (`scale`,
   and every `TapeNodes.elemwise`-based activation) has this shape.  The extra vectorization fact is
   that `toVecT` intertwines `scaleSpec` with the scalar action `c • ·`.
   ------------------------------------------------------------------------------------------- -/

/-- Pointwise: `mapSpec f` acts coordinatewise under vectorization (unary analog of
    `toVecT_map2Spec_apply`). -/
theorem toVecT_mapSpec_apply {f : ℝ → ℝ} :
    ∀ {s : Shape} (t : Tensor ℝ s) (i : Fin (Spec.Shape.size s)),
      toVecT (t := mapSpec f t) i = f (toVecT (t := t) i)
  | .scalar, .scalar x, i => by
      simp only [mapSpec]
      rw [toVecT_scalar_apply, toVecT_scalar_apply]
  | .dim n s, .dim fa, i => by
      by_cases hm : Spec.Shape.size s = 0
      · exact absurd i.isLt (by simp [Spec.Shape.size, hm])
      · have hmpos : 0 < Spec.Shape.size s := Nat.pos_of_ne_zero hm
        obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective i
        have hstep : mapSpec f (Tensor.dim fa) = Tensor.dim (fun j => mapSpec f (fa j)) := rfl
        rw [hstep, toVecT_dim_apply hmpos, toVecT_dim_apply hmpos]
        exact toVecT_mapSpec_apply (fa p.1) p.2

/-- Vectorization intertwines `scaleSpec` (a `mapSpec (· * c)`) with the scalar action `c • ·`. -/
theorem toVecT_scaleSpec {s : Shape} (t : Tensor ℝ s) (c : ℝ) :
    toVecT (t := scaleSpec t c) = c • toVecT (t := t) := by
  ext i
  have h : toVecT (t := scaleSpec t c) i = toVecT (t := t) i * c := by
    simpa [scaleSpec] using toVecT_mapSpec_apply (f := fun x => x * c) t i
  rw [h, PiLp.smul_apply, smul_eq_mul, mul_comm]

/-- The eager `scale` forward value is the P `scale` node's forward map. -/
theorem scale_forward_eq {Γ' : List Shape} {s : Shape} (idx : Idx Γ' s) (c : ℝ) (w : TList Γ') :
    (TapeNodes.scale (Γ := Γ') (s := s) idx c).forward w = scaleSpec (getIdx w idx) c := by
  show ofVecT (c • CtxVec.get idx (flattenCtx w)) = scaleSpec (getIdx w idx) c
  rw [getIdx_flattenCtx, ← toVecT_scaleSpec, ofVecT_toVecT]

/-- **The `scale` accounting identity**: accumulating the single eager contribution `scaleSpec δ c`
    at the parent slot is accumulating the compiled node's dense vjp context. -/
theorem scale_vjp_add_eq {Γ' : List Shape} {s : Shape} (idx : Idx Γ' s) (c : ℝ) (w : TList Γ')
    (d : Tensor ℝ s) (u : TList Γ') :
    Algebra.TList.add (α := ℝ) u (TList.single idx (scaleSpec d c))
      = Algebra.TList.add (α := ℝ) u ((TapeNodes.scale (Γ := Γ') (s := s) idx c).vjp w d) := by
  apply flattenCtx_inj
  show flattenCtx (Algebra.TList.add (α := ℝ) u (TList.single idx (scaleSpec d c)))
      = flattenCtx (Algebra.TList.add (α := ℝ) u
          (unflattenCtx (CtxVec.single idx (c • toVecT (t := d)))))
  rw [flattenCtx_add, flattenCtx_add, flattenCtx_unflattenCtx, flattenCtx_single, toVecT_scaleSpec]

/- -------------------------------------------------------------------------------------------
   The elementwise family (`TapeNodes.elemwise idx f f'`), generic in the scalar map `f` and its
   derivative `f'`.  This is the *unary crank abstracted*: `scale` above is the special case
   `f = (· * c)`, `f' = const c`; every activation (`exp`, `tanh`, `sigmoid`, …) is another
   instance.  The two bridges below are the elementwise analogues of `scale_forward_eq` and
   `scale_vjp_add_eq`, parameterized by the runtime forward/derivative specs and the single
   pointwise fact that vectorizing each spec applies the corresponding scalar map coordinatewise.
   The runtime backward for the whole family is `mulSpec (f'Spec x) δ` (see `Engine/Core/Elementwise`
   and `ActivationsLoss`); the constructor `EagerBuilds.unary` (§E) keys on the shared `Tape.unary`
   node shape they all reduce to.
   ------------------------------------------------------------------------------------------- -/

/-- The eager elementwise forward value is the P `elemwise` node's forward map, whenever the runtime
    forward spec `fwdSpec` vectorizes to `f` coordinatewise. -/
theorem elemwise_forward_eq {Γ' : List Shape} {s : Shape} (idx : Idx Γ' s) (f f' : ℝ → ℝ)
    (fwdSpec : Tensor ℝ s → Tensor ℝ s)
    (hfs : ∀ (u : Tensor ℝ s) (i : Fin (Spec.Shape.size s)),
        toVecT (t := fwdSpec u) i = f (toVecT (t := u) i))
    (w : TList Γ') :
    (TapeNodes.elemwise (Γ := Γ') (s := s) idx f f').forward w = fwdSpec (getIdx w idx) := by
  have hfwd_vec : toVecT (t := fwdSpec (getIdx w idx))
      = vecOfFun (n := Spec.Shape.size s) (fun i => f (toVecT (t := getIdx w idx) i)) := by
    calc toVecT (t := fwdSpec (getIdx w idx))
        = vecOfFun (fun i => toVecT (t := fwdSpec (getIdx w idx)) i) := (vecOfFun_eta _).symm
      _ = vecOfFun (fun i => f (toVecT (t := getIdx w idx) i)) :=
          congrArg (vecOfFun (n := Spec.Shape.size s)) (funext fun i => hfs _ i)
  show ofVecT (vecOfFun (n := Spec.Shape.size s)
        (fun i => f (CtxVec.get idx (flattenCtx w) i))) = fwdSpec (getIdx w idx)
  rw [getIdx_flattenCtx, ← hfwd_vec, ofVecT_toVecT]

/-- **The elementwise accounting identity**: accumulating the single eager contribution
    `mulSpec (f'Spec x) δ` is accumulating the compiled `elemwise` node's dense vjp context,
    whenever the runtime derivative spec `f'Spec` vectorizes to `f'` coordinatewise. -/
theorem elemwise_vjp_add_eq {Γ' : List Shape} {s : Shape} (idx : Idx Γ' s) (f f' : ℝ → ℝ)
    (f'Spec : Tensor ℝ s → Tensor ℝ s)
    (hf's : ∀ (u : Tensor ℝ s) (i : Fin (Spec.Shape.size s)),
        toVecT (t := f'Spec u) i = f' (toVecT (t := u) i))
    (w : TList Γ') (d : Tensor ℝ s) (u : TList Γ') :
    Algebra.TList.add (α := ℝ) u (TList.single idx (mulSpec (f'Spec (getIdx w idx)) d))
      = Algebra.TList.add (α := ℝ) u ((TapeNodes.elemwise (Γ := Γ') (s := s) idx f f').vjp w d) := by
  apply flattenCtx_inj
  have hcontrib : toVecT (t := mulSpec (f'Spec (getIdx w idx)) d)
      = vecOfFun (n := Spec.Shape.size s)
          (fun i => toVecT (t := d) i * f' (toVecT (t := getIdx w idx) i)) := by
    calc toVecT (t := mulSpec (f'Spec (getIdx w idx)) d)
        = vecOfFun (fun i => toVecT (t := mulSpec (f'Spec (getIdx w idx)) d) i) := (vecOfFun_eta _).symm
      _ = vecOfFun (fun i => toVecT (t := d) i * f' (toVecT (t := getIdx w idx) i)) :=
          congrArg (vecOfFun (n := Spec.Shape.size s)) (funext fun i => by
            simp only [mulSpec]; rw [toVecT_map2Spec_apply (f := (· * ·)), hf's]; ring)
  show flattenCtx (Algebra.TList.add (α := ℝ) u (TList.single idx (mulSpec (f'Spec (getIdx w idx)) d)))
      = flattenCtx (Algebra.TList.add (α := ℝ) u
          (unflattenCtx (CtxVec.single idx (vecOfFun (n := Spec.Shape.size s)
            (fun i => toVecT (t := d) i * f' (CtxVec.get idx (flattenCtx w) i))))))
  rw [flattenCtx_add, flattenCtx_add, flattenCtx_unflattenCtx, flattenCtx_single, hcontrib,
    getIdx_flattenCtx]

/- ===========================================================================================
   §C.  The eager sparse accumulate: one `addGradAll` call at slot `c` performs the one-hot
        context addition.  (The compiled dense list is handled by the upstream bridge
        `foldlM_addGradAll_toIndexedAnyList_eq_add`; this is its two-line sparse counterpart.)
   =========================================================================================== -/

/-- List-level: adding a one-hot context is a `List.set` at its slot. -/
theorem toAnyList_add_single :
    ∀ {Γ' : List Shape} {s : Shape} (w : TList Γ') (c : Idx Γ' s) (u : Tensor ℝ s),
      Algebra.TList.toAnyList (α := ℝ)
          (Algebra.TList.add (α := ℝ) w (TList.single c u))
        = (Algebra.TList.toAnyList (α := ℝ) w).set c.i.val
            (mkAny (addSpec (Algebra.TList.get (α := ℝ) w c.i) (Tensor.castShape u c.h.symm)))
  | s0 :: Γ', s, .cons x xs, ⟨⟨0, h0⟩, h⟩, u => by
      show Algebra.TList.toAnyList (α := ℝ)
            (TList.cons (addSpec x (Tensor.castShape u h.symm))
              (Algebra.TList.add (α := ℝ) xs TList.zero))
          = (mkAny x :: Algebra.TList.toAnyList (α := ℝ) xs).set 0
              (mkAny (addSpec x (Tensor.castShape u h.symm)))
      rw [tlist_add_zero]
      rfl
  | s0 :: Γ', s, .cons x xs, ⟨⟨Nat.succ j, hj⟩, h⟩, u => by
      show Algebra.TList.toAnyList (α := ℝ)
            (TList.cons (addSpec x (fill (0 : ℝ) s0))
              (Algebra.TList.add (α := ℝ) xs
                (TList.single ⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, by simpa using h⟩ u)))
          = (mkAny x :: Algebra.TList.toAnyList (α := ℝ) xs).set (j + 1)
              (mkAny (addSpec
                (Algebra.TList.get (α := ℝ) xs ⟨j, Nat.lt_of_succ_lt_succ hj⟩)
                (Tensor.castShape u (by simpa using h :
                  Γ'.get ⟨j, Nat.lt_of_succ_lt_succ hj⟩ = s).symm)))
      rw [addSpec_fill_zero]
      show mkAny x :: Algebra.TList.toAnyList (α := ℝ)
            (Algebra.TList.add (α := ℝ) xs
              (TList.single ⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, by simpa using h⟩ u))
          = mkAny x :: (Algebra.TList.toAnyList (α := ℝ) xs).set j
              (mkAny (addSpec
                (Algebra.TList.get (α := ℝ) xs ⟨j, Nat.lt_of_succ_lt_succ hj⟩)
                (Tensor.castShape u (by simpa using h :
                  Γ'.get ⟨j, Nat.lt_of_succ_lt_succ hj⟩ = s).symm)))
      rw [toAnyList_add_single xs ⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, by simpa using h⟩ u]

/-- Array-level form of `toAnyList_add_single`. -/
theorem toAnyArray_add_single {Γ' : List Shape} {s : Shape} (w : TList Γ') (c : Idx Γ' s)
    (u : Tensor ℝ s) (hc : c.i.val < (Algebra.TList.toAnyArray (α := ℝ) w).size) :
    Algebra.TList.toAnyArray (α := ℝ) (Algebra.TList.add (α := ℝ) w (TList.single c u))
      = (Algebra.TList.toAnyArray (α := ℝ) w).set c.i.val
          (mkAny (addSpec (Algebra.TList.get (α := ℝ) w c.i) (Tensor.castShape u c.h.symm)))
          hc := by
  apply Array.ext'
  simp [Algebra.TList.toAnyArray, toAnyList_add_single]

/-- **The sparse accumulate**: one `addGradAll` at slot `c` on an erased context performs the
    one-hot context addition — provided the tape's node at `c` is live and carries the slot's
    shape (which the provenance facts of §E supply). -/
theorem addGradAll_toAnyArray_single {Γ' : List Shape} {s : Shape} (t : RTape)
    (c : Idx Γ' s) (u : Tensor ℝ s) (node : RNode)
    (hn : t.getNode? c.i.val = some node)
    (hrg : node.requires_grad = true)
    (hs : node.value.s = Γ'.get c.i) (w : TList Γ') :
    Runtime.Autograd.Tape.addGradAll (t := t)
        (Algebra.TList.toAnyArray (α := ℝ) w) c.i.val (mkAny u)
      = .ok (Algebra.TList.toAnyArray (α := ℝ)
          (Algebra.TList.add (α := ℝ) w (TList.single c u))) := by
  obtain ⟨i, h⟩ := c
  subst h
  -- expose the node's stored shape as a variable and substitute it away
  obtain ⟨nm, ⟨vs, vt⟩, rg, ps, bk⟩ := node
  have hs' : vs = Γ'.get i := hs
  subst hs'
  have hrg' : rg = true := hrg
  have hlt : i.val < (Algebra.TList.toAnyArray (α := ℝ) w).size := by simp
  have harr : (Algebra.TList.toAnyArray (α := ℝ) w)[i.val]'hlt
      = mkAny (Algebra.TList.get (α := ℝ) w i) := by
    simpa using Algebra.TList.get_toAnyArray (α := ℝ) (ss := Γ') w i
  rw [toAnyArray_add_single (hc := hlt)]
  simp [Runtime.Autograd.Tape.addGradAll, hn, hrg', harr,
    Runtime.Autograd.AnyTensor.add, Runtime.Autograd.AnyTensor.materialize, mkAny,
    Runtime.Autograd.AnyTensor.mk, bind, Except.bind, pure, Except.pure]

/- ===========================================================================================
   §D.  Push-invariance: the reverse pass over an extended tape, on an extended accumulator,
        restricts to the prefix (contribution ids are bounded by the emitting node's id, so the
        pushed last slot is never touched).  This is what lets the main induction (§F) consume
        its hypothesis about the un-extended tapes.
   =========================================================================================== -/

/-- `addNode` pushes the node (the stored value is materialized, which is the identity). -/
theorem addNode_nodes (t : RTape) (nd : RNode) :
    (t.addNode nd).1.nodes = t.nodes.push nd := by
  simp [Runtime.Autograd.Tape.addNode]

/-- `getNode?` on the extended tape, below the old size. -/
theorem getNode?_addNode_lt (t : RTape) (nd : RNode) {i : Nat} (h : i < t.nodes.size) :
    (t.addNode nd).1.getNode? i = t.getNode? i := by
  simp only [Runtime.Autograd.Tape.getNode?, addNode_nodes]
  rw [Array.getElem?_push_lt h, Array.getElem?_eq_getElem h]

/-- `getNode?` on the extended tape, at the old size. -/
theorem getNode?_addNode_size (t : RTape) (nd : RNode) :
    (t.addNode nd).1.getNode? t.nodes.size = some nd := by
  simp only [Runtime.Autograd.Tape.getNode?, addNode_nodes]
  exact Array.getElem?_push_size

/-- Inversion for `getNode?` on the extended tape. -/
theorem getNode?_addNode_cases (t : RTape) (nd : RNode) {i : Nat} {node : RNode}
    (h : (t.addNode nd).1.getNode? i = some node) :
    (i < t.nodes.size ∧ t.getNode? i = some node) ∨ (i = t.nodes.size ∧ node = nd) := by
  by_cases hi : i < t.nodes.size
  · exact Or.inl ⟨hi, by rwa [getNode?_addNode_lt t nd hi] at h⟩
  · have hsize : i < t.nodes.size + 1 := by
      have := lt_of_getNode?_eq_some h
      rwa [addNode_nodes, Array.size_push] at this
    have hieq : i = t.nodes.size := by omega
    subst hieq
    rw [getNode?_addNode_size] at h
    exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩

/-- `throw` in the runtime `Result` monad is `Except.error` (definitional unfolding aid). -/
theorem res_throw_def (msg : String) :
    (throw msg : Runtime.Autograd.Result (Array Any)) = Except.error msg := rfl

/-- One accumulation on the extended tape and extended accumulator restricts to the prefix. -/
theorem addGradAll_push (t : RTape) (nd : RNode) (acc : Array Any) (y : Any)
    (pid : Nat) (pg : Any) (hpid : pid < t.nodes.size) (hacc : acc.size = t.nodes.size) :
    Runtime.Autograd.Tape.addGradAll (t := (t.addNode nd).1) (acc.push y) pid pg
      = (Runtime.Autograd.Tape.addGradAll (t := t) acc pid pg).map (·.push y) := by
  have hnode : t.getNode? pid = some (t.nodes[pid]'hpid) := by
    simp [Runtime.Autograd.Tape.getNode?, Array.getElem?_eq_getElem hpid]
  have hnode' : (t.addNode nd).1.getNode? pid = some (t.nodes[pid]'hpid) := by
    rw [getNode?_addNode_lt t nd hpid]
    exact hnode
  set node := t.nodes[pid]'hpid with hnode_def
  have hpacc : pid < acc.size := by rw [hacc]; exact hpid
  by_cases hreq : node.requires_grad = false
  · simp [Runtime.Autograd.Tape.addGradAll, hnode, hnode', hreq,
      bind, Except.bind, pure, Except.pure, Except.map]
  · have hreq' : node.requires_grad = true := by
      cases hb : node.requires_grad
      · exact absurd hb hreq
      · rfl
    by_cases hshape : pg.s = node.value.s
    · have hgets : (acc.push y)[pid]? = some (acc[pid]'hpacc) := Array.getElem?_push_lt hpacc
      have hget : acc[pid]? = some (acc[pid]'hpacc) := Array.getElem?_eq_getElem hpacc
      have hpushed : (acc.push y)[pid]'(by simpa using Nat.lt_succ_of_lt hpacc)
          = acc[pid]'hpacc := Array.getElem_push_lt hpacc
      by_cases hex : (acc[pid]'hpacc).s = node.value.s
      · obtain ⟨summed, hsummed, _⟩ :=
          anyAdd_ok_of_shape_eq
            ⟨node.value.s, Tensor.castShape (acc[pid]'hpacc).t hex⟩
            ⟨node.value.s, Tensor.castShape pg.t hshape⟩ rfl
        have hset : (acc.push y).set pid summed (by simpa using Nat.lt_succ_of_lt hpacc)
            = (acc.set pid summed hpacc).push y := by
          rw [Array.set_push]
          simp [hpacc]
        simp [Runtime.Autograd.Tape.addGradAll, hnode, hnode', hreq', hshape,
          hpushed, hex, hpacc, Nat.le_of_lt hpacc, hsummed, hset,
          bind, Except.bind, pure, Except.pure, Except.map]
      · simp [Runtime.Autograd.Tape.addGradAll, hnode, hnode', hreq', hshape, hgets, hget,
          hex, bind, Except.bind, pure, Except.pure, Except.map, res_throw_def]
    · simp [Runtime.Autograd.Tape.addGradAll, hnode, hnode', hreq', hshape,
        bind, Except.bind, pure, Except.pure, Except.map, res_throw_def]

/-- Folding bounded contributions on the extended tape restricts to the prefix. -/
theorem foldContribs_push (t : RTape) (nd : RNode) :
    ∀ (cs : List (Nat × Any)) (acc : Array Any) (y : Any),
      acc.size = t.nodes.size →
      (∀ pc ∈ cs, pc.1 < t.nodes.size) →
      cs.foldlM
          (fun acc2 (pid, pg) =>
            Runtime.Autograd.Tape.addGradAll (t := (t.addNode nd).1) acc2 pid pg) (acc.push y)
        = (cs.foldlM
            (fun acc2 (pid, pg) =>
              Runtime.Autograd.Tape.addGradAll (t := t) acc2 pid pg) acc).map
            (fun a : Array Any => a.push y)
  | [], acc, y, _, _ => rfl
  | (pid, pg) :: rest, acc, y, hacc, hbound => by
      have hpid : pid < t.nodes.size := hbound (pid, pg) List.mem_cons_self
      show (Runtime.Autograd.Tape.addGradAll (t := (t.addNode nd).1) (acc.push y) pid pg >>=
          fun init => rest.foldlM (fun acc2 (pid, pg) =>
            Runtime.Autograd.Tape.addGradAll (t := (t.addNode nd).1) acc2 pid pg) init)
        = (Runtime.Autograd.Tape.addGradAll (t := t) acc pid pg >>=
          fun init => rest.foldlM (fun acc2 (pid, pg) =>
            Runtime.Autograd.Tape.addGradAll (t := t) acc2 pid pg) init).map
          (fun a : Array Any => a.push y)
      rw [addGradAll_push t nd acc y pid pg hpid hacc]
      cases hstep : Runtime.Autograd.Tape.addGradAll (t := t) acc pid pg with
      | error e => simp [Except.map, bind, Except.bind]
      | ok acc1 =>
        have hacc1 : acc1.size = t.nodes.size := by
          rw [← hacc]
          exact Algebra.Graph.addGradAll_ok_size (α := ℝ) t hstep
        have hrest := foldContribs_push t nd rest acc1 y hacc1
          (fun q hq => hbound q (List.mem_cons_of_mem _ hq))
        simp only [Except.map, bind, Except.bind]
        exact hrest

/-- One reverse step on the extended tape, below the old size, restricts to the prefix. -/
theorem backwardDenseFromStep_push (t : RTape) (nd : RNode) (id : Nat)
    (hid : id < t.nodes.size) (acc : Array Any) (y : Any) (hacc : acc.size = t.nodes.size)
    (hpids : ∀ node : RNode, t.getNode? id = some node →
      ∀ (dc : Any) (cs : List (Nat × Any)), node.backward dc = .ok cs →
        ∀ pc ∈ cs, pc.1 < t.nodes.size) :
    Runtime.Autograd.Tape.backwardDenseFromStep (t := (t.addNode nd).1) (acc.push y) id
      = (Runtime.Autograd.Tape.backwardDenseFromStep (t := t) acc id).map
          (fun a : Array Any => a.push y) := by
  have hnode : t.getNode? id = some (t.nodes[id]'hid) := by
    simp [Runtime.Autograd.Tape.getNode?, Array.getElem?_eq_getElem hid]
  have hnode' : (t.addNode nd).1.getNode? id = some (t.nodes[id]'hid) := by
    rw [getNode?_addNode_lt t nd hid]
    exact hnode
  set node := t.nodes[id]'hid with hnode_def
  have hid_acc : id < acc.size := by rw [hacc]; exact hid
  by_cases hreq : node.requires_grad = false
  · simp [Runtime.Autograd.Tape.backwardDenseFromStep, hnode, hnode', hreq,
      bind, Except.bind, pure, Except.pure, Except.map]
  · have hreq' : node.requires_grad = true := by
      cases hb : node.requires_grad
      · exact absurd hb hreq
      · rfl
    have hgets : (acc.push y)[id]? = some (acc[id]'hid_acc) := Array.getElem?_push_lt hid_acc
    have hget : acc[id]? = some (acc[id]'hid_acc) := Array.getElem?_eq_getElem hid_acc
    by_cases hshape : (acc[id]'hid_acc).s = node.value.s
    · cases hback : node.backward ⟨node.value.s, Tensor.castShape (acc[id]'hid_acc).t hshape⟩ with
      | error e =>
        simp [Runtime.Autograd.Tape.backwardDenseFromStep, hnode, hnode', hreq', hgets, hget,
          hshape, hback, bind, Except.bind, pure, Except.pure, Except.map]
      | ok cs =>
        have hbound : ∀ pc ∈ cs, pc.1 < t.nodes.size :=
          hpids node hnode _ cs hback
        have hfold := foldContribs_push t nd cs acc y hacc hbound
        simp only [Runtime.Autograd.Tape.backwardDenseFromStep, hnode, hnode', hreq', hgets,
          hget, hshape, hback, bind, Except.bind, pure, Except.pure]
        exact hfold
    · simp [Runtime.Autograd.Tape.backwardDenseFromStep, hnode, hnode', hreq', hgets, hget,
        hshape, bind, Except.bind, pure, Except.pure, Except.map, res_throw_def]

/-- The reverse loop over the first `n` ids of the extended tape restricts to the prefix. -/
theorem backwardDenseFromLoop_push (t : RTape) (nd : RNode)
    (hpids : ∀ (i : Nat) (node : RNode), t.getNode? i = some node →
      ∀ (dc : Any) (cs : List (Nat × Any)), node.backward dc = .ok cs →
        ∀ pc ∈ cs, pc.1 < i) :
    ∀ (n : Nat), n ≤ t.nodes.size → ∀ (acc : Array Any) (y : Any),
      acc.size = t.nodes.size →
      Runtime.Autograd.Tape.backwardDenseFromLoop (t := (t.addNode nd).1) n (acc.push y)
        = (Runtime.Autograd.Tape.backwardDenseFromLoop (t := t) n acc).map
            (fun a : Array Any => a.push y)
  | 0, _, acc, y, _ => rfl
  | n + 1, hn, acc, y, hacc => by
      have hn' : n < t.nodes.size := Nat.lt_of_succ_le hn
      have hstep := backwardDenseFromStep_push t nd n hn' acc y hacc
        (fun node hnode dc cs hback pc hpc =>
          Nat.lt_trans (hpids n node hnode dc cs hback pc hpc) hn')
      show (Runtime.Autograd.Tape.backwardDenseFromStep (t := (t.addNode nd).1) (acc.push y) n
          >>= fun acc' =>
            Runtime.Autograd.Tape.backwardDenseFromLoop (t := (t.addNode nd).1) n acc')
        = _
      rw [hstep]
      cases hs : Runtime.Autograd.Tape.backwardDenseFromStep (t := t) acc n with
      | error e =>
        show (Except.error e >>= fun acc' =>
            Runtime.Autograd.Tape.backwardDenseFromLoop (t := (t.addNode nd).1) n acc')
          = Except.map (fun a : Array Any => a.push y)
              (Runtime.Autograd.Tape.backwardDenseFromLoop (t := t) (n + 1) acc)
        have hexp : Runtime.Autograd.Tape.backwardDenseFromLoop (t := t) (n + 1) acc
            = Except.error e := by
          show (Runtime.Autograd.Tape.backwardDenseFromStep (t := t) acc n >>= fun a =>
            Runtime.Autograd.Tape.backwardDenseFromLoop (t := t) n a) = _
          rw [hs]
          rfl
        rw [hexp]
        rfl
      | ok acc' =>
        have hacc' : acc'.size = t.nodes.size := by
          rw [← hacc]
          exact Algebra.Graph.backwardDenseFromStep_ok_size (α := ℝ) t hs
        have hloop := backwardDenseFromLoop_push t nd hpids n (Nat.le_of_succ_le hn) acc' y hacc'
        simp only [Except.map, bind, Except.bind]
        show Runtime.Autograd.Tape.backwardDenseFromLoop (t := (t.addNode nd).1) n (acc'.push y)
            = _
        rw [hloop]
        have hexp : Runtime.Autograd.Tape.backwardDenseFromLoop (t := t) (n + 1) acc
            = Runtime.Autograd.Tape.backwardDenseFromLoop (t := t) n acc' := by
          show (Runtime.Autograd.Tape.backwardDenseFromStep (t := t) acc n >>= fun a =>
            Runtime.Autograd.Tape.backwardDenseFromLoop (t := t) n a) = _
          rw [hs]
          rfl
        show Except.map (fun a : Array Any => a.push y)
              (Runtime.Autograd.Tape.backwardDenseFromLoop (t := t) n acc')
            = Except.map (fun a : Array Any => a.push y)
                (Runtime.Autograd.Tape.backwardDenseFromLoop (t := t) (n + 1) acc)
        rw [hexp]

/- ===========================================================================================
   §E.  The provenance relation: eager runtime construction of the `leaf`/`add`/`mul` fragment,
        and its forward accounting (sizes, stored values, liveness, bounded contribution ids).
   =========================================================================================== -/

/-- **Eager provenance**: `EagerBuilds g x t` says the runtime tape `t` is what the eager
    constructors build for the P-graph `g` at input `x` — `Tape.leaf` folds for the inputs
    (`addLeaves` *is* that fold), then one `Tape.add`/`Tape.mul` call per graph node. -/
inductive EagerBuilds {Γ : List Shape} : {ss : List Shape} → Graph Γ ss → TList Γ → RTape → Prop
  | nil (x : TList Γ) :
      EagerBuilds .nil x
        (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x)
  | add {ss : List Shape} {τ : Shape} {g : Graph Γ ss} {x : TList Γ} {t t' : RTape} {id : Nat}
      (a b : Idx (Γ ++ ss) τ) (hg : EagerBuilds g x t)
      (hop : Runtime.Autograd.Tape.add (α := ℝ) (s := τ) t a.i.val b.i.val = .ok (t', id)) :
      EagerBuilds (.snoc g (TapeNodes.add a b)) x t'
  | mul {ss : List Shape} {τ : Shape} {g : Graph Γ ss} {x : TList Γ} {t t' : RTape} {id : Nat}
      (a b : Idx (Γ ++ ss) τ) (hg : EagerBuilds g x t)
      (hop : Runtime.Autograd.Tape.mul (α := ℝ) (s := τ) t a.i.val b.i.val = .ok (t', id)) :
      EagerBuilds (.snoc g (TapeNodes.mul a b)) x t'
  | sub {ss : List Shape} {τ : Shape} {g : Graph Γ ss} {x : TList Γ} {t t' : RTape} {id : Nat}
      (a b : Idx (Γ ++ ss) τ) (hg : EagerBuilds g x t)
      (hop : Runtime.Autograd.Tape.sub (α := ℝ) (s := τ) t a.i.val b.i.val = .ok (t', id)) :
      EagerBuilds (.snoc g (TapeNodes.sub a b)) x t'
  | div {ss : List Shape} {τ : Shape} {g : Graph Γ ss} {x : TList Γ} {t t' : RTape} {id : Nat}
      (a b : Idx (Γ ++ ss) τ) (hg : EagerBuilds g x t)
      (hop : Runtime.Autograd.Tape.div (α := ℝ) (s := τ) t a.i.val b.i.val = .ok (t', id)) :
      EagerBuilds (.snoc g (TapeNodes.div a b)) x t'
  | scale {ss : List Shape} {τ : Shape} {g : Graph Γ ss} {x : TList Γ} {t t' : RTape} {id : Nat}
      (idx : Idx (Γ ++ ss) τ) (c : ℝ) (hg : EagerBuilds g x t)
      (hop : Runtime.Autograd.Tape.scale (α := ℝ) (s := τ) t idx.i.val c = .ok (t', id)) :
      EagerBuilds (.snoc g (TapeNodes.scale idx c)) x t'
  | unary {ss : List Shape} {τ : Shape} {g : Graph Γ ss} {x : TList Γ} {t t' : RTape} {id : Nat}
      (idx : Idx (Γ ++ ss) τ) (name : String) (f f' : ℝ → ℝ)
      (fwdSpec bwdSpec : Tensor ℝ τ → Tensor ℝ τ)
      (hfs : ∀ (u : Tensor ℝ τ) (i : Fin (Spec.Shape.size τ)),
          toVecT (t := fwdSpec u) i = f (toVecT (t := u) i))
      (hf's : ∀ (u : Tensor ℝ τ) (i : Fin (Spec.Shape.size τ)),
          toVecT (t := bwdSpec u) i = f' (toVecT (t := u) i))
      (hg : EagerBuilds g x t)
      (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := τ) (τ := τ) t name idx.i.val
          fwdSpec (fun xv d => mulSpec (bwdSpec xv) d) = .ok (t', id)) :
      EagerBuilds (.snoc g (TapeNodes.elemwise idx f f')) x t'

/-- The eager `add` node literal (what `Tape.add` pushes). -/
def eagerAddNode {s : Shape} (aId bId : Nat) (aT bT : Tensor ℝ s) : RNode :=
  { name := some "add", value := Runtime.Autograd.AnyTensor.mk (addSpec aT bT),
    requires_grad := true, parents := [aId, bId],
    backward := fun dLdyAny => do
      let dLdy ← Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := s) dLdyAny
      pure [(aId, Runtime.Autograd.AnyTensor.mk dLdy),
        (bId, Runtime.Autograd.AnyTensor.mk dLdy)] }

/-- The eager `mul` node literal (what `Tape.mul` pushes). -/
def eagerMulNode {s : Shape} (aId bId : Nat) (aT bT : Tensor ℝ s) : RNode :=
  { name := some "mul", value := Runtime.Autograd.AnyTensor.mk (mulSpec aT bT),
    requires_grad := true, parents := [aId, bId],
    backward := fun dLdyAny => do
      let dLdy ← Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := s) dLdyAny
      let da : Tensor ℝ s := mulSpec dLdy bT
      let db : Tensor ℝ s := mulSpec dLdy aT
      pure [(aId, Runtime.Autograd.AnyTensor.mk da),
        (bId, Runtime.Autograd.AnyTensor.mk db)] }

/-- The eager `sub` node literal (what `Tape.sub` pushes — the right parent receives the negated
    cotangent `subSpec (fill 0) dLdy`, mirroring `Engine/Core/Elementwise.lean`). -/
def eagerSubNode {s : Shape} (aId bId : Nat) (aT bT : Tensor ℝ s) : RNode :=
  { name := some "sub", value := Runtime.Autograd.AnyTensor.mk (subSpec aT bT),
    requires_grad := true, parents := [aId, bId],
    backward := fun dLdyAny => do
      let dLdy ← Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := s) dLdyAny
      let neg_dLdy : Tensor ℝ s := subSpec (fill (0 : ℝ) s) dLdy
      pure [(aId, Runtime.Autograd.AnyTensor.mk dLdy),
        (bId, Runtime.Autograd.AnyTensor.mk neg_dLdy)] }

/-- The eager `div` node literal (what `Tape.div` pushes — the left parent receives the quotient
    cotangent `divSpec dLdy bT`, the right parent the negated
    `subSpec (fill 0) (mulSpec dLdy (divSpec aT (mulSpec bT bT)))`, mirroring
    `Engine/Core/Elementwise.lean`). -/
def eagerDivNode {s : Shape} (aId bId : Nat) (aT bT : Tensor ℝ s) : RNode :=
  { name := some "div", value := Runtime.Autograd.AnyTensor.mk (divSpec aT bT),
    requires_grad := true, parents := [aId, bId],
    backward := fun dLdyAny => do
      let dLdy ← Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := s) dLdyAny
      let da : Tensor ℝ s := divSpec dLdy bT
      let dLdyA : Tensor ℝ s := mulSpec dLdy (divSpec aT (mulSpec bT bT))
      let db : Tensor ℝ s := subSpec (fill (0 : ℝ) s) dLdyA
      pure [(aId, Runtime.Autograd.AnyTensor.mk da),
        (bId, Runtime.Autograd.AnyTensor.mk db)] }

/-- The eager `scale` node literal (what `Tape.scale` pushes — one parent, contribution
    `scaleSpec dLdy c`, mirroring `Engine/Core/Elementwise.lean:113`). -/
def eagerScaleNode {s : Shape} (xId : Nat) (c : ℝ) (xT : Tensor ℝ s) : RNode :=
  { name := some "scale", value := Runtime.Autograd.AnyTensor.mk (scaleSpec xT c),
    requires_grad := true, parents := [xId],
    backward := fun dLdyAny => do
      let dLdy ← Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := s) dLdyAny
      pure [(xId, Runtime.Autograd.AnyTensor.mk (scaleSpec dLdy c))] }

/-- Inversion of a successful eager `Tape.add`. -/
theorem tape_add_inv {s : Shape} {t t' : RTape} {aId bId id : Nat}
    (h : Runtime.Autograd.Tape.add (α := ℝ) (s := s) t aId bId = .ok (t', id)) :
    ∃ (aT bT : Tensor ℝ s),
      Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) aId = .ok aT ∧
      Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) bId = .ok bT ∧
      t' = (t.addNode (eagerAddNode aId bId aT bT)).1 := by
  cases hA : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) aId with
  | error e => simp [Runtime.Autograd.Tape.add, hA, bind, Except.bind] at h
  | ok aT =>
  cases hB : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) bId with
  | error e => simp [Runtime.Autograd.Tape.add, hA, hB, bind, Except.bind] at h
  | ok bT =>
  refine ⟨aT, bT, rfl, rfl, ?_⟩
  simp only [Runtime.Autograd.Tape.add, hA, hB, bind, Except.bind, pure, Except.pure] at h
  have hpair := Except.ok.inj h
  exact (congrArg Prod.fst hpair).symm

/-- Inversion of a successful eager `Tape.mul`. -/
theorem tape_mul_inv {s : Shape} {t t' : RTape} {aId bId id : Nat}
    (h : Runtime.Autograd.Tape.mul (α := ℝ) (s := s) t aId bId = .ok (t', id)) :
    ∃ (aT bT : Tensor ℝ s),
      Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) aId = .ok aT ∧
      Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) bId = .ok bT ∧
      t' = (t.addNode (eagerMulNode aId bId aT bT)).1 := by
  cases hA : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) aId with
  | error e => simp [Runtime.Autograd.Tape.mul, hA, bind, Except.bind] at h
  | ok aT =>
  cases hB : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) bId with
  | error e => simp [Runtime.Autograd.Tape.mul, hA, hB, bind, Except.bind] at h
  | ok bT =>
  refine ⟨aT, bT, rfl, rfl, ?_⟩
  simp only [Runtime.Autograd.Tape.mul, hA, hB, bind, Except.bind, pure, Except.pure] at h
  have hpair := Except.ok.inj h
  exact (congrArg Prod.fst hpair).symm

/-- Inversion of a successful eager `Tape.sub`. -/
theorem tape_sub_inv {s : Shape} {t t' : RTape} {aId bId id : Nat}
    (h : Runtime.Autograd.Tape.sub (α := ℝ) (s := s) t aId bId = .ok (t', id)) :
    ∃ (aT bT : Tensor ℝ s),
      Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) aId = .ok aT ∧
      Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) bId = .ok bT ∧
      t' = (t.addNode (eagerSubNode aId bId aT bT)).1 := by
  cases hA : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) aId with
  | error e => simp [Runtime.Autograd.Tape.sub, hA, bind, Except.bind] at h
  | ok aT =>
  cases hB : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) bId with
  | error e => simp [Runtime.Autograd.Tape.sub, hA, hB, bind, Except.bind] at h
  | ok bT =>
  refine ⟨aT, bT, rfl, rfl, ?_⟩
  simp only [Runtime.Autograd.Tape.sub, hA, hB, bind, Except.bind, pure, Except.pure] at h
  have hpair := Except.ok.inj h
  exact (congrArg Prod.fst hpair).symm

/-- Inversion of a successful eager `Tape.div`. -/
theorem tape_div_inv {s : Shape} {t t' : RTape} {aId bId id : Nat}
    (h : Runtime.Autograd.Tape.div (α := ℝ) (s := s) t aId bId = .ok (t', id)) :
    ∃ (aT bT : Tensor ℝ s),
      Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) aId = .ok aT ∧
      Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) bId = .ok bT ∧
      t' = (t.addNode (eagerDivNode aId bId aT bT)).1 := by
  cases hA : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) aId with
  | error e => simp [Runtime.Autograd.Tape.div, hA, bind, Except.bind] at h
  | ok aT =>
  cases hB : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) bId with
  | error e => simp [Runtime.Autograd.Tape.div, hA, hB, bind, Except.bind] at h
  | ok bT =>
  refine ⟨aT, bT, rfl, rfl, ?_⟩
  simp only [Runtime.Autograd.Tape.div, hA, hB, bind, Except.bind, pure, Except.pure] at h
  have hpair := Except.ok.inj h
  exact (congrArg Prod.fst hpair).symm

/-- Inversion of a successful eager `Tape.scale`. -/
theorem tape_scale_inv {s : Shape} {t t' : RTape} {xId id : Nat} {c : ℝ}
    (h : Runtime.Autograd.Tape.scale (α := ℝ) (s := s) t xId c = .ok (t', id)) :
    ∃ (xT : Tensor ℝ s),
      Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) xId = .ok xT ∧
      t' = (t.addNode (eagerScaleNode xId c xT)).1 := by
  cases hX : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) xId with
  | error e => simp [Runtime.Autograd.Tape.scale, hX, bind, Except.bind] at h
  | ok xT =>
  refine ⟨xT, rfl, ?_⟩
  simp only [Runtime.Autograd.Tape.scale, hX, bind, Except.bind, pure, Except.pure] at h
  have hpair := Except.ok.inj h
  exact (congrArg Prod.fst hpair).symm

/-- The eager unary node literal (what `Tape.unary` pushes for the elementwise family — one parent,
    value `fwdSpec xT`, contribution `mulSpec (bwdSpec xT) dLdy`, mirroring `Engine/Core/Core.unary`
    and the inline activations of `ActivationsLoss`). -/
def eagerUnaryNode {s : Shape} (name : String) (xId : Nat)
    (fwdSpec bwdSpec : Tensor ℝ s → Tensor ℝ s) (xT : Tensor ℝ s) : RNode :=
  { name := some name, value := Runtime.Autograd.AnyTensor.mk (fwdSpec xT),
    requires_grad := true, parents := [xId],
    backward := fun dLdyAny => do
      let dLdy ← Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := s) dLdyAny
      pure [(xId, Runtime.Autograd.AnyTensor.mk (mulSpec (bwdSpec xT) dLdy))] }

/-- Inversion of a successful eager `Tape.unary` (elementwise family). -/
theorem tape_unary_inv {s : Shape} {t t' : RTape} {xId id : Nat} {name : String}
    {fwdSpec bwdSpec : Tensor ℝ s → Tensor ℝ s}
    (h : Runtime.Autograd.Tape.unary (α := ℝ) (σ := s) (τ := s) t name xId
        fwdSpec (fun xv d => mulSpec (bwdSpec xv) d) = .ok (t', id)) :
    ∃ (xT : Tensor ℝ s),
      Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) xId = .ok xT ∧
      t' = (t.addNode (eagerUnaryNode name xId fwdSpec bwdSpec xT)).1 := by
  cases hX : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) xId with
  | error e => simp [Runtime.Autograd.Tape.unary, hX, bind, Except.bind] at h
  | ok xT =>
  refine ⟨xT, rfl, ?_⟩
  simp only [Runtime.Autograd.Tape.unary, hX, bind, Except.bind, pure, Except.pure] at h
  have hpair := Except.ok.inj h
  exact (congrArg Prod.fst hpair).symm

/-- A→P evaluation agreement (the `Δ := Unit` slice evaluates as the P graph). -/
theorem eval_toAlgebra {Γ : List Shape} {ss : List Shape} (g : Graph Γ ss) (x : TList Γ) :
    Algebra.Graph.eval (α := ℝ) (Δ := Unit) g.toAlgebra x () = Graph.eval g x := by
  rw [← Algebra.Graph.toReal_eval]
  simp

/-- The eager base tape is the compiled tape of the empty graph. -/
theorem addLeaves_eq_compileAux_nil {Γ : List Shape} (x : TList Γ) :
    Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x
      = (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := [])
          (Graph.toAlgebra .nil) x ()).1 := rfl

/-- Sizes: an eagerly built tape has one node per context slot. -/
theorem eagerBuilds_size {Γ : List Shape} :
    ∀ {ss : List Shape} {g : Graph Γ ss} {x : TList Γ} {t : RTape},
      EagerBuilds g x t → t.nodes.size = (Γ ++ ss).length := by
  intro ss g x t h
  induction h with
  | nil x =>
    simp [Algebra.Graph.size_addLeaves, Runtime.Autograd.Tape.empty]
  | add a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, _, _, ht'⟩ := tape_add_inv hop
    subst ht'
    rw [addNode_nodes, Array.size_push, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  | mul a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, _, _, ht'⟩ := tape_mul_inv hop
    subst ht'
    rw [addNode_nodes, Array.size_push, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  | sub a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, _, _, ht'⟩ := tape_sub_inv hop
    subst ht'
    rw [addNode_nodes, Array.size_push, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  | div a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, _, _, ht'⟩ := tape_div_inv hop
    subst ht'
    rw [addNode_nodes, Array.size_push, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  | scale idx c hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨xT, _, ht'⟩ := tape_scale_inv hop
    subst ht'
    rw [addNode_nodes, Array.size_push, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  | unary idx name f f' fwdSpec bwdSpec hfs hf's hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨xT, _, ht'⟩ := tape_unary_inv hop
    subst ht'
    rw [addNode_nodes, Array.size_push, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- A successful `requireValue`, on a tape whose values erase a context, reads that context. -/
theorem requireValue_eq_of_values {Γ' : List Shape} {s : Shape} {t : RTape} {ctx : TList Γ'}
    (hvals : t.nodes.map (fun node => node.value)
      = Algebra.TList.toAnyArray (α := ℝ) (ss := Γ') ctx)
    (c : Idx Γ' s) {v : Tensor ℝ s}
    (h : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) c.i.val = .ok v) :
    v = getIdx ctx c := by
  have hval : t.getValue? c.i.val = some (mkAny (Algebra.TList.get (α := ℝ) ctx c.i)) := by
    have : t.getValue? c.i.val = (t.nodes.map (fun node => node.value))[c.i.val]? := by
      simp [Runtime.Autograd.Tape.getValue?, Runtime.Autograd.Tape.getNode?,
        Array.getElem?_map]
    rw [this, hvals, toAnyArray_getElem?]
  obtain ⟨i, hidx⟩ := c
  subst hidx
  simp [Runtime.Autograd.Tape.requireValue, hval, mkAny, Runtime.Autograd.AnyTensor.mk] at h
  simp [getIdx]
  exact h.symm

/-- Values: an eagerly built tape stores exactly the erased evaluation context. -/
theorem eagerBuilds_values {Γ : List Shape} :
    ∀ {ss : List Shape} {g : Graph Γ ss} {x : TList Γ} {t : RTape},
      EagerBuilds g x t →
      t.nodes.map (fun node => node.value)
        = Algebra.TList.toAnyArray (α := ℝ) (ss := Γ ++ ss) (Graph.eval g x) := by
  intro ss g x t h
  induction h with
  | nil x =>
    rw [Algebra.Graph.addLeaves_values]
    simp [Runtime.Autograd.Tape.empty, Graph.eval]
  | add a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, hA, hB, ht'⟩ := tape_add_inv hop
    have haT : aT = getIdx (Graph.eval g x) a := requireValue_eq_of_values ih a hA
    have hbT : bT = getIdx (Graph.eval g x) b := requireValue_eq_of_values ih b hB
    subst ht'
    rw [addNode_nodes, Array.map_push, ih]
    show (Algebra.TList.toAnyArray (α := ℝ) (Graph.eval g x)).push
          (Runtime.Autograd.AnyTensor.mk (addSpec aT bT))
        = Algebra.TList.toAnyArray (α := ℝ)
            (Algebra.TList.cast (α := ℝ) (List.append_assoc Γ ss [τ])
              (Algebra.TList.snoc (α := ℝ) (Graph.eval g x)
                ((TapeNodes.add a b).forward (Graph.eval g x))))
    rw [Algebra.TList.toAnyArray_cast, Algebra.TList.toAnyArray_snoc,
      add_forward_eq, haT, hbT]
  | mul a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, hA, hB, ht'⟩ := tape_mul_inv hop
    have haT : aT = getIdx (Graph.eval g x) a := requireValue_eq_of_values ih a hA
    have hbT : bT = getIdx (Graph.eval g x) b := requireValue_eq_of_values ih b hB
    subst ht'
    rw [addNode_nodes, Array.map_push, ih]
    show (Algebra.TList.toAnyArray (α := ℝ) (Graph.eval g x)).push
          (Runtime.Autograd.AnyTensor.mk (mulSpec aT bT))
        = Algebra.TList.toAnyArray (α := ℝ)
            (Algebra.TList.cast (α := ℝ) (List.append_assoc Γ ss [τ])
              (Algebra.TList.snoc (α := ℝ) (Graph.eval g x)
                ((TapeNodes.mul a b).forward (Graph.eval g x))))
    rw [Algebra.TList.toAnyArray_cast, Algebra.TList.toAnyArray_snoc,
      mul_forward_eq, haT, hbT]
  | sub a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, hA, hB, ht'⟩ := tape_sub_inv hop
    have haT : aT = getIdx (Graph.eval g x) a := requireValue_eq_of_values ih a hA
    have hbT : bT = getIdx (Graph.eval g x) b := requireValue_eq_of_values ih b hB
    subst ht'
    rw [addNode_nodes, Array.map_push, ih]
    show (Algebra.TList.toAnyArray (α := ℝ) (Graph.eval g x)).push
          (Runtime.Autograd.AnyTensor.mk (subSpec aT bT))
        = Algebra.TList.toAnyArray (α := ℝ)
            (Algebra.TList.cast (α := ℝ) (List.append_assoc Γ ss [τ])
              (Algebra.TList.snoc (α := ℝ) (Graph.eval g x)
                ((TapeNodes.sub a b).forward (Graph.eval g x))))
    rw [Algebra.TList.toAnyArray_cast, Algebra.TList.toAnyArray_snoc,
      sub_forward_eq, haT, hbT]
  | div a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, hA, hB, ht'⟩ := tape_div_inv hop
    have haT : aT = getIdx (Graph.eval g x) a := requireValue_eq_of_values ih a hA
    have hbT : bT = getIdx (Graph.eval g x) b := requireValue_eq_of_values ih b hB
    subst ht'
    rw [addNode_nodes, Array.map_push, ih]
    show (Algebra.TList.toAnyArray (α := ℝ) (Graph.eval g x)).push
          (Runtime.Autograd.AnyTensor.mk (divSpec aT bT))
        = Algebra.TList.toAnyArray (α := ℝ)
            (Algebra.TList.cast (α := ℝ) (List.append_assoc Γ ss [τ])
              (Algebra.TList.snoc (α := ℝ) (Graph.eval g x)
                ((TapeNodes.div a b).forward (Graph.eval g x))))
    rw [Algebra.TList.toAnyArray_cast, Algebra.TList.toAnyArray_snoc,
      div_forward_eq, haT, hbT]
  | scale idx c hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨xT, hX, ht'⟩ := tape_scale_inv hop
    have hxT : xT = getIdx (Graph.eval g x) idx := requireValue_eq_of_values ih idx hX
    subst ht'
    rw [addNode_nodes, Array.map_push, ih]
    show (Algebra.TList.toAnyArray (α := ℝ) (Graph.eval g x)).push
          (Runtime.Autograd.AnyTensor.mk (scaleSpec xT c))
        = Algebra.TList.toAnyArray (α := ℝ)
            (Algebra.TList.cast (α := ℝ) (List.append_assoc Γ ss [τ])
              (Algebra.TList.snoc (α := ℝ) (Graph.eval g x)
                ((TapeNodes.scale idx c).forward (Graph.eval g x))))
    rw [Algebra.TList.toAnyArray_cast, Algebra.TList.toAnyArray_snoc,
      scale_forward_eq, hxT]
  | unary idx name f f' fwdSpec bwdSpec hfs hf's hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨xT, hX, ht'⟩ := tape_unary_inv hop
    have hxT : xT = getIdx (Graph.eval g x) idx := requireValue_eq_of_values ih idx hX
    subst ht'
    rw [addNode_nodes, Array.map_push, ih]
    show (Algebra.TList.toAnyArray (α := ℝ) (Graph.eval g x)).push
          (Runtime.Autograd.AnyTensor.mk (fwdSpec xT))
        = Algebra.TList.toAnyArray (α := ℝ)
            (Algebra.TList.cast (α := ℝ) (List.append_assoc Γ ss [τ])
              (Algebra.TList.snoc (α := ℝ) (Graph.eval g x)
                ((TapeNodes.elemwise idx f f').forward (Graph.eval g x))))
    rw [Algebra.TList.toAnyArray_cast, Algebra.TList.toAnyArray_snoc,
      elemwise_forward_eq idx f f' fwdSpec hfs, hxT]

/-- Liveness: every node of an eagerly built tape participates in backward. -/
theorem eagerBuilds_rg {Γ : List Shape} :
    ∀ {ss : List Shape} {g : Graph Γ ss} {x : TList Γ} {t : RTape},
      EagerBuilds g x t →
      ∀ (i : Nat) (node : RNode), t.getNode? i = some node → node.requires_grad = true := by
  intro ss g x t h
  induction h with
  | nil x =>
    intro i node hnode
    have hi := lt_of_getNode?_eq_some hnode
    have := Algebra.Graph.compileAux_requires_grad_true (α := ℝ) (Δ := Unit) (Γ := Γ)
      (ss := []) (Graph.toAlgebra .nil) x ()
    rw [addLeaves_eq_compileAux_nil] at hnode hi
    have hval := this i hi
    have : node = (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := [])
        (Graph.toAlgebra .nil) x ()).1.nodes[i]'hi := by
      have hn : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := [])
          (Graph.toAlgebra .nil) x ()).1.getNode? i = some ((Algebra.Graph.compileAux (α := ℝ)
            (Δ := Unit) (Γ := Γ) (ss := []) (Graph.toAlgebra .nil) x ()).1.nodes[i]'hi) := by
        simp [Runtime.Autograd.Tape.getNode?, Array.getElem?_eq_getElem hi]
      rw [hn] at hnode
      exact (Option.some.inj hnode).symm
    rw [this]
    exact hval
  | add a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, _, _, ht'⟩ := tape_add_inv hop
    subst ht'
    intro i node hnode
    rcases getNode?_addNode_cases _ _ hnode with ⟨_, hold⟩ | ⟨_, hnew⟩
    · exact ih i node hold
    · rw [hnew]; rfl
  | mul a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, _, _, ht'⟩ := tape_mul_inv hop
    subst ht'
    intro i node hnode
    rcases getNode?_addNode_cases _ _ hnode with ⟨_, hold⟩ | ⟨_, hnew⟩
    · exact ih i node hold
    · rw [hnew]; rfl
  | sub a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, _, _, ht'⟩ := tape_sub_inv hop
    subst ht'
    intro i node hnode
    rcases getNode?_addNode_cases _ _ hnode with ⟨_, hold⟩ | ⟨_, hnew⟩
    · exact ih i node hold
    · rw [hnew]; rfl
  | div a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, _, _, ht'⟩ := tape_div_inv hop
    subst ht'
    intro i node hnode
    rcases getNode?_addNode_cases _ _ hnode with ⟨_, hold⟩ | ⟨_, hnew⟩
    · exact ih i node hold
    · rw [hnew]; rfl
  | scale idx c hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨xT, _, ht'⟩ := tape_scale_inv hop
    subst ht'
    intro i node hnode
    rcases getNode?_addNode_cases _ _ hnode with ⟨_, hold⟩ | ⟨_, hnew⟩
    · exact ih i node hold
    · rw [hnew]; rfl
  | unary idx name f f' fwdSpec bwdSpec hfs hf's hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨xT, _, ht'⟩ := tape_unary_inv hop
    subst ht'
    intro i node hnode
    rcases getNode?_addNode_cases _ _ hnode with ⟨_, hold⟩ | ⟨_, hnew⟩
    · exact ih i node hold
    · rw [hnew]; rfl

/-- Bounded contributions: every backward closure only targets strictly earlier ids. -/
theorem eagerBuilds_pids {Γ : List Shape} :
    ∀ {ss : List Shape} {g : Graph Γ ss} {x : TList Γ} {t : RTape},
      EagerBuilds g x t →
      ∀ (i : Nat) (node : RNode), t.getNode? i = some node →
        ∀ (dc : Any) (cs : List (Nat × Any)), node.backward dc = .ok cs →
          ∀ pc ∈ cs, pc.1 < i := by
  intro ss g x t h
  induction h with
  | nil x =>
    intro i node hnode dc cs hback pc hpc
    rw [addLeaves_eq_compileAux_nil] at hnode
    exact Algebra.Graph.compileAux_backward_pids_lt_id (α := ℝ) (Δ := Unit) (Γ := Γ)
      (ss := []) (Graph.toAlgebra .nil) x () i node hnode dc cs hback hpc
  | add a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, hA, hB, ht'⟩ := tape_add_inv hop
    have haLt : a.i.val < t.nodes.size := by
      obtain ⟨pa, hpa, _⟩ := requireValue_shape t a.i.val aT hA
      exact lt_of_getNode?_eq_some hpa
    have hbLt : b.i.val < t.nodes.size := by
      obtain ⟨pb, hpb, _⟩ := requireValue_shape t b.i.val bT hB
      exact lt_of_getNode?_eq_some hpb
    subst ht'
    intro i node hnode dc cs hback pc hpc
    rcases getNode?_addNode_cases _ _ hnode with ⟨_, hold⟩ | ⟨hieq, hnew⟩
    · exact ih i node hold dc cs hback pc hpc
    · subst hieq
      subst hnew
      -- the closure emits exactly the two parent ids
      cases hrg : Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := τ) dc with
      | error e =>
        simp [eagerAddNode, hrg, bind, Except.bind] at hback
      | ok dLdy =>
        simp only [eagerAddNode, hrg, bind, Except.bind, pure, Except.pure] at hback
        have hcs : [(a.i.val, Runtime.Autograd.AnyTensor.mk dLdy),
            (b.i.val, Runtime.Autograd.AnyTensor.mk dLdy)] = cs := Except.ok.inj hback
        rw [← hcs] at hpc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
        rcases hpc with rfl | rfl
        · exact haLt
        · exact hbLt
  | mul a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, hA, hB, ht'⟩ := tape_mul_inv hop
    have haLt : a.i.val < t.nodes.size := by
      obtain ⟨pa, hpa, _⟩ := requireValue_shape t a.i.val aT hA
      exact lt_of_getNode?_eq_some hpa
    have hbLt : b.i.val < t.nodes.size := by
      obtain ⟨pb, hpb, _⟩ := requireValue_shape t b.i.val bT hB
      exact lt_of_getNode?_eq_some hpb
    subst ht'
    intro i node hnode dc cs hback pc hpc
    rcases getNode?_addNode_cases _ _ hnode with ⟨_, hold⟩ | ⟨hieq, hnew⟩
    · exact ih i node hold dc cs hback pc hpc
    · subst hieq
      subst hnew
      cases hrg : Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := τ) dc with
      | error e =>
        simp [eagerMulNode, hrg, bind, Except.bind] at hback
      | ok dLdy =>
        simp only [eagerMulNode, hrg, bind, Except.bind, pure, Except.pure] at hback
        have hcs : [(a.i.val, Runtime.Autograd.AnyTensor.mk (mulSpec dLdy bT)),
            (b.i.val, Runtime.Autograd.AnyTensor.mk (mulSpec dLdy aT))] = cs :=
          Except.ok.inj hback
        rw [← hcs] at hpc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
        rcases hpc with rfl | rfl
        · exact haLt
        · exact hbLt
  | sub a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, hA, hB, ht'⟩ := tape_sub_inv hop
    have haLt : a.i.val < t.nodes.size := by
      obtain ⟨pa, hpa, _⟩ := requireValue_shape t a.i.val aT hA
      exact lt_of_getNode?_eq_some hpa
    have hbLt : b.i.val < t.nodes.size := by
      obtain ⟨pb, hpb, _⟩ := requireValue_shape t b.i.val bT hB
      exact lt_of_getNode?_eq_some hpb
    subst ht'
    intro i node hnode dc cs hback pc hpc
    rcases getNode?_addNode_cases _ _ hnode with ⟨_, hold⟩ | ⟨hieq, hnew⟩
    · exact ih i node hold dc cs hback pc hpc
    · subst hieq
      subst hnew
      cases hrg : Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := τ) dc with
      | error e =>
        simp [eagerSubNode, hrg, bind, Except.bind] at hback
      | ok dLdy =>
        simp only [eagerSubNode, hrg, bind, Except.bind, pure, Except.pure] at hback
        have hcs : [(a.i.val, Runtime.Autograd.AnyTensor.mk dLdy),
            (b.i.val, Runtime.Autograd.AnyTensor.mk (subSpec (fill (0 : ℝ) τ) dLdy))] = cs :=
          Except.ok.inj hback
        rw [← hcs] at hpc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
        rcases hpc with rfl | rfl
        · exact haLt
        · exact hbLt
  | div a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, hA, hB, ht'⟩ := tape_div_inv hop
    have haLt : a.i.val < t.nodes.size := by
      obtain ⟨pa, hpa, _⟩ := requireValue_shape t a.i.val aT hA
      exact lt_of_getNode?_eq_some hpa
    have hbLt : b.i.val < t.nodes.size := by
      obtain ⟨pb, hpb, _⟩ := requireValue_shape t b.i.val bT hB
      exact lt_of_getNode?_eq_some hpb
    subst ht'
    intro i node hnode dc cs hback pc hpc
    rcases getNode?_addNode_cases _ _ hnode with ⟨_, hold⟩ | ⟨hieq, hnew⟩
    · exact ih i node hold dc cs hback pc hpc
    · subst hieq
      subst hnew
      cases hrg : Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := τ) dc with
      | error e =>
        simp [eagerDivNode, hrg, bind, Except.bind] at hback
      | ok dLdy =>
        simp only [eagerDivNode, hrg, bind, Except.bind, pure, Except.pure] at hback
        have hcs : [(a.i.val, Runtime.Autograd.AnyTensor.mk (divSpec dLdy bT)),
            (b.i.val, Runtime.Autograd.AnyTensor.mk (subSpec (fill (0 : ℝ) τ)
              (mulSpec dLdy (divSpec aT (mulSpec bT bT)))))] = cs :=
          Except.ok.inj hback
        rw [← hcs] at hpc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
        rcases hpc with rfl | rfl
        · exact haLt
        · exact hbLt
  | scale idx c hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨xT, hX, ht'⟩ := tape_scale_inv hop
    have hxLt : idx.i.val < t.nodes.size := by
      obtain ⟨px, hpx, _⟩ := requireValue_shape t idx.i.val xT hX
      exact lt_of_getNode?_eq_some hpx
    subst ht'
    intro i node hnode dc cs hback pc hpc
    rcases getNode?_addNode_cases _ _ hnode with ⟨_, hold⟩ | ⟨hieq, hnew⟩
    · exact ih i node hold dc cs hback pc hpc
    · subst hieq
      subst hnew
      cases hrg : Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := τ) dc with
      | error e =>
        simp [eagerScaleNode, hrg, bind, Except.bind] at hback
      | ok dLdy =>
        simp only [eagerScaleNode, hrg, bind, Except.bind, pure, Except.pure] at hback
        have hcs : [(idx.i.val, Runtime.Autograd.AnyTensor.mk (scaleSpec dLdy c))] = cs :=
          Except.ok.inj hback
        rw [← hcs] at hpc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
        rcases hpc with rfl
        exact hxLt
  | unary idx name f f' fwdSpec bwdSpec hfs hf's hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨xT, hX, ht'⟩ := tape_unary_inv hop
    have hxLt : idx.i.val < t.nodes.size := by
      obtain ⟨px, hpx, _⟩ := requireValue_shape t idx.i.val xT hX
      exact lt_of_getNode?_eq_some hpx
    subst ht'
    intro i node hnode dc cs hback pc hpc
    rcases getNode?_addNode_cases _ _ hnode with ⟨_, hold⟩ | ⟨hieq, hnew⟩
    · exact ih i node hold dc cs hback pc hpc
    · subst hieq
      subst hnew
      cases hrg : Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := τ) dc with
      | error e =>
        simp [eagerUnaryNode, hrg, bind, Except.bind] at hback
      | ok dLdy =>
        simp only [eagerUnaryNode, hrg, bind, Except.bind, pure, Except.pure] at hback
        have hcs : [(idx.i.val,
            Runtime.Autograd.AnyTensor.mk (mulSpec (bwdSpec xT) dLdy))] = cs :=
          Except.ok.inj hback
        rw [← hcs] at hpc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
        rcases hpc with rfl
        exact hxLt

/- ===========================================================================================
   §F.  The main identification and the transferred endpoints.
   =========================================================================================== -/

/-- Node/value facts from a values-array equation (works for eager and compiled tapes alike). -/
theorem node_facts_of_values {Γ' : List Shape} {t : RTape} {ctx : TList Γ'}
    (hvals : t.nodes.map (fun node => node.value) = Algebra.TList.toAnyArray (α := ℝ) ctx)
    (hsize : t.nodes.size = Γ'.length) (i : Fin Γ'.length) :
    ∃ node : RNode, t.getNode? i.val = some node
      ∧ node.value = mkAny (Algebra.TList.get (α := ℝ) ctx i) := by
  have hi : i.val < t.nodes.size := by rw [hsize]; exact i.isLt
  refine ⟨t.nodes[i.val]'hi, by
    simp [Runtime.Autograd.Tape.getNode?, Array.getElem?_eq_getElem hi], ?_⟩
  have hmap : (t.nodes.map (fun node => node.value))[i.val]?
      = some ((t.nodes[i.val]'hi).value) := by
    simp [Array.getElem?_map, Array.getElem?_eq_getElem hi]
  rw [hvals, toAnyArray_getElem?] at hmap
  exact (Option.some.inj hmap).symm

/-- **Eager = compiled, loop by loop**: the total reverse loop on an eagerly built tape computes
    exactly the loop on the compiled tape, from any erased-context seed. -/
theorem loop_eager_eq_compiled {Γ : List Shape} :
    ∀ {ss : List Shape} {g : Graph Γ ss} {x : TList Γ} {t : RTape},
      EagerBuilds g x t →
      ∀ S : TList (Γ ++ ss),
        Runtime.Autograd.Tape.backwardDenseFromLoop (t := t) ((Γ ++ ss).length)
            (Algebra.TList.toAnyArray (α := ℝ) S)
          = Runtime.Autograd.Tape.backwardDenseFromLoop
              (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                g.toAlgebra x ()).1)
              ((Γ ++ ss).length) (Algebra.TList.toAnyArray (α := ℝ) S) := by
  intro ss g x t h
  induction h with
  | nil x => intro S; rfl
  | mul a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, hA, hB, ht'⟩ := tape_mul_inv hop
    have hsize := eagerBuilds_size hg
    have hvals := eagerBuilds_values hg
    have haT : aT = getIdx (Graph.eval g x) a := requireValue_eq_of_values hvals a hA
    have hbT : bT = getIdx (Graph.eval g x) b := requireValue_eq_of_values hvals b hB
    have haLt : a.i.val < t.nodes.size := by
      obtain ⟨pa, hpa, _⟩ := requireValue_shape t a.i.val aT hA
      exact lt_of_getNode?_eq_some hpa
    have hbLt : b.i.val < t.nodes.size := by
      obtain ⟨pb, hpb, _⟩ := requireValue_shape t b.i.val bT hB
      exact lt_of_getNode?_eq_some hpb
    rw [haT, hbT] at ht'
    subst ht'
    intro S
    -- compiled prefix tape and its facts
    set tc := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
      g.toAlgebra x ()).1 with htc
    have hsize_c : tc.nodes.size = (Γ ++ ss).length := by
      rw [htc, Algebra.Graph.compileAux_nodes_size]
      simp
    have hctxc : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
        g.toAlgebra x ()).2 = Graph.eval g x := by
      rw [Algebra.Graph.compileAux_ctx_eq_eval, eval_toAlgebra]
    have hvals_c : tc.nodes.map (fun node => node.value)
        = Algebra.TList.toAnyArray (α := ℝ) (Graph.eval g x) := by
      rw [htc, Algebra.Graph.compileAux_values_eq, hctxc]
    -- the compiled snoc tape is `tc` extended with the compiled node
    have hcomp : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.mul a b)).toAlgebra x ()).1
      = (tc.addNode
          { name := some "proof-compiled"
            value := Runtime.Autograd.AnyTensor.mk
              (((TapeNodes.mul a b).toAlgebra).forward
                ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                  g.toAlgebra x ()).2) ())
            requires_grad := true
            parents := []
            backward := fun dLdyAny =>
              if hsh : dLdyAny.s = τ then
                .ok (Algebra.TList.toIndexedAnyList (α := ℝ) (ss := Γ ++ ss)
                  (((TapeNodes.mul a b).toAlgebra).vjp
                    ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                      g.toAlgebra x ()).2) ()
                    (Tensor.castShape dLdyAny.t hsh)) 0)
              else .error "autograd: upstream gradient shape mismatch" }).1 := rfl
    -- seed decomposition: S = snoc u y (after reassociation)
    set S' := Algebra.TList.cast (α := ℝ) (List.append_assoc Γ ss [τ]).symm S with hS'def
    have hSS : Algebra.TList.toAnyArray (α := ℝ) S = Algebra.TList.toAnyArray (α := ℝ) S' := by
      rw [hS'def, Algebra.TList.toAnyArray_cast]
    obtain ⟨u, y, huy⟩ : ∃ (u : TList (Γ ++ ss)) (y : Tensor ℝ τ),
        S' = Algebra.TList.snoc (α := ℝ) u y :=
      ⟨(Algebra.TList.unsnoc S').1, (Algebra.TList.unsnoc S').2,
        (Algebra.TList.snoc_unsnoc (α := ℝ) (xs := S')).symm⟩
    have harr : Algebra.TList.toAnyArray (α := ℝ) S
        = (Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y) := by
      rw [hSS, huy, Algebra.TList.toAnyArray_snoc]
    have husize : (Algebra.TList.toAnyArray (α := ℝ) u).size = (Γ ++ ss).length := by simp
    -- target node facts at the two parents (for the sparse accumulate)
    obtain ⟨na, hna, hna_val⟩ := node_facts_of_values hvals hsize a.i
    obtain ⟨nb, hnb, hnb_val⟩ := node_facts_of_values hvals hsize b.i
    have hna_rg : na.requires_grad = true := eagerBuilds_rg hg a.i.val na hna
    have hnb_rg : nb.requires_grad = true := eagerBuilds_rg hg b.i.val nb hnb
    have hna_s : na.value.s = (Γ ++ ss).get a.i := by rw [hna_val]; rfl
    have hnb_s : nb.value.s = (Γ ++ ss).get b.i := by rw [hnb_val]; rfl
    -- the two-element eager fold = the double one-hot accumulation
    have hfold2 :
        [(a.i.val, mkAny (mulSpec y (getIdx (Graph.eval g x) b))), (b.i.val, mkAny (mulSpec y (getIdx (Graph.eval g x) a)))].foldlM
            (fun acc2 (pid, pg) => Runtime.Autograd.Tape.addGradAll (t := t) acc2 pid pg)
            (Algebra.TList.toAnyArray (α := ℝ) u)
          = .ok (Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ)
                (Algebra.TList.add (α := ℝ) u (TList.single a (mulSpec y (getIdx (Graph.eval g x) b))))
                (TList.single b (mulSpec y (getIdx (Graph.eval g x) a))))) := by
      show (Runtime.Autograd.Tape.addGradAll (t := t)
            (Algebra.TList.toAnyArray (α := ℝ) u) a.i.val (mkAny (mulSpec y (getIdx (Graph.eval g x) b))) >>= fun a1 =>
          (Runtime.Autograd.Tape.addGradAll (t := t) a1 b.i.val (mkAny (mulSpec y (getIdx (Graph.eval g x) a)))
            >>= fun a2 => pure a2))
        = _
      rw [addGradAll_toAnyArray_single t a (mulSpec y (getIdx (Graph.eval g x) b)) na hna hna_rg hna_s u]
      show (Runtime.Autograd.Tape.addGradAll (t := t)
            (Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ) u (TList.single a (mulSpec y (getIdx (Graph.eval g x) b)))))
            b.i.val (mkAny (mulSpec y (getIdx (Graph.eval g x) a))) >>= fun a2 => pure a2)
        = _
      rw [addGradAll_toAnyArray_single t b (mulSpec y (getIdx (Graph.eval g x) a)) nb hnb hnb_rg hnb_s
        (Algebra.TList.add (α := ℝ) u (TList.single a (mulSpec y (getIdx (Graph.eval g x) b))))]
      rfl
    -- eager step at the last id
    have hnodeN : (t.addNode (eagerMulNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1.getNode?
        ((Γ ++ ss).length) = some (eagerMulNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b)) := by
      have h := getNode?_addNode_size t (eagerMulNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))
      rwa [hsize] at h
    have hgetsN : ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y))[(Γ ++ ss).length]?
        = some (mkAny y) := by
      have h := Array.getElem?_push_size (xs := Algebra.TList.toAnyArray (α := ℝ) u)
        (x := mkAny y)
      rwa [husize] at h
    have hstep_e : Runtime.Autograd.Tape.backwardDenseFromStep
        (t := (t.addNode (eagerMulNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1)
        ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
      = .ok ((Algebra.TList.toAnyArray (α := ℝ)
          (Algebra.TList.add (α := ℝ) u
            ((TapeNodes.mul (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))).push
          (mkAny y)) := by
      have hfold2' := hfold2
      rw [mul_vjp_add_eq] at hfold2'
      have hpush := foldContribs_push t (eagerMulNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))
        [(a.i.val, mkAny (mulSpec y (getIdx (Graph.eval g x) b))), (b.i.val, mkAny (mulSpec y (getIdx (Graph.eval g x) a)))]
        (Algebra.TList.toAnyArray (α := ℝ) u) (mkAny y) (by rw [husize, hsize])
        (by
          intro pc hpc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
          rcases hpc with rfl | rfl
          · exact haLt
          · exact hbLt)
      rw [hfold2'] at hpush
      have hrgY : Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := τ) ⟨τ, y⟩ = .ok y := by
        simp [Runtime.Autograd.Tape.requireGrad]
      simp only [Runtime.Autograd.Tape.backwardDenseFromStep, hnodeN, hgetsN,
        bind, Except.bind, pure, Except.pure]
      simpa [eagerMulNode, mkAny, Runtime.Autograd.AnyTensor.mk, hrgY,
        List.foldlM_cons, List.foldlM_nil, bind, Except.bind, pure, Except.pure,
        Except.map] using hpush
    -- compiled step at the last id
    have hnodeN_c : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.mul a b)).toAlgebra x ()).1.getNode? ((Γ ++ ss).length)
      = some { name := some "proof-compiled"
               value := Runtime.Autograd.AnyTensor.mk
                 (((TapeNodes.mul a b).toAlgebra).forward
                   ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                     g.toAlgebra x ()).2) ())
               requires_grad := true
               parents := []
               backward := fun dLdyAny =>
                 if hsh : dLdyAny.s = τ then
                   .ok (Algebra.TList.toIndexedAnyList (α := ℝ) (ss := Γ ++ ss)
                     (((TapeNodes.mul a b).toAlgebra).vjp
                       ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                         g.toAlgebra x ()).2) ()
                       (Tensor.castShape dLdyAny.t hsh)) 0)
                 else .error "autograd: upstream gradient shape mismatch" } := by
      rw [hcomp, ← hsize_c]
      exact getNode?_addNode_size tc _
    have hupstream := Algebra.Graph.foldlM_addGradAll_toIndexedAnyList_eq_add (α := ℝ)
      (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.mul a b)).toAlgebra x ()).1
      (ss := Γ ++ ss) #[] u
      ((TapeNodes.mul (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y)
      #[(mkAny y : Any)]
      (by
        intro i hi
        obtain ⟨node, hnode, hval⟩ :=
          node_facts_of_values hvals_c hsize_c ⟨i, hi⟩
        have hlt : i < tc.nodes.size := by rw [hsize_c]; exact hi
        refine ⟨node, ?_, ?_, ?_⟩
        · rw [hcomp]
          show (tc.addNode _).1.getNode? (#[].size + i) = some node
          simpa using (getNode?_addNode_lt tc _ hlt).trans hnode
        · -- all compiled nodes are live
          have := Algebra.Graph.compileAux_requires_grad_true (α := ℝ) (Δ := Unit)
            (Γ := Γ) (ss := ss) g.toAlgebra x ()
          have hnode' : tc.getNode? i = some (tc.nodes[i]'hlt) := by
            simp [Runtime.Autograd.Tape.getNode?, Array.getElem?_eq_getElem hlt]
          rw [hnode'] at hnode
          rw [(Option.some.inj hnode).symm]
          exact this i hlt
        · rw [hval]
          have he : (Algebra.TList.toAnyArray (α := ℝ) u)[i]'(by simpa using hi)
              = mkAny (Algebra.TList.get (α := ℝ) u ⟨i, hi⟩) := by
            simpa using Algebra.TList.get_toAnyArray (α := ℝ) (ss := Γ ++ ss) u ⟨i, hi⟩
          rw [he]
          rfl)
    have hstep_c : Runtime.Autograd.Tape.backwardDenseFromStep
        (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
          (Graph.snoc g (TapeNodes.mul a b)).toAlgebra x ()).1)
        ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
      = .ok ((Algebra.TList.toAnyArray (α := ℝ)
          (Algebra.TList.add (α := ℝ) u
            ((TapeNodes.mul (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))).push
          (mkAny y)) := by
      have hpre : (Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)
          = #[] ++ Algebra.TList.toAnyArray (α := ℝ) u ++ #[(mkAny y : Any)] := by
        simp
      have hpost : (Algebra.TList.toAnyArray (α := ℝ)
            (Algebra.TList.add (α := ℝ) u
              ((TapeNodes.mul (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))).push
            (mkAny y)
          = #[] ++ Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ) u
                ((TapeNodes.mul (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))
              ++ #[(mkAny y : Any)] := by
        simp
      simp only [Runtime.Autograd.Tape.backwardDenseFromStep, hnodeN_c, hgetsN,
        bind, Except.bind, pure, Except.pure]
      rw [hpre, hpost]
      have harg : ((TapeNodes.mul a b).toAlgebra).vjp
          ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
            g.toAlgebra x ()).2) () y
        = (TapeNodes.mul (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y := by
        rw [hctxc]
        rfl
      simpa [mkAny, Runtime.Autograd.AnyTensor.mk, harg] using hupstream
    -- assemble: unfold both loops one step and use the push-invariance + IH
    have hN' : (Γ ++ (ss ++ [τ])).length = (Γ ++ ss).length + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [harr, hN']
    show (Runtime.Autograd.Tape.backwardDenseFromStep
          (t := (t.addNode (eagerMulNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1)
          ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
        >>= fun acc' => Runtime.Autograd.Tape.backwardDenseFromLoop
          (t := (t.addNode (eagerMulNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1)
          ((Γ ++ ss).length) acc')
      = (Runtime.Autograd.Tape.backwardDenseFromStep
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
            (Graph.snoc g (TapeNodes.mul a b)).toAlgebra x ()).1)
          ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
        >>= fun acc' => Runtime.Autograd.Tape.backwardDenseFromLoop
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
            (Graph.snoc g (TapeNodes.mul a b)).toAlgebra x ()).1)
          ((Γ ++ ss).length) acc')
    rw [hstep_e, hstep_c]
    show Runtime.Autograd.Tape.backwardDenseFromLoop
        (t := (t.addNode (eagerMulNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1) ((Γ ++ ss).length) _
      = Runtime.Autograd.Tape.backwardDenseFromLoop
        (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
          (Graph.snoc g (TapeNodes.mul a b)).toAlgebra x ()).1) ((Γ ++ ss).length) _
    rw [hcomp]
    rw [backwardDenseFromLoop_push t _ (eagerBuilds_pids hg) ((Γ ++ ss).length)
      (by rw [hsize]) _ (mkAny y) (by simp [hsize]),
      backwardDenseFromLoop_push tc _
        (fun i node hnode dc cs hback pc hpc =>
          Algebra.Graph.compileAux_backward_pids_lt_id (α := ℝ) (Δ := Unit) (Γ := Γ)
            (ss := ss) g.toAlgebra x () i node hnode dc cs hback hpc)
        ((Γ ++ ss).length) (by rw [hsize_c]) _ (mkAny y) (by simp [hsize_c])]
    rw [ih]
  | add a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, hA, hB, ht'⟩ := tape_add_inv hop
    have hsize := eagerBuilds_size hg
    have hvals := eagerBuilds_values hg
    have haT : aT = getIdx (Graph.eval g x) a := requireValue_eq_of_values hvals a hA
    have hbT : bT = getIdx (Graph.eval g x) b := requireValue_eq_of_values hvals b hB
    have haLt : a.i.val < t.nodes.size := by
      obtain ⟨pa, hpa, _⟩ := requireValue_shape t a.i.val aT hA
      exact lt_of_getNode?_eq_some hpa
    have hbLt : b.i.val < t.nodes.size := by
      obtain ⟨pb, hpb, _⟩ := requireValue_shape t b.i.val bT hB
      exact lt_of_getNode?_eq_some hpb
    rw [haT, hbT] at ht'
    subst ht'
    intro S
    set tc := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
      g.toAlgebra x ()).1 with htc
    have hsize_c : tc.nodes.size = (Γ ++ ss).length := by
      rw [htc, Algebra.Graph.compileAux_nodes_size]
      simp
    have hctxc : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
        g.toAlgebra x ()).2 = Graph.eval g x := by
      rw [Algebra.Graph.compileAux_ctx_eq_eval, eval_toAlgebra]
    have hvals_c : tc.nodes.map (fun node => node.value)
        = Algebra.TList.toAnyArray (α := ℝ) (Graph.eval g x) := by
      rw [htc, Algebra.Graph.compileAux_values_eq, hctxc]
    have hcomp : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.add a b)).toAlgebra x ()).1
      = (tc.addNode
          { name := some "proof-compiled"
            value := Runtime.Autograd.AnyTensor.mk
              (((TapeNodes.add a b).toAlgebra).forward
                ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                  g.toAlgebra x ()).2) ())
            requires_grad := true
            parents := []
            backward := fun dLdyAny =>
              if hsh : dLdyAny.s = τ then
                .ok (Algebra.TList.toIndexedAnyList (α := ℝ) (ss := Γ ++ ss)
                  (((TapeNodes.add a b).toAlgebra).vjp
                    ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                      g.toAlgebra x ()).2) ()
                    (Tensor.castShape dLdyAny.t hsh)) 0)
              else .error "autograd: upstream gradient shape mismatch" }).1 := rfl
    set S' := Algebra.TList.cast (α := ℝ) (List.append_assoc Γ ss [τ]).symm S with hS'def
    have hSS : Algebra.TList.toAnyArray (α := ℝ) S = Algebra.TList.toAnyArray (α := ℝ) S' := by
      rw [hS'def, Algebra.TList.toAnyArray_cast]
    obtain ⟨u, y, huy⟩ : ∃ (u : TList (Γ ++ ss)) (y : Tensor ℝ τ),
        S' = Algebra.TList.snoc (α := ℝ) u y :=
      ⟨(Algebra.TList.unsnoc S').1, (Algebra.TList.unsnoc S').2,
        (Algebra.TList.snoc_unsnoc (α := ℝ) (xs := S')).symm⟩
    have harr : Algebra.TList.toAnyArray (α := ℝ) S
        = (Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y) := by
      rw [hSS, huy, Algebra.TList.toAnyArray_snoc]
    have husize : (Algebra.TList.toAnyArray (α := ℝ) u).size = (Γ ++ ss).length := by simp
    obtain ⟨na, hna, hna_val⟩ := node_facts_of_values hvals hsize a.i
    obtain ⟨nb, hnb, hnb_val⟩ := node_facts_of_values hvals hsize b.i
    have hna_rg : na.requires_grad = true := eagerBuilds_rg hg a.i.val na hna
    have hnb_rg : nb.requires_grad = true := eagerBuilds_rg hg b.i.val nb hnb
    have hna_s : na.value.s = (Γ ++ ss).get a.i := by rw [hna_val]; rfl
    have hnb_s : nb.value.s = (Γ ++ ss).get b.i := by rw [hnb_val]; rfl
    have hfold2 :
        [(a.i.val, mkAny y), (b.i.val, mkAny y)].foldlM
            (fun acc2 (pid, pg) => Runtime.Autograd.Tape.addGradAll (t := t) acc2 pid pg)
            (Algebra.TList.toAnyArray (α := ℝ) u)
          = .ok (Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ)
                (Algebra.TList.add (α := ℝ) u (TList.single a y))
                (TList.single b y))) := by
      show (Runtime.Autograd.Tape.addGradAll (t := t)
            (Algebra.TList.toAnyArray (α := ℝ) u) a.i.val (mkAny y) >>= fun a1 =>
          (Runtime.Autograd.Tape.addGradAll (t := t) a1 b.i.val (mkAny y)
            >>= fun a2 => pure a2))
        = _
      rw [addGradAll_toAnyArray_single t a y na hna hna_rg hna_s u]
      show (Runtime.Autograd.Tape.addGradAll (t := t)
            (Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ) u (TList.single a y)))
            b.i.val (mkAny y) >>= fun a2 => pure a2)
        = _
      rw [addGradAll_toAnyArray_single t b y nb hnb hnb_rg hnb_s
        (Algebra.TList.add (α := ℝ) u (TList.single a y))]
      rfl
    have hnodeN : (t.addNode (eagerAddNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1.getNode?
        ((Γ ++ ss).length) = some (eagerAddNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b)) := by
      have h := getNode?_addNode_size t (eagerAddNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))
      rwa [hsize] at h
    have hgetsN : ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y))[(Γ ++ ss).length]?
        = some (mkAny y) := by
      have h := Array.getElem?_push_size (xs := Algebra.TList.toAnyArray (α := ℝ) u)
        (x := mkAny y)
      rwa [husize] at h
    have hstep_e : Runtime.Autograd.Tape.backwardDenseFromStep
        (t := (t.addNode (eagerAddNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1)
        ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
      = .ok ((Algebra.TList.toAnyArray (α := ℝ)
          (Algebra.TList.add (α := ℝ) u
            ((TapeNodes.add (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))).push
          (mkAny y)) := by
      have hfold2' := hfold2
      rw [add_vjp_add_eq] at hfold2'
      have hpush := foldContribs_push t (eagerAddNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))
        [(a.i.val, mkAny y), (b.i.val, mkAny y)]
        (Algebra.TList.toAnyArray (α := ℝ) u) (mkAny y) (by rw [husize, hsize])
        (by
          intro pc hpc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
          rcases hpc with rfl | rfl
          · exact haLt
          · exact hbLt)
      rw [hfold2'] at hpush
      have hrgY : Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := τ) ⟨τ, y⟩ = .ok y := by
        simp [Runtime.Autograd.Tape.requireGrad]
      simp only [Runtime.Autograd.Tape.backwardDenseFromStep, hnodeN, hgetsN,
        bind, Except.bind, pure, Except.pure]
      simpa [eagerAddNode, mkAny, Runtime.Autograd.AnyTensor.mk, hrgY,
        List.foldlM_cons, List.foldlM_nil, bind, Except.bind, pure, Except.pure,
        Except.map] using hpush
    have hnodeN_c : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.add a b)).toAlgebra x ()).1.getNode? ((Γ ++ ss).length)
      = some { name := some "proof-compiled"
               value := Runtime.Autograd.AnyTensor.mk
                 (((TapeNodes.add a b).toAlgebra).forward
                   ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                     g.toAlgebra x ()).2) ())
               requires_grad := true
               parents := []
               backward := fun dLdyAny =>
                 if hsh : dLdyAny.s = τ then
                   .ok (Algebra.TList.toIndexedAnyList (α := ℝ) (ss := Γ ++ ss)
                     (((TapeNodes.add a b).toAlgebra).vjp
                       ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                         g.toAlgebra x ()).2) ()
                       (Tensor.castShape dLdyAny.t hsh)) 0)
                 else .error "autograd: upstream gradient shape mismatch" } := by
      rw [hcomp, ← hsize_c]
      exact getNode?_addNode_size tc _
    have hupstream := Algebra.Graph.foldlM_addGradAll_toIndexedAnyList_eq_add (α := ℝ)
      (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.add a b)).toAlgebra x ()).1
      (ss := Γ ++ ss) #[] u
      ((TapeNodes.add (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y)
      #[(mkAny y : Any)]
      (by
        intro i hi
        obtain ⟨node, hnode, hval⟩ :=
          node_facts_of_values hvals_c hsize_c ⟨i, hi⟩
        have hlt : i < tc.nodes.size := by rw [hsize_c]; exact hi
        refine ⟨node, ?_, ?_, ?_⟩
        · rw [hcomp]
          show (tc.addNode _).1.getNode? (#[].size + i) = some node
          simpa using (getNode?_addNode_lt tc _ hlt).trans hnode
        · have := Algebra.Graph.compileAux_requires_grad_true (α := ℝ) (Δ := Unit)
            (Γ := Γ) (ss := ss) g.toAlgebra x ()
          have hnode' : tc.getNode? i = some (tc.nodes[i]'hlt) := by
            simp [Runtime.Autograd.Tape.getNode?, Array.getElem?_eq_getElem hlt]
          rw [hnode'] at hnode
          rw [(Option.some.inj hnode).symm]
          exact this i hlt
        · rw [hval]
          have he : (Algebra.TList.toAnyArray (α := ℝ) u)[i]'(by simpa using hi)
              = mkAny (Algebra.TList.get (α := ℝ) u ⟨i, hi⟩) := by
            simpa using Algebra.TList.get_toAnyArray (α := ℝ) (ss := Γ ++ ss) u ⟨i, hi⟩
          rw [he]
          rfl)
    have hstep_c : Runtime.Autograd.Tape.backwardDenseFromStep
        (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
          (Graph.snoc g (TapeNodes.add a b)).toAlgebra x ()).1)
        ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
      = .ok ((Algebra.TList.toAnyArray (α := ℝ)
          (Algebra.TList.add (α := ℝ) u
            ((TapeNodes.add (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))).push
          (mkAny y)) := by
      have hpre : (Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)
          = #[] ++ Algebra.TList.toAnyArray (α := ℝ) u ++ #[(mkAny y : Any)] := by
        simp
      have hpost : (Algebra.TList.toAnyArray (α := ℝ)
            (Algebra.TList.add (α := ℝ) u
              ((TapeNodes.add (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))).push
            (mkAny y)
          = #[] ++ Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ) u
                ((TapeNodes.add (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))
              ++ #[(mkAny y : Any)] := by
        simp
      simp only [Runtime.Autograd.Tape.backwardDenseFromStep, hnodeN_c, hgetsN,
        bind, Except.bind, pure, Except.pure]
      rw [hpre, hpost]
      have harg : ((TapeNodes.add a b).toAlgebra).vjp
          ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
            g.toAlgebra x ()).2) () y
        = (TapeNodes.add (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y := by
        rw [hctxc]
        rfl
      simpa [mkAny, Runtime.Autograd.AnyTensor.mk, harg] using hupstream
    have hN' : (Γ ++ (ss ++ [τ])).length = (Γ ++ ss).length + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [harr, hN']
    show (Runtime.Autograd.Tape.backwardDenseFromStep
          (t := (t.addNode (eagerAddNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1)
          ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
        >>= fun acc' => Runtime.Autograd.Tape.backwardDenseFromLoop
          (t := (t.addNode (eagerAddNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1)
          ((Γ ++ ss).length) acc')
      = (Runtime.Autograd.Tape.backwardDenseFromStep
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
            (Graph.snoc g (TapeNodes.add a b)).toAlgebra x ()).1)
          ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
        >>= fun acc' => Runtime.Autograd.Tape.backwardDenseFromLoop
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
            (Graph.snoc g (TapeNodes.add a b)).toAlgebra x ()).1)
          ((Γ ++ ss).length) acc')
    rw [hstep_e, hstep_c]
    show Runtime.Autograd.Tape.backwardDenseFromLoop
        (t := (t.addNode (eagerAddNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1) ((Γ ++ ss).length) _
      = Runtime.Autograd.Tape.backwardDenseFromLoop
        (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
          (Graph.snoc g (TapeNodes.add a b)).toAlgebra x ()).1) ((Γ ++ ss).length) _
    rw [hcomp]
    rw [backwardDenseFromLoop_push t _ (eagerBuilds_pids hg) ((Γ ++ ss).length)
      (by rw [hsize]) _ (mkAny y) (by simp [hsize]),
      backwardDenseFromLoop_push tc _
        (fun i node hnode dc cs hback pc hpc =>
          Algebra.Graph.compileAux_backward_pids_lt_id (α := ℝ) (Δ := Unit) (Γ := Γ)
            (ss := ss) g.toAlgebra x () i node hnode dc cs hback hpc)
        ((Γ ++ ss).length) (by rw [hsize_c]) _ (mkAny y) (by simp [hsize_c])]
    rw [ih]
  | sub a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, hA, hB, ht'⟩ := tape_sub_inv hop
    have hsize := eagerBuilds_size hg
    have hvals := eagerBuilds_values hg
    have haT : aT = getIdx (Graph.eval g x) a := requireValue_eq_of_values hvals a hA
    have hbT : bT = getIdx (Graph.eval g x) b := requireValue_eq_of_values hvals b hB
    have haLt : a.i.val < t.nodes.size := by
      obtain ⟨pa, hpa, _⟩ := requireValue_shape t a.i.val aT hA
      exact lt_of_getNode?_eq_some hpa
    have hbLt : b.i.val < t.nodes.size := by
      obtain ⟨pb, hpb, _⟩ := requireValue_shape t b.i.val bT hB
      exact lt_of_getNode?_eq_some hpb
    rw [haT, hbT] at ht'
    subst ht'
    intro S
    set tc := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
      g.toAlgebra x ()).1 with htc
    have hsize_c : tc.nodes.size = (Γ ++ ss).length := by
      rw [htc, Algebra.Graph.compileAux_nodes_size]
      simp
    have hctxc : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
        g.toAlgebra x ()).2 = Graph.eval g x := by
      rw [Algebra.Graph.compileAux_ctx_eq_eval, eval_toAlgebra]
    have hvals_c : tc.nodes.map (fun node => node.value)
        = Algebra.TList.toAnyArray (α := ℝ) (Graph.eval g x) := by
      rw [htc, Algebra.Graph.compileAux_values_eq, hctxc]
    have hcomp : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.sub a b)).toAlgebra x ()).1
      = (tc.addNode
          { name := some "proof-compiled"
            value := Runtime.Autograd.AnyTensor.mk
              (((TapeNodes.sub a b).toAlgebra).forward
                ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                  g.toAlgebra x ()).2) ())
            requires_grad := true
            parents := []
            backward := fun dLdyAny =>
              if hsh : dLdyAny.s = τ then
                .ok (Algebra.TList.toIndexedAnyList (α := ℝ) (ss := Γ ++ ss)
                  (((TapeNodes.sub a b).toAlgebra).vjp
                    ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                      g.toAlgebra x ()).2) ()
                    (Tensor.castShape dLdyAny.t hsh)) 0)
              else .error "autograd: upstream gradient shape mismatch" }).1 := rfl
    set S' := Algebra.TList.cast (α := ℝ) (List.append_assoc Γ ss [τ]).symm S with hS'def
    have hSS : Algebra.TList.toAnyArray (α := ℝ) S = Algebra.TList.toAnyArray (α := ℝ) S' := by
      rw [hS'def, Algebra.TList.toAnyArray_cast]
    obtain ⟨u, y, huy⟩ : ∃ (u : TList (Γ ++ ss)) (y : Tensor ℝ τ),
        S' = Algebra.TList.snoc (α := ℝ) u y :=
      ⟨(Algebra.TList.unsnoc S').1, (Algebra.TList.unsnoc S').2,
        (Algebra.TList.snoc_unsnoc (α := ℝ) (xs := S')).symm⟩
    have harr : Algebra.TList.toAnyArray (α := ℝ) S
        = (Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y) := by
      rw [hSS, huy, Algebra.TList.toAnyArray_snoc]
    have husize : (Algebra.TList.toAnyArray (α := ℝ) u).size = (Γ ++ ss).length := by simp
    obtain ⟨na, hna, hna_val⟩ := node_facts_of_values hvals hsize a.i
    obtain ⟨nb, hnb, hnb_val⟩ := node_facts_of_values hvals hsize b.i
    have hna_rg : na.requires_grad = true := eagerBuilds_rg hg a.i.val na hna
    have hnb_rg : nb.requires_grad = true := eagerBuilds_rg hg b.i.val nb hnb
    have hna_s : na.value.s = (Γ ++ ss).get a.i := by rw [hna_val]; rfl
    have hnb_s : nb.value.s = (Γ ++ ss).get b.i := by rw [hnb_val]; rfl
    have hfold2 :
        [(a.i.val, mkAny y), (b.i.val, mkAny (subSpec (fill (0 : ℝ) τ) y))].foldlM
            (fun acc2 (pid, pg) => Runtime.Autograd.Tape.addGradAll (t := t) acc2 pid pg)
            (Algebra.TList.toAnyArray (α := ℝ) u)
          = .ok (Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ)
                (Algebra.TList.add (α := ℝ) u (TList.single a y))
                (TList.single b (subSpec (fill (0 : ℝ) τ) y)))) := by
      show (Runtime.Autograd.Tape.addGradAll (t := t)
            (Algebra.TList.toAnyArray (α := ℝ) u) a.i.val (mkAny y) >>= fun a1 =>
          (Runtime.Autograd.Tape.addGradAll (t := t) a1 b.i.val (mkAny (subSpec (fill (0 : ℝ) τ) y))
            >>= fun a2 => pure a2))
        = _
      rw [addGradAll_toAnyArray_single t a y na hna hna_rg hna_s u]
      show (Runtime.Autograd.Tape.addGradAll (t := t)
            (Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ) u (TList.single a y)))
            b.i.val (mkAny (subSpec (fill (0 : ℝ) τ) y)) >>= fun a2 => pure a2)
        = _
      rw [addGradAll_toAnyArray_single t b (subSpec (fill (0 : ℝ) τ) y) nb hnb hnb_rg hnb_s
        (Algebra.TList.add (α := ℝ) u (TList.single a y))]
      rfl
    have hnodeN : (t.addNode (eagerSubNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1.getNode?
        ((Γ ++ ss).length) = some (eagerSubNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b)) := by
      have h := getNode?_addNode_size t (eagerSubNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))
      rwa [hsize] at h
    have hgetsN : ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y))[(Γ ++ ss).length]?
        = some (mkAny y) := by
      have h := Array.getElem?_push_size (xs := Algebra.TList.toAnyArray (α := ℝ) u)
        (x := mkAny y)
      rwa [husize] at h
    have hstep_e : Runtime.Autograd.Tape.backwardDenseFromStep
        (t := (t.addNode (eagerSubNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1)
        ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
      = .ok ((Algebra.TList.toAnyArray (α := ℝ)
          (Algebra.TList.add (α := ℝ) u
            ((TapeNodes.sub (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))).push
          (mkAny y)) := by
      have hfold2' := hfold2
      rw [sub_vjp_add_eq] at hfold2'
      have hpush := foldContribs_push t (eagerSubNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))
        [(a.i.val, mkAny y), (b.i.val, mkAny (subSpec (fill (0 : ℝ) τ) y))]
        (Algebra.TList.toAnyArray (α := ℝ) u) (mkAny y) (by rw [husize, hsize])
        (by
          intro pc hpc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
          rcases hpc with rfl | rfl
          · exact haLt
          · exact hbLt)
      rw [hfold2'] at hpush
      have hrgY : Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := τ) ⟨τ, y⟩ = .ok y := by
        simp [Runtime.Autograd.Tape.requireGrad]
      simp only [Runtime.Autograd.Tape.backwardDenseFromStep, hnodeN, hgetsN,
        bind, Except.bind, pure, Except.pure]
      simpa [eagerSubNode, mkAny, Runtime.Autograd.AnyTensor.mk, hrgY,
        List.foldlM_cons, List.foldlM_nil, bind, Except.bind, pure, Except.pure,
        Except.map] using hpush
    have hnodeN_c : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.sub a b)).toAlgebra x ()).1.getNode? ((Γ ++ ss).length)
      = some { name := some "proof-compiled"
               value := Runtime.Autograd.AnyTensor.mk
                 (((TapeNodes.sub a b).toAlgebra).forward
                   ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                     g.toAlgebra x ()).2) ())
               requires_grad := true
               parents := []
               backward := fun dLdyAny =>
                 if hsh : dLdyAny.s = τ then
                   .ok (Algebra.TList.toIndexedAnyList (α := ℝ) (ss := Γ ++ ss)
                     (((TapeNodes.sub a b).toAlgebra).vjp
                       ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                         g.toAlgebra x ()).2) ()
                       (Tensor.castShape dLdyAny.t hsh)) 0)
                 else .error "autograd: upstream gradient shape mismatch" } := by
      rw [hcomp, ← hsize_c]
      exact getNode?_addNode_size tc _
    have hupstream := Algebra.Graph.foldlM_addGradAll_toIndexedAnyList_eq_add (α := ℝ)
      (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.sub a b)).toAlgebra x ()).1
      (ss := Γ ++ ss) #[] u
      ((TapeNodes.sub (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y)
      #[(mkAny y : Any)]
      (by
        intro i hi
        obtain ⟨node, hnode, hval⟩ :=
          node_facts_of_values hvals_c hsize_c ⟨i, hi⟩
        have hlt : i < tc.nodes.size := by rw [hsize_c]; exact hi
        refine ⟨node, ?_, ?_, ?_⟩
        · rw [hcomp]
          show (tc.addNode _).1.getNode? (#[].size + i) = some node
          simpa using (getNode?_addNode_lt tc _ hlt).trans hnode
        · have := Algebra.Graph.compileAux_requires_grad_true (α := ℝ) (Δ := Unit)
            (Γ := Γ) (ss := ss) g.toAlgebra x ()
          have hnode' : tc.getNode? i = some (tc.nodes[i]'hlt) := by
            simp [Runtime.Autograd.Tape.getNode?, Array.getElem?_eq_getElem hlt]
          rw [hnode'] at hnode
          rw [(Option.some.inj hnode).symm]
          exact this i hlt
        · rw [hval]
          have he : (Algebra.TList.toAnyArray (α := ℝ) u)[i]'(by simpa using hi)
              = mkAny (Algebra.TList.get (α := ℝ) u ⟨i, hi⟩) := by
            simpa using Algebra.TList.get_toAnyArray (α := ℝ) (ss := Γ ++ ss) u ⟨i, hi⟩
          rw [he]
          rfl)
    have hstep_c : Runtime.Autograd.Tape.backwardDenseFromStep
        (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
          (Graph.snoc g (TapeNodes.sub a b)).toAlgebra x ()).1)
        ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
      = .ok ((Algebra.TList.toAnyArray (α := ℝ)
          (Algebra.TList.add (α := ℝ) u
            ((TapeNodes.sub (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))).push
          (mkAny y)) := by
      have hpre : (Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)
          = #[] ++ Algebra.TList.toAnyArray (α := ℝ) u ++ #[(mkAny y : Any)] := by
        simp
      have hpost : (Algebra.TList.toAnyArray (α := ℝ)
            (Algebra.TList.add (α := ℝ) u
              ((TapeNodes.sub (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))).push
            (mkAny y)
          = #[] ++ Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ) u
                ((TapeNodes.sub (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))
              ++ #[(mkAny y : Any)] := by
        simp
      simp only [Runtime.Autograd.Tape.backwardDenseFromStep, hnodeN_c, hgetsN,
        bind, Except.bind, pure, Except.pure]
      rw [hpre, hpost]
      have harg : ((TapeNodes.sub a b).toAlgebra).vjp
          ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
            g.toAlgebra x ()).2) () y
        = (TapeNodes.sub (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y := by
        rw [hctxc]
        rfl
      simpa [mkAny, Runtime.Autograd.AnyTensor.mk, harg] using hupstream
    have hN' : (Γ ++ (ss ++ [τ])).length = (Γ ++ ss).length + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [harr, hN']
    show (Runtime.Autograd.Tape.backwardDenseFromStep
          (t := (t.addNode (eagerSubNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1)
          ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
        >>= fun acc' => Runtime.Autograd.Tape.backwardDenseFromLoop
          (t := (t.addNode (eagerSubNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1)
          ((Γ ++ ss).length) acc')
      = (Runtime.Autograd.Tape.backwardDenseFromStep
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
            (Graph.snoc g (TapeNodes.sub a b)).toAlgebra x ()).1)
          ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
        >>= fun acc' => Runtime.Autograd.Tape.backwardDenseFromLoop
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
            (Graph.snoc g (TapeNodes.sub a b)).toAlgebra x ()).1)
          ((Γ ++ ss).length) acc')
    rw [hstep_e, hstep_c]
    show Runtime.Autograd.Tape.backwardDenseFromLoop
        (t := (t.addNode (eagerSubNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1) ((Γ ++ ss).length) _
      = Runtime.Autograd.Tape.backwardDenseFromLoop
        (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
          (Graph.snoc g (TapeNodes.sub a b)).toAlgebra x ()).1) ((Γ ++ ss).length) _
    rw [hcomp]
    rw [backwardDenseFromLoop_push t _ (eagerBuilds_pids hg) ((Γ ++ ss).length)
      (by rw [hsize]) _ (mkAny y) (by simp [hsize]),
      backwardDenseFromLoop_push tc _
        (fun i node hnode dc cs hback pc hpc =>
          Algebra.Graph.compileAux_backward_pids_lt_id (α := ℝ) (Δ := Unit) (Γ := Γ)
            (ss := ss) g.toAlgebra x () i node hnode dc cs hback hpc)
        ((Γ ++ ss).length) (by rw [hsize_c]) _ (mkAny y) (by simp [hsize_c])]
    rw [ih]
  | div a b hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨aT, bT, hA, hB, ht'⟩ := tape_div_inv hop
    have hsize := eagerBuilds_size hg
    have hvals := eagerBuilds_values hg
    have haT : aT = getIdx (Graph.eval g x) a := requireValue_eq_of_values hvals a hA
    have hbT : bT = getIdx (Graph.eval g x) b := requireValue_eq_of_values hvals b hB
    have haLt : a.i.val < t.nodes.size := by
      obtain ⟨pa, hpa, _⟩ := requireValue_shape t a.i.val aT hA
      exact lt_of_getNode?_eq_some hpa
    have hbLt : b.i.val < t.nodes.size := by
      obtain ⟨pb, hpb, _⟩ := requireValue_shape t b.i.val bT hB
      exact lt_of_getNode?_eq_some hpb
    rw [haT, hbT] at ht'
    subst ht'
    intro S
    set tc := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
      g.toAlgebra x ()).1 with htc
    have hsize_c : tc.nodes.size = (Γ ++ ss).length := by
      rw [htc, Algebra.Graph.compileAux_nodes_size]
      simp
    have hctxc : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
        g.toAlgebra x ()).2 = Graph.eval g x := by
      rw [Algebra.Graph.compileAux_ctx_eq_eval, eval_toAlgebra]
    have hvals_c : tc.nodes.map (fun node => node.value)
        = Algebra.TList.toAnyArray (α := ℝ) (Graph.eval g x) := by
      rw [htc, Algebra.Graph.compileAux_values_eq, hctxc]
    have hcomp : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.div a b)).toAlgebra x ()).1
      = (tc.addNode
          { name := some "proof-compiled"
            value := Runtime.Autograd.AnyTensor.mk
              (((TapeNodes.div a b).toAlgebra).forward
                ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                  g.toAlgebra x ()).2) ())
            requires_grad := true
            parents := []
            backward := fun dLdyAny =>
              if hsh : dLdyAny.s = τ then
                .ok (Algebra.TList.toIndexedAnyList (α := ℝ) (ss := Γ ++ ss)
                  (((TapeNodes.div a b).toAlgebra).vjp
                    ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                      g.toAlgebra x ()).2) ()
                    (Tensor.castShape dLdyAny.t hsh)) 0)
              else .error "autograd: upstream gradient shape mismatch" }).1 := rfl
    set S' := Algebra.TList.cast (α := ℝ) (List.append_assoc Γ ss [τ]).symm S with hS'def
    have hSS : Algebra.TList.toAnyArray (α := ℝ) S = Algebra.TList.toAnyArray (α := ℝ) S' := by
      rw [hS'def, Algebra.TList.toAnyArray_cast]
    obtain ⟨u, y, huy⟩ : ∃ (u : TList (Γ ++ ss)) (y : Tensor ℝ τ),
        S' = Algebra.TList.snoc (α := ℝ) u y :=
      ⟨(Algebra.TList.unsnoc S').1, (Algebra.TList.unsnoc S').2,
        (Algebra.TList.snoc_unsnoc (α := ℝ) (xs := S')).symm⟩
    have harr : Algebra.TList.toAnyArray (α := ℝ) S
        = (Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y) := by
      rw [hSS, huy, Algebra.TList.toAnyArray_snoc]
    have husize : (Algebra.TList.toAnyArray (α := ℝ) u).size = (Γ ++ ss).length := by simp
    obtain ⟨na, hna, hna_val⟩ := node_facts_of_values hvals hsize a.i
    obtain ⟨nb, hnb, hnb_val⟩ := node_facts_of_values hvals hsize b.i
    have hna_rg : na.requires_grad = true := eagerBuilds_rg hg a.i.val na hna
    have hnb_rg : nb.requires_grad = true := eagerBuilds_rg hg b.i.val nb hnb
    have hna_s : na.value.s = (Γ ++ ss).get a.i := by rw [hna_val]; rfl
    have hnb_s : nb.value.s = (Γ ++ ss).get b.i := by rw [hnb_val]; rfl
    have hfold2 :
        [(a.i.val, mkAny (divSpec y (getIdx (Graph.eval g x) b))),
            (b.i.val, mkAny (subSpec (fill (0 : ℝ) τ)
              (mulSpec y (divSpec (getIdx (Graph.eval g x) a)
                (mulSpec (getIdx (Graph.eval g x) b) (getIdx (Graph.eval g x) b))))))].foldlM
            (fun acc2 (pid, pg) => Runtime.Autograd.Tape.addGradAll (t := t) acc2 pid pg)
            (Algebra.TList.toAnyArray (α := ℝ) u)
          = .ok (Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ)
                (Algebra.TList.add (α := ℝ) u
                  (TList.single a (divSpec y (getIdx (Graph.eval g x) b))))
                (TList.single b (subSpec (fill (0 : ℝ) τ)
                  (mulSpec y (divSpec (getIdx (Graph.eval g x) a)
                    (mulSpec (getIdx (Graph.eval g x) b) (getIdx (Graph.eval g x) b)))))))) := by
      show (Runtime.Autograd.Tape.addGradAll (t := t)
            (Algebra.TList.toAnyArray (α := ℝ) u) a.i.val
            (mkAny (divSpec y (getIdx (Graph.eval g x) b))) >>= fun a1 =>
          (Runtime.Autograd.Tape.addGradAll (t := t) a1 b.i.val
            (mkAny (subSpec (fill (0 : ℝ) τ)
              (mulSpec y (divSpec (getIdx (Graph.eval g x) a)
                (mulSpec (getIdx (Graph.eval g x) b) (getIdx (Graph.eval g x) b))))))
            >>= fun a2 => pure a2))
        = _
      rw [addGradAll_toAnyArray_single t a (divSpec y (getIdx (Graph.eval g x) b))
        na hna hna_rg hna_s u]
      show (Runtime.Autograd.Tape.addGradAll (t := t)
            (Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ) u
                (TList.single a (divSpec y (getIdx (Graph.eval g x) b)))))
            b.i.val (mkAny (subSpec (fill (0 : ℝ) τ)
              (mulSpec y (divSpec (getIdx (Graph.eval g x) a)
                (mulSpec (getIdx (Graph.eval g x) b) (getIdx (Graph.eval g x) b))))))
            >>= fun a2 => pure a2)
        = _
      rw [addGradAll_toAnyArray_single t b (subSpec (fill (0 : ℝ) τ)
          (mulSpec y (divSpec (getIdx (Graph.eval g x) a)
            (mulSpec (getIdx (Graph.eval g x) b) (getIdx (Graph.eval g x) b)))))
        nb hnb hnb_rg hnb_s
        (Algebra.TList.add (α := ℝ) u
          (TList.single a (divSpec y (getIdx (Graph.eval g x) b))))]
      rfl
    have hnodeN : (t.addNode (eagerDivNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1.getNode?
        ((Γ ++ ss).length) = some (eagerDivNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b)) := by
      have h := getNode?_addNode_size t (eagerDivNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))
      rwa [hsize] at h
    have hgetsN : ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y))[(Γ ++ ss).length]?
        = some (mkAny y) := by
      have h := Array.getElem?_push_size (xs := Algebra.TList.toAnyArray (α := ℝ) u)
        (x := mkAny y)
      rwa [husize] at h
    have hstep_e : Runtime.Autograd.Tape.backwardDenseFromStep
        (t := (t.addNode (eagerDivNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1)
        ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
      = .ok ((Algebra.TList.toAnyArray (α := ℝ)
          (Algebra.TList.add (α := ℝ) u
            ((TapeNodes.div (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))).push
          (mkAny y)) := by
      have hfold2' := hfold2
      rw [div_vjp_add_eq] at hfold2'
      have hpush := foldContribs_push t (eagerDivNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))
        [(a.i.val, mkAny (divSpec y (getIdx (Graph.eval g x) b))),
          (b.i.val, mkAny (subSpec (fill (0 : ℝ) τ)
            (mulSpec y (divSpec (getIdx (Graph.eval g x) a)
              (mulSpec (getIdx (Graph.eval g x) b) (getIdx (Graph.eval g x) b))))))]
        (Algebra.TList.toAnyArray (α := ℝ) u) (mkAny y) (by rw [husize, hsize])
        (by
          intro pc hpc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
          rcases hpc with rfl | rfl
          · exact haLt
          · exact hbLt)
      rw [hfold2'] at hpush
      have hrgY : Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := τ) ⟨τ, y⟩ = .ok y := by
        simp [Runtime.Autograd.Tape.requireGrad]
      simp only [Runtime.Autograd.Tape.backwardDenseFromStep, hnodeN, hgetsN,
        bind, Except.bind, pure, Except.pure]
      simpa [eagerDivNode, mkAny, Runtime.Autograd.AnyTensor.mk, hrgY,
        List.foldlM_cons, List.foldlM_nil, bind, Except.bind, pure, Except.pure,
        Except.map] using hpush
    have hnodeN_c : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.div a b)).toAlgebra x ()).1.getNode? ((Γ ++ ss).length)
      = some { name := some "proof-compiled"
               value := Runtime.Autograd.AnyTensor.mk
                 (((TapeNodes.div a b).toAlgebra).forward
                   ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                     g.toAlgebra x ()).2) ())
               requires_grad := true
               parents := []
               backward := fun dLdyAny =>
                 if hsh : dLdyAny.s = τ then
                   .ok (Algebra.TList.toIndexedAnyList (α := ℝ) (ss := Γ ++ ss)
                     (((TapeNodes.div a b).toAlgebra).vjp
                       ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                         g.toAlgebra x ()).2) ()
                       (Tensor.castShape dLdyAny.t hsh)) 0)
                 else .error "autograd: upstream gradient shape mismatch" } := by
      rw [hcomp, ← hsize_c]
      exact getNode?_addNode_size tc _
    have hupstream := Algebra.Graph.foldlM_addGradAll_toIndexedAnyList_eq_add (α := ℝ)
      (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.div a b)).toAlgebra x ()).1
      (ss := Γ ++ ss) #[] u
      ((TapeNodes.div (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y)
      #[(mkAny y : Any)]
      (by
        intro i hi
        obtain ⟨node, hnode, hval⟩ :=
          node_facts_of_values hvals_c hsize_c ⟨i, hi⟩
        have hlt : i < tc.nodes.size := by rw [hsize_c]; exact hi
        refine ⟨node, ?_, ?_, ?_⟩
        · rw [hcomp]
          show (tc.addNode _).1.getNode? (#[].size + i) = some node
          simpa using (getNode?_addNode_lt tc _ hlt).trans hnode
        · have := Algebra.Graph.compileAux_requires_grad_true (α := ℝ) (Δ := Unit)
            (Γ := Γ) (ss := ss) g.toAlgebra x ()
          have hnode' : tc.getNode? i = some (tc.nodes[i]'hlt) := by
            simp [Runtime.Autograd.Tape.getNode?, Array.getElem?_eq_getElem hlt]
          rw [hnode'] at hnode
          rw [(Option.some.inj hnode).symm]
          exact this i hlt
        · rw [hval]
          have he : (Algebra.TList.toAnyArray (α := ℝ) u)[i]'(by simpa using hi)
              = mkAny (Algebra.TList.get (α := ℝ) u ⟨i, hi⟩) := by
            simpa using Algebra.TList.get_toAnyArray (α := ℝ) (ss := Γ ++ ss) u ⟨i, hi⟩
          rw [he]
          rfl)
    have hstep_c : Runtime.Autograd.Tape.backwardDenseFromStep
        (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
          (Graph.snoc g (TapeNodes.div a b)).toAlgebra x ()).1)
        ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
      = .ok ((Algebra.TList.toAnyArray (α := ℝ)
          (Algebra.TList.add (α := ℝ) u
            ((TapeNodes.div (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))).push
          (mkAny y)) := by
      have hpre : (Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)
          = #[] ++ Algebra.TList.toAnyArray (α := ℝ) u ++ #[(mkAny y : Any)] := by
        simp
      have hpost : (Algebra.TList.toAnyArray (α := ℝ)
            (Algebra.TList.add (α := ℝ) u
              ((TapeNodes.div (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))).push
            (mkAny y)
          = #[] ++ Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ) u
                ((TapeNodes.div (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y))
              ++ #[(mkAny y : Any)] := by
        simp
      simp only [Runtime.Autograd.Tape.backwardDenseFromStep, hnodeN_c, hgetsN,
        bind, Except.bind, pure, Except.pure]
      rw [hpre, hpost]
      have harg : ((TapeNodes.div a b).toAlgebra).vjp
          ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
            g.toAlgebra x ()).2) () y
        = (TapeNodes.div (Γ := Γ ++ ss) (s := τ) a b).vjp (Graph.eval g x) y := by
        rw [hctxc]
        rfl
      simpa [mkAny, Runtime.Autograd.AnyTensor.mk, harg] using hupstream
    have hN' : (Γ ++ (ss ++ [τ])).length = (Γ ++ ss).length + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [harr, hN']
    show (Runtime.Autograd.Tape.backwardDenseFromStep
          (t := (t.addNode (eagerDivNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1)
          ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
        >>= fun acc' => Runtime.Autograd.Tape.backwardDenseFromLoop
          (t := (t.addNode (eagerDivNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1)
          ((Γ ++ ss).length) acc')
      = (Runtime.Autograd.Tape.backwardDenseFromStep
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
            (Graph.snoc g (TapeNodes.div a b)).toAlgebra x ()).1)
          ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
        >>= fun acc' => Runtime.Autograd.Tape.backwardDenseFromLoop
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
            (Graph.snoc g (TapeNodes.div a b)).toAlgebra x ()).1)
          ((Γ ++ ss).length) acc')
    rw [hstep_e, hstep_c]
    show Runtime.Autograd.Tape.backwardDenseFromLoop
        (t := (t.addNode (eagerDivNode a.i.val b.i.val (getIdx (Graph.eval g x) a) (getIdx (Graph.eval g x) b))).1) ((Γ ++ ss).length) _
      = Runtime.Autograd.Tape.backwardDenseFromLoop
        (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
          (Graph.snoc g (TapeNodes.div a b)).toAlgebra x ()).1) ((Γ ++ ss).length) _
    rw [hcomp]
    rw [backwardDenseFromLoop_push t _ (eagerBuilds_pids hg) ((Γ ++ ss).length)
      (by rw [hsize]) _ (mkAny y) (by simp [hsize]),
      backwardDenseFromLoop_push tc _
        (fun i node hnode dc cs hback pc hpc =>
          Algebra.Graph.compileAux_backward_pids_lt_id (α := ℝ) (Δ := Unit) (Γ := Γ)
            (ss := ss) g.toAlgebra x () i node hnode dc cs hback hpc)
        ((Γ ++ ss).length) (by rw [hsize_c]) _ (mkAny y) (by simp [hsize_c])]
    rw [ih]
  | scale idx c hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨xT, hX, ht'⟩ := tape_scale_inv hop
    have hsize := eagerBuilds_size hg
    have hvals := eagerBuilds_values hg
    have hxT : xT = getIdx (Graph.eval g x) idx := requireValue_eq_of_values hvals idx hX
    have hxLt : idx.i.val < t.nodes.size := by
      obtain ⟨px, hpx, _⟩ := requireValue_shape t idx.i.val xT hX
      exact lt_of_getNode?_eq_some hpx
    rw [hxT] at ht'
    subst ht'
    intro S
    set tc := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
      g.toAlgebra x ()).1 with htc
    have hsize_c : tc.nodes.size = (Γ ++ ss).length := by
      rw [htc, Algebra.Graph.compileAux_nodes_size]
      simp
    have hctxc : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
        g.toAlgebra x ()).2 = Graph.eval g x := by
      rw [Algebra.Graph.compileAux_ctx_eq_eval, eval_toAlgebra]
    have hvals_c : tc.nodes.map (fun node => node.value)
        = Algebra.TList.toAnyArray (α := ℝ) (Graph.eval g x) := by
      rw [htc, Algebra.Graph.compileAux_values_eq, hctxc]
    have hcomp : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.scale idx c)).toAlgebra x ()).1
      = (tc.addNode
          { name := some "proof-compiled"
            value := Runtime.Autograd.AnyTensor.mk
              (((TapeNodes.scale idx c).toAlgebra).forward
                ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                  g.toAlgebra x ()).2) ())
            requires_grad := true
            parents := []
            backward := fun dLdyAny =>
              if hsh : dLdyAny.s = τ then
                .ok (Algebra.TList.toIndexedAnyList (α := ℝ) (ss := Γ ++ ss)
                  (((TapeNodes.scale idx c).toAlgebra).vjp
                    ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                      g.toAlgebra x ()).2) ()
                    (Tensor.castShape dLdyAny.t hsh)) 0)
              else .error "autograd: upstream gradient shape mismatch" }).1 := rfl
    set S' := Algebra.TList.cast (α := ℝ) (List.append_assoc Γ ss [τ]).symm S with hS'def
    have hSS : Algebra.TList.toAnyArray (α := ℝ) S = Algebra.TList.toAnyArray (α := ℝ) S' := by
      rw [hS'def, Algebra.TList.toAnyArray_cast]
    obtain ⟨u, y, huy⟩ : ∃ (u : TList (Γ ++ ss)) (y : Tensor ℝ τ),
        S' = Algebra.TList.snoc (α := ℝ) u y :=
      ⟨(Algebra.TList.unsnoc S').1, (Algebra.TList.unsnoc S').2,
        (Algebra.TList.snoc_unsnoc (α := ℝ) (xs := S')).symm⟩
    have harr : Algebra.TList.toAnyArray (α := ℝ) S
        = (Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y) := by
      rw [hSS, huy, Algebra.TList.toAnyArray_snoc]
    have husize : (Algebra.TList.toAnyArray (α := ℝ) u).size = (Γ ++ ss).length := by simp
    obtain ⟨nx, hnx, hnx_val⟩ := node_facts_of_values hvals hsize idx.i
    have hnx_rg : nx.requires_grad = true := eagerBuilds_rg hg idx.i.val nx hnx
    have hnx_s : nx.value.s = (Γ ++ ss).get idx.i := by rw [hnx_val]; rfl
    have hfold1 :
        [(idx.i.val, mkAny (scaleSpec y c))].foldlM
            (fun acc2 (pid, pg) => Runtime.Autograd.Tape.addGradAll (t := t) acc2 pid pg)
            (Algebra.TList.toAnyArray (α := ℝ) u)
          = .ok (Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ) u (TList.single idx (scaleSpec y c)))) := by
      show (Runtime.Autograd.Tape.addGradAll (t := t)
            (Algebra.TList.toAnyArray (α := ℝ) u) idx.i.val (mkAny (scaleSpec y c))
            >>= fun a1 => pure a1)
        = _
      rw [addGradAll_toAnyArray_single t idx (scaleSpec y c) nx hnx hnx_rg hnx_s u]
      rfl
    have hnodeN : (t.addNode (eagerScaleNode idx.i.val c (getIdx (Graph.eval g x) idx))).1.getNode?
        ((Γ ++ ss).length) = some (eagerScaleNode idx.i.val c (getIdx (Graph.eval g x) idx)) := by
      have h := getNode?_addNode_size t (eagerScaleNode idx.i.val c (getIdx (Graph.eval g x) idx))
      rwa [hsize] at h
    have hgetsN : ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y))[(Γ ++ ss).length]?
        = some (mkAny y) := by
      have h := Array.getElem?_push_size (xs := Algebra.TList.toAnyArray (α := ℝ) u)
        (x := mkAny y)
      rwa [husize] at h
    have hstep_e : Runtime.Autograd.Tape.backwardDenseFromStep
        (t := (t.addNode (eagerScaleNode idx.i.val c (getIdx (Graph.eval g x) idx))).1)
        ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
      = .ok ((Algebra.TList.toAnyArray (α := ℝ)
          (Algebra.TList.add (α := ℝ) u
            ((TapeNodes.scale (Γ := Γ ++ ss) (s := τ) idx c).vjp (Graph.eval g x) y))).push
          (mkAny y)) := by
      have hfold1' := hfold1
      rw [scale_vjp_add_eq] at hfold1'
      have hpush := foldContribs_push t (eagerScaleNode idx.i.val c (getIdx (Graph.eval g x) idx))
        [(idx.i.val, mkAny (scaleSpec y c))]
        (Algebra.TList.toAnyArray (α := ℝ) u) (mkAny y) (by rw [husize, hsize])
        (by
          intro pc hpc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
          rcases hpc with rfl
          exact hxLt)
      rw [hfold1'] at hpush
      have hrgY : Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := τ) ⟨τ, y⟩ = .ok y := by
        simp [Runtime.Autograd.Tape.requireGrad]
      simp only [Runtime.Autograd.Tape.backwardDenseFromStep, hnodeN, hgetsN,
        bind, Except.bind, pure, Except.pure]
      simpa [eagerScaleNode, mkAny, Runtime.Autograd.AnyTensor.mk, hrgY,
        List.foldlM_cons, List.foldlM_nil, bind, Except.bind, pure, Except.pure,
        Except.map] using hpush
    have hnodeN_c : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.scale idx c)).toAlgebra x ()).1.getNode? ((Γ ++ ss).length)
      = some { name := some "proof-compiled"
               value := Runtime.Autograd.AnyTensor.mk
                 (((TapeNodes.scale idx c).toAlgebra).forward
                   ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                     g.toAlgebra x ()).2) ())
               requires_grad := true
               parents := []
               backward := fun dLdyAny =>
                 if hsh : dLdyAny.s = τ then
                   .ok (Algebra.TList.toIndexedAnyList (α := ℝ) (ss := Γ ++ ss)
                     (((TapeNodes.scale idx c).toAlgebra).vjp
                       ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                         g.toAlgebra x ()).2) ()
                       (Tensor.castShape dLdyAny.t hsh)) 0)
                 else .error "autograd: upstream gradient shape mismatch" } := by
      rw [hcomp, ← hsize_c]
      exact getNode?_addNode_size tc _
    have hupstream := Algebra.Graph.foldlM_addGradAll_toIndexedAnyList_eq_add (α := ℝ)
      (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.scale idx c)).toAlgebra x ()).1
      (ss := Γ ++ ss) #[] u
      ((TapeNodes.scale (Γ := Γ ++ ss) (s := τ) idx c).vjp (Graph.eval g x) y)
      #[(mkAny y : Any)]
      (by
        intro i hi
        obtain ⟨node, hnode, hval⟩ :=
          node_facts_of_values hvals_c hsize_c ⟨i, hi⟩
        have hlt : i < tc.nodes.size := by rw [hsize_c]; exact hi
        refine ⟨node, ?_, ?_, ?_⟩
        · rw [hcomp]
          show (tc.addNode _).1.getNode? (#[].size + i) = some node
          simpa using (getNode?_addNode_lt tc _ hlt).trans hnode
        · have := Algebra.Graph.compileAux_requires_grad_true (α := ℝ) (Δ := Unit)
            (Γ := Γ) (ss := ss) g.toAlgebra x ()
          have hnode' : tc.getNode? i = some (tc.nodes[i]'hlt) := by
            simp [Runtime.Autograd.Tape.getNode?, Array.getElem?_eq_getElem hlt]
          rw [hnode'] at hnode
          rw [(Option.some.inj hnode).symm]
          exact this i hlt
        · rw [hval]
          have he : (Algebra.TList.toAnyArray (α := ℝ) u)[i]'(by simpa using hi)
              = mkAny (Algebra.TList.get (α := ℝ) u ⟨i, hi⟩) := by
            simpa using Algebra.TList.get_toAnyArray (α := ℝ) (ss := Γ ++ ss) u ⟨i, hi⟩
          rw [he]
          rfl)
    have hstep_c : Runtime.Autograd.Tape.backwardDenseFromStep
        (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
          (Graph.snoc g (TapeNodes.scale idx c)).toAlgebra x ()).1)
        ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
      = .ok ((Algebra.TList.toAnyArray (α := ℝ)
          (Algebra.TList.add (α := ℝ) u
            ((TapeNodes.scale (Γ := Γ ++ ss) (s := τ) idx c).vjp (Graph.eval g x) y))).push
          (mkAny y)) := by
      have hpre : (Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)
          = #[] ++ Algebra.TList.toAnyArray (α := ℝ) u ++ #[(mkAny y : Any)] := by
        simp
      have hpost : (Algebra.TList.toAnyArray (α := ℝ)
            (Algebra.TList.add (α := ℝ) u
              ((TapeNodes.scale (Γ := Γ ++ ss) (s := τ) idx c).vjp (Graph.eval g x) y))).push
            (mkAny y)
          = #[] ++ Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ) u
                ((TapeNodes.scale (Γ := Γ ++ ss) (s := τ) idx c).vjp (Graph.eval g x) y))
              ++ #[(mkAny y : Any)] := by
        simp
      simp only [Runtime.Autograd.Tape.backwardDenseFromStep, hnodeN_c, hgetsN,
        bind, Except.bind, pure, Except.pure]
      rw [hpre, hpost]
      have harg : ((TapeNodes.scale idx c).toAlgebra).vjp
          ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
            g.toAlgebra x ()).2) () y
        = (TapeNodes.scale (Γ := Γ ++ ss) (s := τ) idx c).vjp (Graph.eval g x) y := by
        rw [hctxc]
        rfl
      simpa [mkAny, Runtime.Autograd.AnyTensor.mk, harg] using hupstream
    have hN' : (Γ ++ (ss ++ [τ])).length = (Γ ++ ss).length + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [harr, hN']
    show (Runtime.Autograd.Tape.backwardDenseFromStep
          (t := (t.addNode (eagerScaleNode idx.i.val c (getIdx (Graph.eval g x) idx))).1)
          ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
        >>= fun acc' => Runtime.Autograd.Tape.backwardDenseFromLoop
          (t := (t.addNode (eagerScaleNode idx.i.val c (getIdx (Graph.eval g x) idx))).1)
          ((Γ ++ ss).length) acc')
      = (Runtime.Autograd.Tape.backwardDenseFromStep
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
            (Graph.snoc g (TapeNodes.scale idx c)).toAlgebra x ()).1)
          ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
        >>= fun acc' => Runtime.Autograd.Tape.backwardDenseFromLoop
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
            (Graph.snoc g (TapeNodes.scale idx c)).toAlgebra x ()).1)
          ((Γ ++ ss).length) acc')
    rw [hstep_e, hstep_c]
    show Runtime.Autograd.Tape.backwardDenseFromLoop
        (t := (t.addNode (eagerScaleNode idx.i.val c (getIdx (Graph.eval g x) idx))).1) ((Γ ++ ss).length) _
      = Runtime.Autograd.Tape.backwardDenseFromLoop
        (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
          (Graph.snoc g (TapeNodes.scale idx c)).toAlgebra x ()).1) ((Γ ++ ss).length) _
    rw [hcomp]
    rw [backwardDenseFromLoop_push t _ (eagerBuilds_pids hg) ((Γ ++ ss).length)
      (by rw [hsize]) _ (mkAny y) (by simp [hsize]),
      backwardDenseFromLoop_push tc _
        (fun i node hnode dc cs hback pc hpc =>
          Algebra.Graph.compileAux_backward_pids_lt_id (α := ℝ) (Δ := Unit) (Γ := Γ)
            (ss := ss) g.toAlgebra x () i node hnode dc cs hback hpc)
        ((Γ ++ ss).length) (by rw [hsize_c]) _ (mkAny y) (by simp [hsize_c])]
    rw [ih]
  | unary idx name f f' fwdSpec bwdSpec hfs hf's hg hop ih =>
    rename_i ss τ g x t t' id
    obtain ⟨xT, hX, ht'⟩ := tape_unary_inv hop
    have hsize := eagerBuilds_size hg
    have hvals := eagerBuilds_values hg
    have hxT : xT = getIdx (Graph.eval g x) idx := requireValue_eq_of_values hvals idx hX
    have hxLt : idx.i.val < t.nodes.size := by
      obtain ⟨px, hpx, _⟩ := requireValue_shape t idx.i.val xT hX
      exact lt_of_getNode?_eq_some hpx
    rw [hxT] at ht'
    subst ht'
    intro S
    set tc := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
      g.toAlgebra x ()).1 with htc
    have hsize_c : tc.nodes.size = (Γ ++ ss).length := by
      rw [htc, Algebra.Graph.compileAux_nodes_size]
      simp
    have hctxc : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
        g.toAlgebra x ()).2 = Graph.eval g x := by
      rw [Algebra.Graph.compileAux_ctx_eq_eval, eval_toAlgebra]
    have hvals_c : tc.nodes.map (fun node => node.value)
        = Algebra.TList.toAnyArray (α := ℝ) (Graph.eval g x) := by
      rw [htc, Algebra.Graph.compileAux_values_eq, hctxc]
    have hcomp : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.elemwise idx f f')).toAlgebra x ()).1
      = (tc.addNode
          { name := some "proof-compiled"
            value := Runtime.Autograd.AnyTensor.mk
              (((TapeNodes.elemwise idx f f').toAlgebra).forward
                ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                  g.toAlgebra x ()).2) ())
            requires_grad := true
            parents := []
            backward := fun dLdyAny =>
              if hsh : dLdyAny.s = τ then
                .ok (Algebra.TList.toIndexedAnyList (α := ℝ) (ss := Γ ++ ss)
                  (((TapeNodes.elemwise idx f f').toAlgebra).vjp
                    ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                      g.toAlgebra x ()).2) ()
                    (Tensor.castShape dLdyAny.t hsh)) 0)
              else .error "autograd: upstream gradient shape mismatch" }).1 := rfl
    set S' := Algebra.TList.cast (α := ℝ) (List.append_assoc Γ ss [τ]).symm S with hS'def
    have hSS : Algebra.TList.toAnyArray (α := ℝ) S = Algebra.TList.toAnyArray (α := ℝ) S' := by
      rw [hS'def, Algebra.TList.toAnyArray_cast]
    obtain ⟨u, y, huy⟩ : ∃ (u : TList (Γ ++ ss)) (y : Tensor ℝ τ),
        S' = Algebra.TList.snoc (α := ℝ) u y :=
      ⟨(Algebra.TList.unsnoc S').1, (Algebra.TList.unsnoc S').2,
        (Algebra.TList.snoc_unsnoc (α := ℝ) (xs := S')).symm⟩
    have harr : Algebra.TList.toAnyArray (α := ℝ) S
        = (Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y) := by
      rw [hSS, huy, Algebra.TList.toAnyArray_snoc]
    have husize : (Algebra.TList.toAnyArray (α := ℝ) u).size = (Γ ++ ss).length := by simp
    obtain ⟨nx, hnx, hnx_val⟩ := node_facts_of_values hvals hsize idx.i
    have hnx_rg : nx.requires_grad = true := eagerBuilds_rg hg idx.i.val nx hnx
    have hnx_s : nx.value.s = (Γ ++ ss).get idx.i := by rw [hnx_val]; rfl
    have hfold1 :
        [(idx.i.val, mkAny (mulSpec (bwdSpec (getIdx (Graph.eval g x) idx)) y))].foldlM
            (fun acc2 (pid, pg) => Runtime.Autograd.Tape.addGradAll (t := t) acc2 pid pg)
            (Algebra.TList.toAnyArray (α := ℝ) u)
          = .ok (Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ) u
                (TList.single idx (mulSpec (bwdSpec (getIdx (Graph.eval g x) idx)) y)))) := by
      show (Runtime.Autograd.Tape.addGradAll (t := t)
            (Algebra.TList.toAnyArray (α := ℝ) u) idx.i.val
            (mkAny (mulSpec (bwdSpec (getIdx (Graph.eval g x) idx)) y))
            >>= fun a1 => pure a1)
        = _
      rw [addGradAll_toAnyArray_single t idx (mulSpec (bwdSpec (getIdx (Graph.eval g x) idx)) y)
        nx hnx hnx_rg hnx_s u]
      rfl
    have hnodeN : (t.addNode (eagerUnaryNode name idx.i.val fwdSpec bwdSpec
          (getIdx (Graph.eval g x) idx))).1.getNode? ((Γ ++ ss).length)
        = some (eagerUnaryNode name idx.i.val fwdSpec bwdSpec (getIdx (Graph.eval g x) idx)) := by
      have h := getNode?_addNode_size t
        (eagerUnaryNode name idx.i.val fwdSpec bwdSpec (getIdx (Graph.eval g x) idx))
      rwa [hsize] at h
    have hgetsN : ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y))[(Γ ++ ss).length]?
        = some (mkAny y) := by
      have h := Array.getElem?_push_size (xs := Algebra.TList.toAnyArray (α := ℝ) u)
        (x := mkAny y)
      rwa [husize] at h
    have hstep_e : Runtime.Autograd.Tape.backwardDenseFromStep
        (t := (t.addNode (eagerUnaryNode name idx.i.val fwdSpec bwdSpec
          (getIdx (Graph.eval g x) idx))).1)
        ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
      = .ok ((Algebra.TList.toAnyArray (α := ℝ)
          (Algebra.TList.add (α := ℝ) u
            ((TapeNodes.elemwise (Γ := Γ ++ ss) (s := τ) idx f f').vjp (Graph.eval g x) y))).push
          (mkAny y)) := by
      have hfold1' := hfold1
      rw [elemwise_vjp_add_eq idx f f' bwdSpec hf's] at hfold1'
      have hpush := foldContribs_push t
        (eagerUnaryNode name idx.i.val fwdSpec bwdSpec (getIdx (Graph.eval g x) idx))
        [(idx.i.val, mkAny (mulSpec (bwdSpec (getIdx (Graph.eval g x) idx)) y))]
        (Algebra.TList.toAnyArray (α := ℝ) u) (mkAny y) (by rw [husize, hsize])
        (by
          intro pc hpc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
          rcases hpc with rfl
          exact hxLt)
      rw [hfold1'] at hpush
      have hrgY : Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := τ) ⟨τ, y⟩ = .ok y := by
        simp [Runtime.Autograd.Tape.requireGrad]
      simp only [Runtime.Autograd.Tape.backwardDenseFromStep, hnodeN, hgetsN,
        bind, Except.bind, pure, Except.pure]
      simpa [eagerUnaryNode, mkAny, Runtime.Autograd.AnyTensor.mk, hrgY,
        List.foldlM_cons, List.foldlM_nil, bind, Except.bind, pure, Except.pure,
        Except.map] using hpush
    have hnodeN_c : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.elemwise idx f f')).toAlgebra x ()).1.getNode? ((Γ ++ ss).length)
      = some { name := some "proof-compiled"
               value := Runtime.Autograd.AnyTensor.mk
                 (((TapeNodes.elemwise idx f f').toAlgebra).forward
                   ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                     g.toAlgebra x ()).2) ())
               requires_grad := true
               parents := []
               backward := fun dLdyAny =>
                 if hsh : dLdyAny.s = τ then
                   .ok (Algebra.TList.toIndexedAnyList (α := ℝ) (ss := Γ ++ ss)
                     (((TapeNodes.elemwise idx f f').toAlgebra).vjp
                       ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
                         g.toAlgebra x ()).2) ()
                       (Tensor.castShape dLdyAny.t hsh)) 0)
                 else .error "autograd: upstream gradient shape mismatch" } := by
      rw [hcomp, ← hsize_c]
      exact getNode?_addNode_size tc _
    have hupstream := Algebra.Graph.foldlM_addGradAll_toIndexedAnyList_eq_add (α := ℝ)
      (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
        (Graph.snoc g (TapeNodes.elemwise idx f f')).toAlgebra x ()).1
      (ss := Γ ++ ss) #[] u
      ((TapeNodes.elemwise (Γ := Γ ++ ss) (s := τ) idx f f').vjp (Graph.eval g x) y)
      #[(mkAny y : Any)]
      (by
        intro i hi
        obtain ⟨node, hnode, hval⟩ :=
          node_facts_of_values hvals_c hsize_c ⟨i, hi⟩
        have hlt : i < tc.nodes.size := by rw [hsize_c]; exact hi
        refine ⟨node, ?_, ?_, ?_⟩
        · rw [hcomp]
          show (tc.addNode _).1.getNode? (#[].size + i) = some node
          simpa using (getNode?_addNode_lt tc _ hlt).trans hnode
        · have := Algebra.Graph.compileAux_requires_grad_true (α := ℝ) (Δ := Unit)
            (Γ := Γ) (ss := ss) g.toAlgebra x ()
          have hnode' : tc.getNode? i = some (tc.nodes[i]'hlt) := by
            simp [Runtime.Autograd.Tape.getNode?, Array.getElem?_eq_getElem hlt]
          rw [hnode'] at hnode
          rw [(Option.some.inj hnode).symm]
          exact this i hlt
        · rw [hval]
          have he : (Algebra.TList.toAnyArray (α := ℝ) u)[i]'(by simpa using hi)
              = mkAny (Algebra.TList.get (α := ℝ) u ⟨i, hi⟩) := by
            simpa using Algebra.TList.get_toAnyArray (α := ℝ) (ss := Γ ++ ss) u ⟨i, hi⟩
          rw [he]
          rfl)
    have hstep_c : Runtime.Autograd.Tape.backwardDenseFromStep
        (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
          (Graph.snoc g (TapeNodes.elemwise idx f f')).toAlgebra x ()).1)
        ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
      = .ok ((Algebra.TList.toAnyArray (α := ℝ)
          (Algebra.TList.add (α := ℝ) u
            ((TapeNodes.elemwise (Γ := Γ ++ ss) (s := τ) idx f f').vjp (Graph.eval g x) y))).push
          (mkAny y)) := by
      have hpre : (Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)
          = #[] ++ Algebra.TList.toAnyArray (α := ℝ) u ++ #[(mkAny y : Any)] := by
        simp
      have hpost : (Algebra.TList.toAnyArray (α := ℝ)
            (Algebra.TList.add (α := ℝ) u
              ((TapeNodes.elemwise (Γ := Γ ++ ss) (s := τ) idx f f').vjp (Graph.eval g x) y))).push
            (mkAny y)
          = #[] ++ Algebra.TList.toAnyArray (α := ℝ)
              (Algebra.TList.add (α := ℝ) u
                ((TapeNodes.elemwise (Γ := Γ ++ ss) (s := τ) idx f f').vjp (Graph.eval g x) y))
              ++ #[(mkAny y : Any)] := by
        simp
      simp only [Runtime.Autograd.Tape.backwardDenseFromStep, hnodeN_c, hgetsN,
        bind, Except.bind, pure, Except.pure]
      rw [hpre, hpost]
      have harg : ((TapeNodes.elemwise idx f f').toAlgebra).vjp
          ((Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
            g.toAlgebra x ()).2) () y
        = (TapeNodes.elemwise (Γ := Γ ++ ss) (s := τ) idx f f').vjp (Graph.eval g x) y := by
        rw [hctxc]
        rfl
      simpa [mkAny, Runtime.Autograd.AnyTensor.mk, harg] using hupstream
    have hN' : (Γ ++ (ss ++ [τ])).length = (Γ ++ ss).length + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [harr, hN']
    show (Runtime.Autograd.Tape.backwardDenseFromStep
          (t := (t.addNode (eagerUnaryNode name idx.i.val fwdSpec bwdSpec
            (getIdx (Graph.eval g x) idx))).1)
          ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
        >>= fun acc' => Runtime.Autograd.Tape.backwardDenseFromLoop
          (t := (t.addNode (eagerUnaryNode name idx.i.val fwdSpec bwdSpec
            (getIdx (Graph.eval g x) idx))).1)
          ((Γ ++ ss).length) acc')
      = (Runtime.Autograd.Tape.backwardDenseFromStep
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
            (Graph.snoc g (TapeNodes.elemwise idx f f')).toAlgebra x ()).1)
          ((Algebra.TList.toAnyArray (α := ℝ) u).push (mkAny y)) ((Γ ++ ss).length)
        >>= fun acc' => Runtime.Autograd.Tape.backwardDenseFromLoop
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
            (Graph.snoc g (TapeNodes.elemwise idx f f')).toAlgebra x ()).1)
          ((Γ ++ ss).length) acc')
    rw [hstep_e, hstep_c]
    show Runtime.Autograd.Tape.backwardDenseFromLoop
        (t := (t.addNode (eagerUnaryNode name idx.i.val fwdSpec bwdSpec
          (getIdx (Graph.eval g x) idx))).1) ((Γ ++ ss).length) _
      = Runtime.Autograd.Tape.backwardDenseFromLoop
        (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss ++ [τ])
          (Graph.snoc g (TapeNodes.elemwise idx f f')).toAlgebra x ()).1) ((Γ ++ ss).length) _
    rw [hcomp]
    rw [backwardDenseFromLoop_push t _ (eagerBuilds_pids hg) ((Γ ++ ss).length)
      (by rw [hsize]) _ (mkAny y) (by simp [hsize]),
      backwardDenseFromLoop_push tc _
        (fun i node hnode dc cs hback pc hpc =>
          Algebra.Graph.compileAux_backward_pids_lt_id (α := ℝ) (Δ := Unit) (Γ := Γ)
            (ss := ss) g.toAlgebra x () i node hnode dc cs hback hpc)
        ((Γ ++ ss).length) (by rw [hsize_c]) _ (mkAny y) (by simp [hsize_c])]
    rw [ih]

/-- **The eager tape's total dense reverse pass is the compiled tape's.** -/
theorem backwardDenseFrom_eager_eq_compiled {Γ ss : List Shape} {g : Graph Γ ss}
    {x : TList Γ} {t : RTape} (h : EagerBuilds g x t) (S : TList (Γ ++ ss)) :
    Runtime.Autograd.Tape.backwardDenseFrom (t := t) (Algebra.TList.toAnyArray (α := ℝ) S)
      = Runtime.Autograd.Tape.backwardDenseFrom
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
            g.toAlgebra x ()).1)
          (Algebra.TList.toAnyArray (α := ℝ) S) := by
  have hsz_e := eagerBuilds_size h
  have hsz_c : (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
      g.toAlgebra x ()).1.nodes.size = (Γ ++ ss).length := by
    rw [Algebra.Graph.compileAux_nodes_size]
    simp
  have hS : (Algebra.TList.toAnyArray (α := ℝ) S).size = (Γ ++ ss).length := by simp
  show (if (Algebra.TList.toAnyArray (α := ℝ) S).size = t.nodes.size then
      Runtime.Autograd.Tape.backwardDenseFromLoop (t := t) t.nodes.size
        (Algebra.TList.toAnyArray (α := ℝ) S)
    else throw "autograd: initial dense gradient array has wrong length") = _
  rw [if_pos (by rw [hS, hsz_e]), hsz_e]
  show _ = (if (Algebra.TList.toAnyArray (α := ℝ) S).size
      = (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
        g.toAlgebra x ()).1.nodes.size then
      Runtime.Autograd.Tape.backwardDenseFromLoop
        (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
          g.toAlgebra x ()).1)
        (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
          g.toAlgebra x ()).1.nodes.size
        (Algebra.TList.toAnyArray (α := ℝ) S)
    else throw "autograd: initial dense gradient array has wrong length")
  rw [if_pos (by rw [hS, hsz_c]), hsz_c]
  exact loop_eager_eq_compiled h S

/-- Eager tapes inhabit the forward simulation relation. -/
theorem forwardSim_eager {Γ ss : List Shape} {g : Graph Γ ss} {x : TList Γ} {t : RTape}
    (h : EagerBuilds g x t) : ForwardSim g (flattenCtx x) t := by
  refine ⟨eagerBuilds_size h, ?_⟩
  intro i
  obtain ⟨node, hnode, hval⟩ := node_facts_of_values (eagerBuilds_values h)
    (eagerBuilds_size h) i
  have : t.getValue? i.val = some node.value := by
    simp [Runtime.Autograd.Tape.getValue?, hnode]
  rw [this, hval]
  unfold ctxSlotValue
  rw [Graph.evalVec_flattenCtx, getRaw_flattenCtx, ofVecT_toVecT]

/-- **The Stage-3.5/3.6 endpoint, on the eagerly built tape**: the dense reverse pass on the
    runtime-constructed `leaf`/`add`/`mul` tape succeeds, and the input-prefix of its output
    realises the adjoint of the Fréchet derivative of the graph's forward evaluation. -/
theorem direct_PR_soundness_eager {Γ ss : List Shape}
    (g : Graph Γ ss) (hg : GraphFDerivCorrect g) (x : TList Γ) {t : RTape}
    (ht : EagerBuilds g x t) (seed : TList (Γ ++ ss)) :
    ∃ out : Array Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t)
          (Algebra.TList.toAnyArray (α := ℝ) seed) = .ok out ∧
      ArrCorr ((fderiv ℝ (g.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ.length) := by
  obtain ⟨out, h1, h2⟩ := direct_PR_soundness_compiled g hg x seed
  exact ⟨out, (backwardDenseFrom_eager_eq_compiled ht seed).trans h1, h2⟩

/-- Pointwise-differentiability variant of `direct_PR_soundness_eager`. -/
theorem direct_PR_soundness_eager_at {Γ ss : List Shape}
    (g : Graph Γ ss) (x : TList Γ) (hg : GraphFDerivCorrectAt g (flattenCtx x)) {t : RTape}
    (ht : EagerBuilds g x t) (seed : TList (Γ ++ ss)) :
    ∃ out : Array Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t)
          (Algebra.TList.toAnyArray (α := ℝ) seed) = .ok out ∧
      ArrCorr ((fderiv ℝ (g.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ.length) := by
  obtain ⟨out, h1, h2⟩ := direct_PR_soundness_compiled_at g x hg seed
  exact ⟨out, (backwardDenseFrom_eager_eq_compiled ht seed).trans h1, h2⟩

end PRSim
