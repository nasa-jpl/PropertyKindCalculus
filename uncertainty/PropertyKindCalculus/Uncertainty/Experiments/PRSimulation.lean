/-
# A direct P↔R simulation for TorchLean reverse-mode AD — closed (Stage 3.6)

Historically a *spike* with five `sorry`s (committed 2026-07-31 as a recorded experiment);
now a sorry-free module, indexed in the `UncertaintyRigor` library. Typecheck standalone with:

    lake env lean uncertainty/PropertyKindCalculus/Uncertainty/Experiments/PRSimulation.lean

Goal: relate TorchLean's **runtime eager tape** (R) to the **fderiv proof model** (P) by a
simulation relation, *directly* — and say precisely which parts of that relation are provable
without re-deriving the carrier-generic algebra bridge (A, `Runtime/Link/BackwardGraph.lean`).

Two worlds:

* **P** (`Proofs.Autograd`, ℝ-only, the fderiv model):
  - `Graph Γ ss`      (`Tape/Core/Soundness.lean`) snoc-list of typed nodes.
  - `Graph.evalVec` / `Graph.backpropVec` (`Tape/Core/FDeriv.lean`), and
    `Graph.backpropVec_eq_adjoint_fderiv` : reverse mode = `(fderiv ℝ evalVec x).adjoint`.
* **R** (`Runtime.Autograd`, carrier-generic eager engine):
  - `SomeTensor α` shape-erased values; `Node α` with an *opaque* `backward` closure
    (`SomeTensor α → Result (List (Nat × SomeTensor α))`); `Tape α = Array (Node α)`.
  - total reverse pass `backwardDenseFrom{,Loop,Step}` (`Engine/Core/Backward.lean`).

How the five original obligations closed (Stage 3.6, ordered per `UNCERTAINTY.md` §6):

1. `mulSpec_vecToTensor` / `addSpec_vecToTensor` (§2) — PROVEN, by `Shape` induction through the
   pointwise lemma `tensorToVec_map2Spec_apply` (using upstream `tensorToVec_dim_apply`).
2. `backwardDenseFrom_ok` (§6) — PROVEN, with one *statement refinement*: the original
   statement assumed only `ForwardSim`, which pins the tape's stored **values** but says
   nothing about the opaque `backward` **closures** the reverse pass runs; a tape with correct
   forward values and a closure `fun _ => .error …` refutes the unrefined claim. The honest
   hypothesis is `BackwardShapeWF` (§5): every closure is *shape-total*. Under it, the
   "every slot carries its node's shape" invariant (`AccShapeAligned`) threads through the
   fold, value-free — and §6 also shows the eager constructors `Tape.leaf`/`add`/`mul`
   *provide* `BackwardShapeWF`, so the hypothesis is discharged on eagerly built tapes.
3. `sim_backward_step` — RETIRED to documentation (§5): its `.ok`-and-invariant half is
   `backwardDenseFromStep_ok`; its per-step *value* half is exactly the `addGradAll`
   fold-commutation the A-bridge already proves (`BackwardGraph.lean`, `haddGradAllPush`
   and neighbours), and re-deriving it against P would duplicate those ~800 lines.
4. `direct_PR_soundness` — CLOSED as `direct_PR_soundness_compiled` (§7): for a *compiled*
   tape it is the `Γ`-prefix projection of the Stage-3.5 endpoint
   `backwardDenseFrom_lowerGraphToTape_adjoint_fderiv` (`Runtime/Link/FDeriv.lean`), transported
   to this file's `ArrCorr` phrasing by `getRaw_flattenCtx` (§1) and
   `toAnyArray_extract_takeLeft` (§7). For an *arbitrary* `ForwardSim` tape the statement is
   unprovable for the same reason as (2) — `ForwardSim` does not pin the closures. For the
   tapes the eager constructors actually build, that closure provenance is supplied by
   `Experiments/EagerProvenance.lean` (`EagerBuilds` / `direct_PR_soundness_eager`).

What this file does *not* do, by design: re-derive any `addGradAll` value commutation against
P. The adjoint mathematics enters exactly once, through the Stage-3.5 bridge.
-/

import NN.Proofs.Autograd.Tape.Nodes.Arithmetic
import NN.Proofs.Autograd.Runtime.Link.FDeriv
import NN.Runtime.Autograd.Engine.Core

open Spec Tensor Proofs.Autograd TorchLean

noncomputable section

namespace PRSim

-- R-side abbreviations (kept qualified to avoid `Node`/`Tape` clashes with P's `Proofs.Autograd`).
abbrev Any    := Spec.SomeTensor ℝ
abbrev RTape  := Runtime.Autograd.Tape ℝ
abbrev RNode  := Runtime.Autograd.Node ℝ
abbrev Res    := Runtime.Autograd.Result
@[reducible] def mkAny {s : Shape} (t : Tensor ℝ s) : Any := Spec.SomeTensor.ofTensor t

/-- Elementwise (Hadamard) product on Euclidean coordinate vectors — P's `mul`-node kernel. -/
def hadamardVec {n : Nat} (u v : Vec n) : Vec n := vecOfFun (n := n) (fun i => u i * v i)

/- ===========================================================================================
   §1.  The id ↔ context-slot correspondence, and the FORWARD simulation relation.

   R's tape is a *flat* `Array (Node ℝ)`: the `Γ.length` leaves are *also* nodes (with
   `backward = fun _ => .ok []`), followed by `ss.length` computed nodes.  P splits inputs `Γ`
   from intermediates `ss`.  We line up: R node id `i`  ↔  P context slot `i` of `Γ ++ ss`.
   =========================================================================================== -/

/-- The shape-erased value P assigns to context slot `i` of `Γ ++ ss` at input `xV`:
    read block `i` out of `evalVec g xV`, un-vectorize, then erase the shape. -/
def ctxSlotValue {Γ ss : List Shape} (g : Graph Γ ss) (xV : CtxVec Γ)
    (i : Fin (Γ ++ ss).length) : Any :=
  mkAny (vecToTensor (s := (Γ ++ ss).get i) (CtxVec.getBlock (Γ := Γ ++ ss) i (g.evalVec xV)))

/-- **Forward simulation relation.**  The runtime tape `t` realises the P graph `g` at input `xV`:
    it has one node per context slot and every stored value is the corresponding `evalVec` block
    (shapes included, since `ctxSlotValue` carries `(Γ ++ ss).get i`). -/
def ForwardSim {Γ ss : List Shape} (g : Graph Γ ss) (xV : CtxVec Γ) (t : RTape) : Prop :=
  t.nodes.size = (Γ ++ ss).length ∧
  ∀ i : Fin (Γ ++ ss).length, t.getValue? i.val = some (ctxSlotValue g xV i)

/-- Block-read of a flattened context: `getBlock` inverts `flattenCtx` entrywise.  This is the
    coordinate bridge between P's `CtxVec` reads and the typed `TensorPack` entries. -/
theorem getRaw_flattenCtx :
    ∀ {Γ : List Shape} (xs : TorchLean.TensorPack ℝ Γ) (i : Fin Γ.length),
      CtxVec.getBlock (Γ := Γ) i (flattenCtx xs)
        = tensorToVec (t := TorchLean.TensorPack.get (α := ℝ) xs i)
  | s :: Γ, .cons x xs, ⟨0, h0⟩ => by
      show CtxVec.getBlock (Γ := s :: Γ) ⟨0, h0⟩ (flattenCtx (TensorPack.cons x xs)) = tensorToVec (t := x)
      ext j
      simp [CtxVec.getBlock, flattenCtx, Fin.append, Fin.addCases]
  | s :: Γ, .cons x xs, ⟨Nat.succ k, hk⟩ => by
      have htail :
          (vecOfFun (n := ctxSize Γ) fun j =>
              flattenCtx (Γ := s :: Γ) (TensorPack.cons x xs) (Fin.natAdd (Spec.Shape.size s) j))
            = flattenCtx (Γ := Γ) xs := by
        ext j
        simp [flattenCtx, Fin.append_right]
      show CtxVec.getBlock (Γ := Γ) ⟨k, Nat.lt_of_succ_lt_succ hk⟩
          (vecOfFun (n := ctxSize Γ) fun j =>
            flattenCtx (Γ := s :: Γ) (TensorPack.cons x xs) (Fin.natAdd (Spec.Shape.size s) j))
          = tensorToVec (t := TorchLean.TensorPack.get (α := ℝ) xs ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
      rw [htail]
      exact getRaw_flattenCtx xs ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Option-form of the upstream `get_toShapeErasedArray`: erased array lookup is the typed entry. -/
theorem toAnyArray_getElem? {ss : List Shape} (xs : TorchLean.TensorPack ℝ ss) (i : Fin ss.length) :
    (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) (ss := ss) xs)[i.val]?
      = some (mkAny (TorchLean.TensorPack.get (α := ℝ) xs i)) := by
  have hlt : i.val < (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) (ss := ss) xs).size := by
    simp
  rw [Array.getElem?_eq_getElem hlt]
  exact congrArg some (TorchLean.TensorPack.get_toShapeErasedArray (α := ℝ) (ss := ss) xs i)

/-- **`ForwardSim` is realised by compiled tapes**: `lowerGraphToTape` on the algebraic embedding of a
    P graph produces a tape forward-simulating that graph.  (So the simulation relation of this
    file is not hypothetical — the Stage-3.5 compile path inhabits it.) -/
theorem forwardSim_lowerGraphToTape {Γ ss : List Shape} (g : Graph Γ ss) (x : TorchLean.TensorPack ℝ Γ) :
    ForwardSim g (flattenCtx x)
      (Algebra.Graph.lowerGraphToTape (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss) g.toAlgebra x ()).1 := by
  have hsize :=
    Algebra.Graph.lowerGraphToTape_nodes_size (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss) g.toAlgebra x ()
  have hvals :=
    Algebra.Graph.lowerGraphToTape_values_eq (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss) g.toAlgebra x ()
  have hctx :=
    Algebra.Graph.lowerGraphToTape_ctx_eq_eval (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss) g.toAlgebra x ()
  have heval : Algebra.Graph.eval (α := ℝ) (Δ := Unit) g.toAlgebra x () = Graph.eval g x := by
    rw [← Algebra.Graph.toReal_eval]
    simp
  refine ⟨by simp [hsize], ?_⟩
  intro i
  -- Read the stored value through `lowerGraphToTape_values_eq`.
  have hread :
      (Algebra.Graph.lowerGraphToTape (α := ℝ) (Δ := Unit) g.toAlgebra x ()).1.getValue? i.val
        = (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) (ss := Γ ++ ss) (Graph.eval g x))[i.val]? := by
    have hmap :
        ((Algebra.Graph.lowerGraphToTape (α := ℝ) (Δ := Unit) g.toAlgebra x ()).1.nodes.map
            (fun node => node.value))[i.val]?
          = (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) (ss := Γ ++ ss) (Graph.eval g x))[i.val]? := by
      rw [hvals, hctx, heval]
    simpa [Runtime.Autograd.Tape.getValue?, Runtime.Autograd.Tape.getNode?,
      Array.getElem?_map] using hmap
  rw [hread, toAnyArray_getElem?]
  -- Both sides are the erased `i`-th entry of `eval g x`.
  unfold ctxSlotValue
  rw [Graph.evalVec_flattenCtx, getRaw_flattenCtx, vecToTensor_tensorToVec]

/- ===========================================================================================
   §2.  VECTORIZATION HOMOMORPHISMS  (pure, no `SomeTensor`) — the two cheap obligations, CLOSED.

   Both forward agreement and the per-op backward *value* agreement (§4) reduce to these two
   facts: `mulSpec`/`addSpec` (elementwise tensor ops, R's forward/backward kernels) commute with
   `vecToTensor`/`tensorToVec` (P's vectorization).  Proven by induction on `Shape` through the pointwise
   characterization `tensorToVec_dim_apply` (`Tape/Core/FDeriv.lean`).
   =========================================================================================== -/

/-- `tensorToVec` on scalar tensors always returns the scalar value (the only coordinate is `0`). -/
lemma tensorToVec_scalar_apply (x : ℝ) (i : Fin (Spec.Shape.size Shape.scalar)) :
    tensorToVec (t := (Tensor.scalar x : Tensor ℝ Shape.scalar)) i = x :=
  tensorToVec_scalar x i

/-- Pointwise: `map2Spec f` acts coordinatewise under vectorization. -/
theorem tensorToVec_map2Spec_apply {f : ℝ → ℝ → ℝ} :
    ∀ {s : Shape} (a b : Tensor ℝ s) (i : Fin (Spec.Shape.size s)),
      tensorToVec (t := map2Spec f a b) i = f (tensorToVec (t := a) i) (tensorToVec (t := b) i)
  | .scalar, .scalar x, .scalar y, i => by
      simp only [map2Spec]
      rw [tensorToVec_scalar_apply, tensorToVec_scalar_apply, tensorToVec_scalar_apply]
  | .dim n s, .dim fa, .dim fb, i => by
      by_cases hm : Spec.Shape.size s = 0
      · exact absurd i.isLt (by simp [Spec.Shape.size, hm])
      · have hmpos : 0 < Spec.Shape.size s := Nat.pos_of_ne_zero hm
        obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective i
        have hstep : map2Spec f (Tensor.dim fa) (Tensor.dim fb)
            = Tensor.dim (fun j => map2Spec f (fa j) (fb j)) := rfl
        rw [hstep, tensorToVec_dim_apply hmpos, tensorToVec_dim_apply hmpos, tensorToVec_dim_apply hmpos]
        exact tensorToVec_map2Spec_apply (fa p.1) (fb p.1) p.2

/-- `mulSpec` is the Hadamard product under `tensorToVec`. -/
theorem tensorToVec_mulSpec {s : Shape} (a b : Tensor ℝ s) :
    tensorToVec (t := mulSpec a b) = hadamardVec (tensorToVec (t := a)) (tensorToVec (t := b)) := by
  have h : ∀ i, tensorToVec (t := mulSpec a b) i = tensorToVec (t := a) i * tensorToVec (t := b) i :=
    fun i => tensorToVec_map2Spec_apply (f := (· * ·)) a b i
  calc tensorToVec (t := mulSpec a b)
      = vecOfFun (fun i => tensorToVec (t := mulSpec a b) i) := (vecOfFun_eta _).symm
    _ = vecOfFun (fun i => tensorToVec (t := a) i * tensorToVec (t := b) i) :=
        congrArg (vecOfFun (n := Spec.Shape.size s)) (funext h)
    _ = hadamardVec (tensorToVec (t := a)) (tensorToVec (t := b)) := rfl

/-- `mulSpec` is the Hadamard product under vectorization.  (Original obligation, CLOSED.) -/
theorem mulSpec_vecToTensor {s : Shape} (u v : Vec s.size) :
    mulSpec (vecToTensor u) (vecToTensor v) = vecToTensor (hadamardVec u v) := by
  have h := congrArg (vecToTensor (s := s))
    (tensorToVec_mulSpec (vecToTensor (s := s) u) (vecToTensor (s := s) v))
  simpa using h

/-- `addSpec` is Euclidean `+` under vectorization.  (Original obligation, CLOSED — via the
    Stage-3.5 lemma `tensorToVec_addSpec`.) -/
theorem addSpec_vecToTensor {s : Shape} (u v : Vec s.size) :
    addSpec (vecToTensor u) (vecToTensor v) = vecToTensor (u + v) := by
  have h := congrArg (vecToTensor (s := s))
    (tensorToVec_addSpec (vecToTensor (s := s) u) (vecToTensor (s := s) v))
  simpa using h

/- ===========================================================================================
   §3.  Where the SHAPE-ERASURE bites, and the fact that it does NOT block a per-node statement.

   R's backward is `SomeTensor ℝ → Result (Array (Nat × SomeTensor ℝ))`.  The cotangent arrives
   shape-erased; the *only* dynamic check inside a per-op backward is `requireGrad`
   (`Engine/Core/Core.lean`), an `if h : dLdyAny.shape = τ`.  Against a cotangent that the
   simulation *mints* with the right shape (`mkAny δ`), that check discharges definitionally.

   Below are the verbatim `add`/`mul` backward closures (Elementwise.lean) and the
   proof that they evaluate to a concrete parent-contribution array.  THESE ARE PROVEN.
   Conclusion: "state R's backward = P's adjoint" is *not* blocked by `SomeTensor`
   at the per-node level. The erasure bites only in the *fold* (§5, `addGradAll`). -/

/-- The exact backward closure stored by the runtime `Tape.mul` node (Elementwise.lean). -/
def mulBackward {s : Shape} (a b : Tensor ℝ s) (aId bId : Nat) :
    Any → Res (Array (Nat × Any)) :=
  fun dLdyAny => do
    let dLdy ← Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := s) dLdyAny
    let da : Tensor ℝ s := mulSpec dLdy b
    let db : Tensor ℝ s := mulSpec dLdy a
    pure #[(aId, mkAny da), (bId, mkAny db)]

/-- The exact backward closure stored by the runtime `Tape.add` node (Elementwise.lean). -/
def addBackward {s : Shape} (aId bId : Nat) : Any → Res (Array (Nat × Any)) :=
  fun dLdyAny => do
    let dLdy ← Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := s) dLdyAny
    pure #[(aId, mkAny dLdy), (bId, mkAny dLdy)]

/-- `requireGrad` discharges on a minted cotangent (the shape check is `rfl`). PROVEN. -/
@[simp] theorem requireGrad_mkAny {s : Shape} (δ : Tensor ℝ s) :
    Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := s) (mkAny δ) = .ok δ := by
  simp [Runtime.Autograd.Tape.requireGrad, mkAny, Spec.SomeTensor.ofTensor]

/-- R's `mul` backward on a minted cotangent `δ` returns the product-rule contributions. PROVEN. -/
theorem mulBackward_mkAny {s : Shape} (a b δ : Tensor ℝ s) (aId bId : Nat) :
    mulBackward a b aId bId (mkAny δ)
      = .ok #[(aId, mkAny (mulSpec δ b)), (bId, mkAny (mulSpec δ a))] := by
  simp [mulBackward, Runtime.Autograd.Tape.requireGrad, mkAny, Spec.SomeTensor.ofTensor]

/-- R's `add` backward on a minted cotangent `δ` copies it to both parents. PROVEN. -/
theorem addBackward_mkAny {s : Shape} (δ : Tensor ℝ s) (aId bId : Nat) :
    addBackward (s := s) aId bId (mkAny δ)
      = .ok #[(aId, mkAny δ), (bId, mkAny δ)] := by
  simp [addBackward, Runtime.Autograd.Tape.requireGrad, mkAny, Spec.SomeTensor.ofTensor]

/- ===========================================================================================
   §4.  BACKWARD/ADJOINT agreement, per op — the *value* level.

   P's node VJP is a *full context update*; it unfolds definitionally (via `Node.vjpVec_ofFn`):
     (mul a b).vjpVec ctx δ = single a (δ ⊙ get b ctx) + single b (δ ⊙ get a ctx)     [PROVEN]
     (add a b).vjpVec ctx δ = single a δ            + single b δ                        [PROVEN]
   and `TapeNodes.mulFderiv`/`addFderiv` certify these equal the `fderiv` adjoint of the node's
   forward map.  R's backward (§3) produces the *same contributions* but keyed by parent id and
   shape-erased.  The per-parent VALUE agreement is exactly the §2 homomorphism (now proven, so
   `mul_contrib_agree` is closed).  Turning the parent-keyed list into P's `single _ + single _`
   is the *scatter*, and it lives in the fold (§5), not here. -/

/-- P's `mul` node VJP, definitional unfold.  PROVEN. -/
theorem p_mul_vjpVec {Γ : List Shape} {s : Shape} (a b : Idx Γ s)
    (ctxV : CtxVec Γ) (δV : Vec s.size) :
    (TapeNodes.mul (Γ := Γ) (s := s) a b).vjpVec ctxV δV
      = CtxVec.single a (hadamardVec δV (CtxVec.get b ctxV))
        + CtxVec.single b (hadamardVec δV (CtxVec.get a ctxV)) := by
  simp [TapeNodes.mul, Node.vjpVec_ofFn, hadamardVec]

/-- P's `add` node VJP, definitional unfold.  PROVEN. -/
theorem p_add_vjpVec {Γ : List Shape} {s : Shape} (a b : Idx Γ s)
    (ctxV : CtxVec Γ) (δV : Vec s.size) :
    (TapeNodes.add (Γ := Γ) (s := s) a b).vjpVec ctxV δV
      = CtxVec.single a δV + CtxVec.single b δV := by
  simp [TapeNodes.add, Node.vjpVec_ofFn]

/-- Per-parent VALUE agreement for `mul`: R's shape-erased contribution `mkAny (mulSpec δ v)` is
    the erasure of P's Hadamard block `δV ⊙ vV`.  CLOSED (was "proven mod §2"). -/
theorem mul_contrib_agree {s : Shape} (δV vV : Vec s.size) :
    mkAny (mulSpec (vecToTensor δV) (vecToTensor vV)) = mkAny (vecToTensor (hadamardVec δV vV)) := by
  rw [mulSpec_vecToTensor]

/-- Per-parent VALUE agreement for `add`.  Trivial (identity contribution).  PROVEN. -/
theorem add_contrib_agree {s : Shape} (δV : Vec s.size) :
    mkAny (vecToTensor δV) = mkAny (vecToTensor δV) := rfl

/- The `fderiv` endpoint these VJPs certify (imported, PROVEN upstream): the P node's `jvpVec` is
   the Fréchet derivative and its VJP is the adjoint. -/
example {Γ : List Shape} {s : Shape} (a b : Idx Γ s) :
    NodeFDerivCorrect (TapeNodes.mul (Γ := Γ) (s := s) a b) := TapeNodes.mulFderiv a b
example {Γ : List Shape} {s : Shape} (a b : Idx Γ s) :
    NodeFDerivCorrect (TapeNodes.add (Γ := Γ) (s := s) a b) := TapeNodes.addFderiv a b

/- ===========================================================================================
   §5.  The reverse pass as a FOLD INVARIANT — the shape-alignment half, PROVEN.

   R's total reverse pass is `backwardDenseFromLoop` over ids `n-1 … 0`, each step
   `backwardDenseFromStep` running `node.backward` then folding contributions through
   `addGradAll`.  `addGradAll` (`Engine/Core/Backward.lean`) is where the shape-erasure
   *actually* bites: per scattered contribution it performs nested dynamic checks/casts.

   The invariant "every accumulator slot has its node's shape" (`AccShapeAligned`) discharges
   every *shape* check.  What it cannot discharge is the closures themselves: `Node.backward`
   is opaque state, so totality additionally needs each closure to be *shape-total*
   (`BackwardShapeWF`) — succeed on a node-shaped cotangent and emit contributions that target
   existing parents at their shapes.  §6 shows the eager constructors provide exactly this.

   The per-step *value* commutation against P (the retired `sim_backward_step`) is
   deliberately NOT re-derived: it is the A-bridge's ~800-line `haddGradAllPush` argument
   (`BackwardGraph.lean:491-617`), and with Stage 3.5 landed its composed consequence is
   available as a theorem — see §7. -/

/-- A runtime gradient array realises a P cotangent context, blockwise (shapes included). -/
def ArrCorr {Γ' : List Shape} (v : CtxVec Γ') (arr : Array Any) : Prop :=
  arr.size = Γ'.length ∧
  ∀ i : Fin Γ'.length,
    arr[i.val]? = some (mkAny (vecToTensor (s := Γ'.get i) (CtxVec.getBlock (Γ := Γ') i v)))

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
    simp [Runtime.Autograd.Tape.getNode?, Array.getElem?_eq_none (Nat.le_of_not_lt hge)]
  simp [hnone] at h

/-- `SomeTensor.add` succeeds on equal shapes, and the sum keeps the left shape. -/
theorem anyAdd_ok_of_shape_eq (a b : Any) (h : a.shape = b.shape) :
    ∃ c : Any, Runtime.Autograd.SomeTensor.add a b = .ok c ∧ c.shape = a.shape := by
  refine ⟨⟨a.shape, addSpec a.tensor (Tensor.castShape b.tensor h.symm)⟩, ?_, rfl⟩
  simp [Runtime.Autograd.SomeTensor.add, h, Spec.SomeTensor.cast]

/-- One `addGradAll` accumulation preserves the shape-alignment invariant and succeeds,
    provided the contribution targets an existing node at that node's shape. -/
theorem addGradAll_ok (t : RTape) (acc : Array Any) (hacc : AccShapeAligned t acc)
    (pid : Nat) (g : Any) (pnode : RNode)
    (hp : t.getNode? pid = some pnode) (hs : g.shape = pnode.value.shape) :
    ∃ acc', Runtime.Autograd.Tape.addGradAll (t := t) acc pid g = .ok acc' ∧
      AccShapeAligned t acc' := by
  obtain ⟨hsize, hslots⟩ := hacc
  by_cases hreq : pnode.requiresGrad = false
  · refine ⟨acc, ?_, hsize, hslots⟩
    simp [Runtime.Autograd.Tape.addGradAll, hp, hreq, bind, Except.bind, pure, Except.pure]
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
        ⟨pnode.value.shape, Tensor.castShape (acc[pid]'hpid_acc).tensor hex⟩
        ⟨pnode.value.shape, Tensor.castShape g.tensor hs⟩ rfl
    refine ⟨acc.set pid summed hpid_acc, ?_, ?_, ?_⟩
    · simp [Runtime.Autograd.Tape.addGradAll, hp, hreq', hs, hex, hpid_acc,
        Spec.SomeTensor.cast, hsummed, bind, Except.bind, pure, Except.pure]
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
            (fun acc2 (pid, pg) => Runtime.Autograd.Tape.addGradAll (t := t) acc2 pid pg) acc
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
          (fun acc2 (pid, pg) => Runtime.Autograd.Tape.addGradAll (t := t) acc2 pid pg) acc
        = .ok acc' ∧ AccShapeAligned t acc' := by
  obtain ⟨acc', hfold, hacc'⟩ :=
    foldContribs_ok t contribs.toList acc hacc (fun q hq => htargets q (by simpa using hq))
  exact ⟨acc', by rwa [Array.foldlM_toList] at hfold, hacc'⟩

/-- One reverse step succeeds and preserves the invariant.  This is the surviving half of the
    retired `sim_backward_step` (the value half is §7's composed endpoint). -/
theorem backwardDenseFromStep_ok (t : RTape) (hwf : BackwardShapeWF t)
    (acc : Array Any) (hacc : AccShapeAligned t acc) (id : Nat) (hid : id < t.nodes.size) :
    ∃ acc', Runtime.Autograd.Tape.backwardDenseFromStep (t := t) acc id = .ok acc' ∧
      AccShapeAligned t acc' := by
  obtain ⟨hsize, hslots⟩ := hacc
  have hnode : t.getNode? id = some (t.nodes[id]'hid) := by
    simp [Runtime.Autograd.Tape.getNode?, Array.getElem?_eq_getElem hid]
  set node := t.nodes[id]'hid with hnode_def
  by_cases hreq : node.requiresGrad = false
  · refine ⟨acc, ?_, hsize, hslots⟩
    simp [Runtime.Autograd.Tape.backwardDenseFromStep, hnode, hreq,
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
      hwf id node hnode (Tensor.castShape g.tensor hshape)
    obtain ⟨acc', hfold, hacc'⟩ :=
      foldContribsArray_ok t contribs acc ⟨hsize, hslots⟩ htargets
    refine ⟨acc', ?_, hacc'⟩
    simp [Runtime.Autograd.Tape.backwardDenseFromStep, hnode, hreq', hg, hshape,
      Spec.SomeTensor.cast, hbackward, hfold, bind, Except.bind, pure, Except.pure]

/-- The reverse loop over the first `n` ids succeeds and preserves the invariant. -/
theorem backwardDenseFromLoop_ok (t : RTape) (hwf : BackwardShapeWF t) :
    ∀ (n : Nat), n ≤ t.nodes.size → ∀ acc, AccShapeAligned t acc →
      ∃ out, Runtime.Autograd.Tape.backwardDenseFromLoop (t := t) n acc = .ok out ∧
        AccShapeAligned t out
  | 0, _, acc, hacc => ⟨acc, rfl, hacc⟩
  | n + 1, hn, acc, hacc => by
      obtain ⟨acc', hstep, hacc'⟩ :=
        backwardDenseFromStep_ok t hwf acc hacc n (Nat.lt_of_succ_le hn)
      obtain ⟨out, hloop, hout⟩ :=
        backwardDenseFromLoop_ok t hwf n (Nat.le_of_succ_le hn) acc' hacc'
      exact ⟨out, by
        simp [Runtime.Autograd.Tape.backwardDenseFromLoop, hstep, hloop,
          bind, Except.bind], hout⟩

/- ===========================================================================================
   §6.  PARTIALITY — R returns `.ok`.  CLOSED (with the honest closure hypothesis).

   The original claim assumed only `ForwardSim`.  That is *not enough*: `ForwardSim` pins the
   tape's stored values, but the reverse pass runs the opaque `backward` closures, and a tape
   whose values are correct but whose closure is `fun _ => .error …` satisfies `ForwardSim`
   while refuting the claim.  The honest statement adds `BackwardShapeWF` — and the lemmas
   after the theorem show the eager runtime constructors (`Tape.leaf`/`Tape.add`/`Tape.mul`,
   the ops `Sensitivity.gradient`'s model class uses) provide it, so on eagerly built tapes the
   hypothesis is discharged constructor by constructor.  The `log`/`sqrt` value-domain side
   conditions live entirely on the P side (`NodeFDerivCorrectAt`); R never inspects values, so
   `.ok` is orthogonal to differentiability, as the spike predicted. -/

/-- `ForwardSim` + a seed realising some cotangent context give the fold invariant. -/
theorem accShapeAligned_of_sim {Γ ss : List Shape} {g : Graph Γ ss} {xV : CtxVec Γ}
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
    simp only [Runtime.Autograd.Tape.getValue?, hnode, Option.map_some] at hval
    exact Option.some.inj hval
  have hnode_s : node.value.shape = (Γ ++ ss).get ⟨i, hi⟩ := by
    rw [hvalue]; rfl
  -- The seed slot's shape is also the slot shape.
  have hslot : seedArr[i]? = some (mkAny (vecToTensor (s := (Γ ++ ss).get ⟨i, hi⟩)
      (CtxVec.getBlock (Γ := Γ ++ ss) ⟨i, hi⟩ seedFull))) := hslots ⟨i, hi⟩
  rw [hgi] at hslot
  have hgieq : gi = mkAny (vecToTensor (s := (Γ ++ ss).get ⟨i, hi⟩)
      (CtxVec.getBlock (Γ := Γ ++ ss) ⟨i, hi⟩ seedFull)) := Option.some.inj hslot
  rw [hgieq, hnode_s]
  rfl

/-- **The total reverse pass returns `.ok`** on a `ForwardSim`-well-formed tape with shape-total
    closures, from any seed realising a cotangent context.  (Original obligation, CLOSED with
    the `BackwardShapeWF` refinement; the invariant on the output comes for free.) -/
theorem backwardDenseFrom_ok
    {Γ ss : List Shape} (g : Graph Γ ss) (xV : CtxVec Γ)
    (t : RTape) (hsim : ForwardSim g xV t) (hwf : BackwardShapeWF t)
    (seedFull : CtxVec (Γ ++ ss)) (seedArr : Array Any) (hseed : ArrCorr seedFull seedArr) :
    ∃ out : Array Any, Runtime.Autograd.Tape.backwardDenseFrom (t := t) seedArr = .ok out ∧
      AccShapeAligned t out := by
  have hacc := accShapeAligned_of_sim hsim hseed
  obtain ⟨out, hloop, hout⟩ :=
    backwardDenseFromLoop_ok t hwf t.nodes.size (Nat.le_refl _) seedArr hacc
  refine ⟨out, ?_, hout⟩
  simp [Runtime.Autograd.Tape.backwardDenseFrom, hacc.1, hloop]

/- The eager constructors provide `BackwardShapeWF`, node by node. -/

/-- The empty tape is (vacuously) shape-total. -/
theorem backwardShapeWF_empty : BackwardShapeWF (Runtime.Autograd.Tape.empty (α := ℝ)) := by
  intro i node hnode
  simp [Runtime.Autograd.Tape.empty, Runtime.Autograd.Tape.getNode?] at hnode

/-- Pushing a node whose closure is shape-total w.r.tensor. the *old* tape preserves
    `BackwardShapeWF` (old closures never see the new id; targets persist under push). -/
theorem backwardShapeWF_addNode (t : RTape) (hwf : BackwardShapeWF t) (node : RNode)
    (hnode : ∀ d : Tensor ℝ node.value.shape,
      ∃ contribs, node.backward ⟨node.value.shape, d⟩ = .ok contribs ∧
        ∀ pc ∈ contribs, ∃ pnode : RNode,
          t.getNode? pc.1 = some pnode ∧ pc.2.shape = pnode.value.shape) :
    BackwardShapeWF (t.addNode node).1 := by
  -- `addNode` materializes the stored value, which is the identity on `SomeTensor`.
  have hpush : (t.addNode node).1.nodes = t.nodes.push node := by
    simp [Runtime.Autograd.Tape.addNode]
  have hmono : ∀ (j : Nat) (pnode : RNode), t.getNode? j = some pnode →
      (t.addNode node).1.getNode? j = some pnode := by
    intro j pnode hj
    have hjlt : j < t.nodes.size := lt_of_getNode?_eq_some hj
    have hj' : t.nodes[j]? = some pnode := hj
    have hval : t.nodes[j]'hjlt = pnode :=
      Option.some.inj ((Array.getElem?_eq_getElem hjlt).symm.trans hj')
    simp only [Runtime.Autograd.Tape.getNode?, hpush]
    rw [Array.getElem?_push_lt hjlt, hval]
  intro i inode hi d
  by_cases hilt : i < t.nodes.size
  · -- an old node: its closure and its targets are untouched
    have hi_old : t.getNode? i = some inode := by
      have h := hi
      simp only [Runtime.Autograd.Tape.getNode?, hpush] at h
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
      simp only [Runtime.Autograd.Tape.getNode?, hpush] at h
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
    BackwardShapeWF (Runtime.Autograd.Tape.leaf (α := ℝ) t v name rg).1 := by
  exact backwardShapeWF_addNode t hwf _ (fun d => ⟨#[], rfl, by simp⟩)

/-- A successful `requireValue` pins the target node's stored shape. -/
theorem requireValue_shape {s : Shape} (t : RTape) (id : Nat) (v : Tensor ℝ s)
    (h : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) id = .ok v) :
    ∃ pnode : RNode, t.getNode? id = some pnode ∧ pnode.value.shape = s := by
  cases hv : t.getValue? id with
  | none => simp [Runtime.Autograd.Tape.requireValue, hv] at h
  | some any =>
    by_cases hs : any.shape = s
    · cases hn : t.getNode? id with
      | none => simp [Runtime.Autograd.Tape.getValue?, hn] at hv
      | some pnode =>
        refine ⟨pnode, rfl, ?_⟩
        have hval : pnode.value = any := by
          simp only [Runtime.Autograd.Tape.getValue?, hn, Option.map_some] at hv
          exact Option.some.inj hv
        rw [hval, hs]
    · simp [Runtime.Autograd.Tape.requireValue, hv, hs] at h

/-- The eager `Tape.add` constructor preserves `BackwardShapeWF`: its closure copies the
    (node-shaped) cotangent to both parents, whose stored shapes `requireValue` has pinned. -/
theorem backwardShapeWF_add {s : Shape} (t : RTape) (hwf : BackwardShapeWF t)
    (aId bId : Nat) (t' : RTape) (id : Nat)
    (h : Runtime.Autograd.Tape.add (α := ℝ) (s := s) t aId bId = .ok (t', id)) :
    BackwardShapeWF t' := by
  cases hA : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) aId with
  | error e => simp [Runtime.Autograd.Tape.add, hA, bind, Except.bind] at h
  | ok a =>
  cases hB : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) bId with
  | error e => simp [Runtime.Autograd.Tape.add, hA, hB, bind, Except.bind] at h
  | ok b =>
  obtain ⟨pa, hpa, hpa_s⟩ := requireValue_shape t aId a hA
  obtain ⟨pb, hpb, hpb_s⟩ := requireValue_shape t bId b hB
  simp only [Runtime.Autograd.Tape.add, hA, hB, bind, Except.bind, pure, Except.pure] at h
  have hpair := Except.ok.inj h
  have ht' : t' = (t.addNode _).1 := (congrArg Prod.fst hpair).symm
  rw [ht']
  refine backwardShapeWF_addNode t hwf _ ?_
  intro d
  refine ⟨#[(aId, mkAny d), (bId, mkAny d)], ?_, ?_⟩
  · simp [Runtime.Autograd.Tape.requireGrad, mkAny, Spec.SomeTensor.ofTensor]
  · intro pc hpc
    have hpc' : pc = (aId, mkAny d) ∨ pc = (bId, mkAny d) := by simpa using hpc
    rcases hpc' with rfl | rfl
    · exact ⟨pa, hpa, by simp [mkAny, Spec.SomeTensor.ofTensor, hpa_s]⟩
    · exact ⟨pb, hpb, by simp [mkAny, Spec.SomeTensor.ofTensor, hpb_s]⟩

/-- The eager `Tape.mul` constructor preserves `BackwardShapeWF`: its product-rule closure
    emits node-shaped contributions to both parents. -/
theorem backwardShapeWF_mul {s : Shape} (t : RTape) (hwf : BackwardShapeWF t)
    (aId bId : Nat) (t' : RTape) (id : Nat)
    (h : Runtime.Autograd.Tape.mul (α := ℝ) (s := s) t aId bId = .ok (t', id)) :
    BackwardShapeWF t' := by
  cases hA : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) aId with
  | error e => simp [Runtime.Autograd.Tape.mul, hA, bind, Except.bind] at h
  | ok a =>
  cases hB : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) bId with
  | error e => simp [Runtime.Autograd.Tape.mul, hA, hB, bind, Except.bind] at h
  | ok b =>
  obtain ⟨pa, hpa, hpa_s⟩ := requireValue_shape t aId a hA
  obtain ⟨pb, hpb, hpb_s⟩ := requireValue_shape t bId b hB
  simp only [Runtime.Autograd.Tape.mul, hA, hB, bind, Except.bind, pure, Except.pure] at h
  have hpair := Except.ok.inj h
  have ht' : t' = (t.addNode _).1 := (congrArg Prod.fst hpair).symm
  rw [ht']
  refine backwardShapeWF_addNode t hwf _ ?_
  intro d
  refine ⟨#[(aId, mkAny (mulSpec d b)), (bId, mkAny (mulSpec d a))], ?_, ?_⟩
  · exact mulBackward_mkAny a b d aId bId
  · intro pc hpc
    have hpc' : pc = (aId, mkAny (mulSpec d b)) ∨ pc = (bId, mkAny (mulSpec d a)) := by
      simpa using hpc
    rcases hpc' with rfl | rfl
    · exact ⟨pa, hpa, by simp [mkAny, Spec.SomeTensor.ofTensor, hpa_s]⟩
    · exact ⟨pb, hpb, by simp [mkAny, Spec.SomeTensor.ofTensor, hpb_s]⟩

/- ===========================================================================================
   §7.  TOP-LEVEL COMPOSITION to `fderiv` — CLOSED for compiled tapes, via Stage 3.5.

   Chaining §5 over the graph would give: R's total `backwardDenseFrom`, projected onto the
   first `Γ.length` slots, equals P's `backpropVec` = `(fderiv ℝ evalVec).adjoint`.  We do NOT
   chain §5 (that would re-derive the A-bridge's fold argument).  Instead the composed value
   statement is the `Γ`-prefix projection of the Stage-3.5 endpoint
   `backwardDenseFrom_lowerGraphToTape_adjoint_fderiv`, transported into this file's `ArrCorr`
   phrasing.  The projection matters because P's `backpropVec` returns INPUT grads only while
   R retains a gradient per node — `Algebra.TensorPack.takeLeft` names the projection on the typed
   side, `Array.extract` on the runtime side, and the two commute with erasure (below).

   For an *arbitrary* tape known only through `ForwardSim`, the corresponding statement is
   unprovable — `ForwardSim` does not pin the backward closures, and a value-correct tape with
   junk closures is a countermodel.  For the tapes the eager constructors build, the closure
   provenance is supplied by `Experiments/EagerProvenance.lean`: `EagerBuilds` relates the
   runtime construction to the graph, and `direct_PR_soundness_eager` transfers this endpoint
   to the eager tape with no compilation involved. -/

/-- Erasure commutes with the input-prefix projection: extracting the first `Γ.length` runtime
    slots is erasing the typed `takeLeft`. -/
theorem toAnyArray_extract_takeLeft {Γ ss : List Shape} (w : TorchLean.TensorPack ℝ (Γ ++ ss)) :
    (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) (ss := Γ ++ ss) w).extract 0 Γ.length
      = TorchLean.TensorPack.toShapeErasedArray (α := ℝ) (ss := Γ)
          (Algebra.TensorPack.takeLeft (α := ℝ) (Γ := Γ) (ss := ss) w) := by
  have hlist : ∀ (Γ' : List Shape) (w' : TorchLean.TensorPack ℝ (Γ' ++ ss)),
      (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) (ss := Γ')
          (Algebra.TensorPack.takeLeft (α := ℝ) (Γ := Γ') (ss := ss) w')).toList
        = (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) (ss := Γ' ++ ss) w').toList.take Γ'.length := by
    intro Γ'
    induction Γ' with
    | nil => intro w'; simp [Algebra.TensorPack.takeLeft, TorchLean.TensorPack.toShapeErasedArray]
    | cons s Γ' ih =>
      intro w'
      cases w' with
      | cons x xs =>
        simp [Algebra.TensorPack.takeLeft, TorchLean.TensorPack.toShapeErasedArray, List.take_succ_cons, ih xs]
  apply Array.ext'
  simp [TorchLean.TensorPack.toShapeErasedArray, hlist Γ w]

/-- An erased typed context realises its own flattening (`ArrCorr` is inhabited by erasure). -/
theorem arrCorr_flattenCtx {Γ : List Shape} (u : TorchLean.TensorPack ℝ Γ) :
    ArrCorr (flattenCtx u) (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) (ss := Γ) u) := by
  refine ⟨by simp, ?_⟩
  intro i
  rw [toAnyArray_getElem?, getRaw_flattenCtx, vecToTensor_tensorToVec]

/-- **Runtime reverse pass on a compiled tape = `(fderiv ℝ evalVec x)†`, in `ArrCorr` form.**
    (The closure of the original `direct_PR_soundness`, for compiled tapes: a corollary of the
    Stage-3.5 endpoint; the `Γ`-prefix of the output array realises exactly the adjoint of the
    Fréchet derivative of the P graph's forward evaluation.) -/
theorem direct_PR_soundness_compiled {Γ ss : List Shape}
    (g : Graph Γ ss) (hg : GraphFDerivCorrect g) (x : TorchLean.TensorPack ℝ Γ) (seed : TorchLean.TensorPack ℝ (Γ ++ ss)) :
    ∃ out : Array Any,
      Runtime.Autograd.Tape.backwardDenseFrom
          (t := (Algebra.Graph.lowerGraphToTape (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
            g.toAlgebra x ()).1)
          (grads0 := TorchLean.TensorPack.toShapeErasedArray (α := ℝ) (ss := Γ ++ ss) seed)
        = .ok out ∧
      ArrCorr ((fderiv ℝ (g.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ.length) := by
  have hg' : GraphFDerivCorrect
      (Algebra.Graph.toReal (Δ := Unit) g.toAlgebra ()) := by simpa using hg
  obtain ⟨h1, h2⟩ :=
    Algebra.Graph.backwardDenseFrom_lowerGraphToTape_adjoint_fderiv (Δ := Unit)
      g.toAlgebra x () seed hg'
  refine ⟨_, h1, ?_⟩
  rw [toAnyArray_extract_takeLeft]
  have h2' : flattenCtx (Algebra.TensorPack.takeLeft
        (Algebra.Graph.backpropAllCtx (α := ℝ) (Δ := Unit) g.toAlgebra x () seed))
      = (fderiv ℝ (g.evalVec) (flattenCtx x)).adjoint (flattenCtx seed) := by
    simpa using h2
  rw [← h2']
  exact arrCorr_flattenCtx _

/-- The pointwise-differentiability variant (`GraphFDerivCorrectAt`), covering graphs with
    non-smooth primitives away from their kinks — same shape, via the `_at` Stage-3.5 endpoint. -/
theorem direct_PR_soundness_compiled_at {Γ ss : List Shape}
    (g : Graph Γ ss) (x : TorchLean.TensorPack ℝ Γ)
    (hg : GraphFDerivCorrectAt g (flattenCtx x)) (seed : TorchLean.TensorPack ℝ (Γ ++ ss)) :
    ∃ out : Array Any,
      Runtime.Autograd.Tape.backwardDenseFrom
          (t := (Algebra.Graph.lowerGraphToTape (α := ℝ) (Δ := Unit) (Γ := Γ) (ss := ss)
            g.toAlgebra x ()).1)
          (grads0 := TorchLean.TensorPack.toShapeErasedArray (α := ℝ) (ss := Γ ++ ss) seed)
        = .ok out ∧
      ArrCorr ((fderiv ℝ (g.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ.length) := by
  have hg' : GraphFDerivCorrectAt
      (Algebra.Graph.toReal (Δ := Unit) g.toAlgebra ()) (flattenCtx x) := by simpa using hg
  obtain ⟨h1, h2⟩ :=
    Algebra.Graph.backwardDenseFrom_lowerGraphToTape_adjoint_fderiv_at (Δ := Unit)
      g.toAlgebra x () seed hg'
  refine ⟨_, h1, ?_⟩
  rw [toAnyArray_extract_takeLeft]
  have h2' : flattenCtx (Algebra.TensorPack.takeLeft
        (Algebra.Graph.backpropAllCtx (α := ℝ) (Δ := Unit) g.toAlgebra x () seed))
      = (fderiv ℝ (g.evalVec) (flattenCtx x)).adjoint (flattenCtx seed) := by
    simpa using h2
  rw [← h2']
  exact arrCorr_flattenCtx _

end PRSim
