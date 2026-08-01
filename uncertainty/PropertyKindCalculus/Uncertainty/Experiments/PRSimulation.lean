/-
# SPIKE: a DIRECT P↔R simulation for TorchLean reverse-mode AD

This is a *scratch* file (not in any lakefile). Typecheck with:

    lake env lean uncertainty/PropertyKindCalculus/Uncertainty/Experiments/PRSimulation.lean

Goal: attempt to prove TorchLean's **runtime eager tape** (R) sound against Mathlib `fderiv`,
*directly*, by a simulation relation to the **fderiv proof model** (P), bypassing the existing
carrier-generic algebra bridge (A, `Runtime/Link/BackwardGraph.lean`).

Two worlds:

* **P** (`Proofs.Autograd`, ℝ-only, the fderiv model):
  - `Graph Γ ss`      (`Tape/Core/Soundness.lean:360`) snoc-list of typed nodes.
  - `Graph.evalVec`    (`Tape/Core/FDeriv.lean:747`)  : `CtxVec Γ → CtxVec (Γ ++ ss)`.
  - `Graph.backpropVec` (`Tape/Core/FDeriv.lean:777`) : returns input grads `CtxVec Γ` **only**.
  - `Graph.backpropVec_eq_adjoint_fderiv` (`…FDeriv.lean:1129`, needs `GraphFDerivCorrect g`)
        `backpropVec g x seed = (fderiv ℝ (evalVec g) x).adjoint seed`.
  - Per-op nodes authored on `CtxVec` via `Node.ofVec` with per-op fderiv proofs:
        `TapeNodes.add`/`TapeNodes.mul` (`Tape/Nodes/Arithmetic.lean:87,280`),
        `TapeNodes.addFderiv`/`mulFderiv` (`…:99,342`).

* **R** (`Runtime.Autograd`, carrier-generic eager engine):
  - `AnyTensor α = { s : Shape, t : Tensor α s }`  (`Runtime/Context.lean:44`), shape-**erased**.
  - `Node α`  (`Engine/Core/Core.lean:143`): `value : AnyTensor α`, `parents : List Nat`,
        `backward : AnyTensor α → Result (List (Nat × AnyTensor α))`  (opaque closure, `Except`).
  - `Tape α = { nodes : Array (Node α) }`.
  - per-op tape ctors `Tape.add`/`Tape.mul` (`Engine/Core/Elementwise.lean:30,65`).
  - reverse pass: `backwardScalar → backward → backwardDense` (`Engine/Core/Backward.lean:245,234,75`,
        a `foldlM` over `(range n).reverse` with reachability pruning), or the total, proof-friendly
        `backwardDenseFrom{,Loop,Step}` (`…Backward.lean:188,175,149`).

What compiles here vs. what is `sorry`:  see the section banners.  Every `sorry` is on a
**precisely-typed** statement so the remaining obligation is explicit.
-/

import NN.Proofs.Autograd.Tape.Nodes.Arithmetic
import NN.Runtime.Autograd.Engine.Core

open Spec Tensor Proofs.Autograd

noncomputable section

namespace PRSim

-- R-side abbreviations (kept qualified to avoid `Node`/`Tape` clashes with P's `Proofs.Autograd`).
abbrev Any    := Runtime.AnyTensor ℝ
abbrev RTape  := Runtime.Autograd.Tape ℝ
abbrev Res    := Runtime.Autograd.Result
@[reducible] def mkAny {s : Shape} (t : Tensor ℝ s) : Any := Runtime.Autograd.AnyTensor.mk t

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
  mkAny (ofVecT (s := (Γ ++ ss).get i) (CtxVec.getRaw (Γ := Γ ++ ss) i (g.evalVec xV)))

/-- **Forward simulation relation.**  The runtime tape `t` realises the P graph `g` at input `xV`:
    it has one node per context slot and every stored value is the corresponding `evalVec` block
    (shapes included, since `ctxSlotValue` carries `(Γ ++ ss).get i`). -/
def ForwardSim {Γ ss : List Shape} (g : Graph Γ ss) (xV : CtxVec Γ) (t : RTape) : Prop :=
  t.nodes.size = (Γ ++ ss).length ∧
  ∀ i : Fin (Γ ++ ss).length, t.getValue? i.val = some (ctxSlotValue g xV i)

/- ===========================================================================================
   §2.  The single "easy" bucket: VECTORIZATION HOMOMORPHISMS  (pure, no `AnyTensor`).

   Both forward agreement and the per-op backward *value* agreement (§4) reduce to these two
   facts: `mulSpec`/`addSpec` (elementwise tensor ops, R's forward/backward kernels) commute with
   `ofVecT`/`toVecT` (P's vectorization).  They are provable by induction on `Shape` exactly like
   `dot_eq_inner_toVecT` / `toVecT_get2` (`Tape/Nodes/Matrix.lean:59`); no runtime representation is
   involved.  Left as `sorry` here — they are the *cheap* remaining obligations. -/

/-- `mulSpec` is the Hadamard product under vectorization.  (⇐ `toVecT_get2`-style shape induction.) -/
theorem mulSpec_ofVecT {s : Shape} (u v : Vec s.size) :
    mulSpec (ofVecT u) (ofVecT v) = ofVecT (hadamardVec u v) := by
  sorry

/-- `addSpec` is Euclidean `+` under vectorization.  (⇐ shape induction; cf. `toVecT_add_spec_mat`.) -/
theorem addSpec_ofVecT {s : Shape} (u v : Vec s.size) :
    addSpec (ofVecT u) (ofVecT v) = ofVecT (u + v) := by
  sorry

/- ===========================================================================================
   §3.  Where the SHAPE-ERASURE bites, and the fact that it does NOT block a per-node statement.

   R's backward is `AnyTensor ℝ → Result (List (Nat × AnyTensor ℝ))`.  The cotangent arrives
   shape-erased; the *only* dynamic check inside a per-op backward is `requireGrad`
   (`Engine/Core/Core.lean:265`), an `if h : dLdyAny.s = τ`.  Against a cotangent that the
   simulation *mints* with the right shape (`mkAny δ`), that check discharges definitionally.

   Below are the verbatim `add`/`mul` backward closures (Elementwise.lean:40-42, 75-79) and the
   proof that they evaluate to a concrete parent-contribution list.  THESE ARE PROVEN (no `sorry`).
   Conclusion for the report: "state R's backward = P's adjoint" is *not* blocked by `AnyTensor`
   at the per-node level. The erasure bites only in the *fold* (§5, `addGradAll`). -/

/-- The exact backward closure stored by the runtime `Tape.mul` node (Elementwise.lean:75-79). -/
def mulBackward {s : Shape} (a b : Tensor ℝ s) (aId bId : Nat) :
    Any → Res (List (Nat × Any)) :=
  fun dLdyAny => do
    let dLdy ← Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := s) dLdyAny
    let da : Tensor ℝ s := mulSpec dLdy b
    let db : Tensor ℝ s := mulSpec dLdy a
    pure [(aId, mkAny da), (bId, mkAny db)]

/-- The exact backward closure stored by the runtime `Tape.add` node (Elementwise.lean:40-42). -/
def addBackward {s : Shape} (aId bId : Nat) : Any → Res (List (Nat × Any)) :=
  fun dLdyAny => do
    let dLdy ← Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := s) dLdyAny
    pure [(aId, mkAny dLdy), (bId, mkAny dLdy)]

/-- `requireGrad` discharges on a minted cotangent (the shape check is `rfl`). PROVEN. -/
@[simp] theorem requireGrad_mkAny {s : Shape} (δ : Tensor ℝ s) :
    Runtime.Autograd.Tape.requireGrad (α := ℝ) (τ := s) (mkAny δ) = .ok δ := by
  simp [Runtime.Autograd.Tape.requireGrad, mkAny, Runtime.Autograd.AnyTensor.mk, Tensor.castShape]

/-- R's `mul` backward on a minted cotangent `δ` returns the product-rule contributions. PROVEN. -/
theorem mulBackward_mkAny {s : Shape} (a b δ : Tensor ℝ s) (aId bId : Nat) :
    mulBackward a b aId bId (mkAny δ)
      = .ok [(aId, mkAny (mulSpec δ b)), (bId, mkAny (mulSpec δ a))] := by
  simp [mulBackward]

/-- R's `add` backward on a minted cotangent `δ` copies it to both parents. PROVEN. -/
theorem addBackward_mkAny {s : Shape} (δ : Tensor ℝ s) (aId bId : Nat) :
    addBackward (s := s) aId bId (mkAny δ)
      = .ok [(aId, mkAny δ), (bId, mkAny δ)] := by
  simp [addBackward]

/- ===========================================================================================
   §4.  BACKWARD/ADJOINT agreement, per op — the *value* level.

   P's node VJP is a *full context update*; it unfolds definitionally (via `Node.vjpVec_ofVec`):
     (mul a b).vjpVec ctx δ = single a (δ ⊙ get b ctx) + single b (δ ⊙ get a ctx)     [PROVEN]
     (add a b).vjpVec ctx δ = single a δ            + single b δ                        [PROVEN]
   and `TapeNodes.mulFderiv`/`addFderiv` certify these equal the `fderiv` adjoint of the node's
   forward map.  R's backward (§3) produces the *same contributions* but keyed by parent id and
   shape-erased.  The per-parent VALUE agreement is exactly the §2 homomorphism, so it is proven
   *modulo* §2 (`mul_contrib_agree` / `add_contrib_agree`).  What is NOT yet closed is turning the
   parent-keyed list into P's `single _ + single _` — that is the *scatter*, and it lives in the
   fold (§5), not here. -/

/-- P's `mul` node VJP, definitional unfold.  PROVEN. -/
theorem p_mul_vjpVec {Γ : List Shape} {s : Shape} (a b : Idx Γ s)
    (ctxV : CtxVec Γ) (δV : Vec s.size) :
    (TapeNodes.mul (Γ := Γ) (s := s) a b).vjpVec ctxV δV
      = CtxVec.single a (hadamardVec δV (CtxVec.get b ctxV))
        + CtxVec.single b (hadamardVec δV (CtxVec.get a ctxV)) := by
  simp [TapeNodes.mul, Node.vjpVec_ofVec, hadamardVec]

/-- P's `add` node VJP, definitional unfold.  PROVEN. -/
theorem p_add_vjpVec {Γ : List Shape} {s : Shape} (a b : Idx Γ s)
    (ctxV : CtxVec Γ) (δV : Vec s.size) :
    (TapeNodes.add (Γ := Γ) (s := s) a b).vjpVec ctxV δV
      = CtxVec.single a δV + CtxVec.single b δV := by
  simp [TapeNodes.add, Node.vjpVec_ofVec]

/-- Per-parent VALUE agreement for `mul`: R's shape-erased contribution `mkAny (mulSpec δ v)` is
    the erasure of P's Hadamard block `δV ⊙ vV`.  Reduces to §2 (`mulSpec_ofVecT`).  PROVEN mod §2. -/
theorem mul_contrib_agree {s : Shape} (δV vV : Vec s.size) :
    mkAny (mulSpec (ofVecT δV) (ofVecT vV)) = mkAny (ofVecT (hadamardVec δV vV)) := by
  rw [mulSpec_ofVecT]

/-- Per-parent VALUE agreement for `add`.  Trivial (identity contribution).  PROVEN. -/
theorem add_contrib_agree {s : Shape} (δV : Vec s.size) :
    mkAny (ofVecT δV) = mkAny (ofVecT δV) := rfl

/- The `fderiv` endpoint these VJPs certify (imported, PROVEN upstream): the P node's `jvpVec` is
   the Fréchet derivative and its VJP is the adjoint. -/
example {Γ : List Shape} {s : Shape} (a b : Idx Γ s) :
    NodeFDerivCorrect (TapeNodes.mul (Γ := Γ) (s := s) a b) := TapeNodes.mulFderiv a b
example {Γ : List Shape} {s : Shape} (a b : Idx Γ s) :
    NodeFDerivCorrect (TapeNodes.add (Γ := Γ) (s := s) a b) := TapeNodes.addFderiv a b

/- ===========================================================================================
   §5.  The reverse pass as a FOLD INVARIANT — the HARD obstacle (all `sorry`).

   R's total reverse pass is `backwardDenseFromLoop` over ids `n-1 … 0`, each step
   `backwardDenseFromStep` running `node.backward` then folding contributions through `addGradAll`.
   P's `backpropVec` is a structural recursion that, at each snoc node, does `seedPrev + node.vjp`.

   `addGradAll` (`Engine/Core/Backward.lean:113`) is where the shape-erasure *actually* bites:
   per scattered contribution it performs FOUR nested dynamic checks/casts —
     `node.requires_grad`,  `if h : g.s = node.value.s`,  `match grads[id]?`,
     `if hex : existing.s = node.value.s`,  `if hid : id < grads.size`.
   The simulation invariant "every array slot has its node's shape" discharges all of them, but
   only through a fold-commutation argument.  The existing A-bridge spends ~250 lines on exactly
   this (`BackwardGraph.lean:491-617`, `haddGradAllPush`).  We phrase the obligation as a relation
   between a runtime gradient `Array (AnyTensor ℝ)` and a P cotangent `CtxVec (Γ ++ ss)`. -/

/-- A runtime gradient array realises a P cotangent context, blockwise (shapes included). -/
def ArrCorr {Γ' : List Shape} (v : CtxVec Γ') (arr : Array Any) : Prop :=
  arr.size = Γ'.length ∧
  ∀ i : Fin Γ'.length,
    arr[i.val]? = some (mkAny (ofVecT (s := Γ'.get i) (CtxVec.getRaw (Γ := Γ') i v)))

/-- **One reverse step commutes (fold invariant).**  If `acc` realises the P cotangent context
    `seedFull`, then R's single step at the last id equals — under `ArrCorr` — P's snoc peel
    `seedPrev + node.vjp`.  This is the crux the direct route must reproduce; it is the fderiv-model
    analogue of `BackwardGraph.lean`'s `hstepLast`/`haddGradAllPush`.  OBLIGATION (sorry). -/
theorem sim_backward_step
    {Γ ss : List Shape} {τ : Shape}
    (g : Graph Γ ss) (node : Node (Γ ++ ss) τ) (xV : CtxVec Γ)
    (t : RTape) (hsim : ForwardSim (Graph.snoc g node) xV t)
    (seedFull : CtxVec ((Γ ++ ss) ++ [τ])) (acc : Array Any)
    (hacc : ArrCorr seedFull acc) :
    ∃ acc',
      Runtime.Autograd.Tape.backwardDenseFromStep (t := t) acc ((Γ ++ ss).length) = .ok acc' ∧
      -- `acc'` realises the P context after this node's VJP has been scattered/accumulated
      True := by
  sorry

/- ===========================================================================================
   §6.  PARTIALITY — does R return `.ok`?  (sorry, but the shape of the answer is settled.)

   Claim: for a `ForwardSim`-well-formed graph, every dynamic *shape* check in the reverse pass
   takes its matching branch, so `backwardDenseFrom` returns `.ok`.  Crucially this needs ONLY
   shape-alignment: the `log`/`sqrt` value-domain side conditions are on the *real values* and live
   entirely on the P side as `NodeFDerivCorrectAt` (`Tape/Core/FDeriv.lean:928`); R never inspects
   them (it totalises the derivative), so `.ok` is orthogonal to differentiability.  OBLIGATION. -/

theorem backwardDenseFrom_ok
    {Γ ss : List Shape} (g : Graph Γ ss) (xV : CtxVec Γ)
    (t : RTape) (hsim : ForwardSim g xV t)
    (seedFull : CtxVec (Γ ++ ss)) (seedArr : Array Any) (hseed : ArrCorr seedFull seedArr) :
    ∃ out : Array Any, Runtime.Autograd.Tape.backwardDenseFrom (t := t) seedArr = .ok out := by
  sorry

/- ===========================================================================================
   §7.  TOP-LEVEL COMPOSITION to `fderiv`.  (sorry, but the endpoint is the real theorem.)

   Chaining §5 over the graph gives:  R's total `backwardDenseFrom`, projected onto the first
   `Γ.length` slots, equals P's `backpropVec`, which (`backpropVec_eq_adjoint_fderiv`) equals
   `(fderiv ℝ evalVec).adjoint`.

   NOTE (a real mismatch worth naming): P's `backpropVec` returns `CtxVec Γ` — INPUT grads only;
   it folds intermediate cotangents into `seedPrev` and discards them.  R's `backwardDenseFrom`
   RETAINS a gradient for *every* node.  So the comparison must PROJECT R's output array onto the
   `Γ`-prefix.  (The dropped slots are the intermediate accumulated cotangents, computed identically
   along the way — but P's fderiv model gives no name for them, unlike A's `backpropAllCtx`.) -/

/-- Projection of a runtime gradient array onto the input (`Γ`-prefix) slots, as a P `CtxVec Γ`
    — assuming the array already realises some `CtxVec (Γ ++ ss)` we could just read it off; here we
    only need the *statement*, so we take the realised context as a hypothesis. -/
theorem direct_PR_soundness
    {Γ ss : List Shape} (g : Graph Γ ss) (hg : GraphFDerivCorrect g)
    (xV : CtxVec Γ) (t : RTape) (hsim : ForwardSim g xV t)
    (seedFull : CtxVec (Γ ++ ss)) (seedArr : Array Any) (hseed : ArrCorr seedFull seedArr) :
    ∃ (out : Array Any) (gInput : CtxVec Γ),
      Runtime.Autograd.Tape.backwardDenseFrom (t := t) seedArr = .ok out ∧
      -- the `Γ`-prefix of `out` realises `gInput`:
      ArrCorr gInput (out.extract 0 Γ.length) ∧
      -- …and `gInput` is exactly the `fderiv` adjoint (the imported P theorem):
      gInput = (fderiv ℝ (g.evalVec) xV).adjoint seedFull := by
  -- The last conjunct's RHS is `g.backpropVec xV seedFull` by `backpropVec_eq_adjoint_fderiv`;
  -- the first two are §6 + (§5 chained). We record the fderiv endpoint is genuinely available:
  have hfderiv : g.backpropVec xV seedFull = (fderiv ℝ (g.evalVec) xV).adjoint seedFull :=
    Graph.backpropVec_eq_adjoint_fderiv g hg xV seedFull
  sorry

end PRSim
