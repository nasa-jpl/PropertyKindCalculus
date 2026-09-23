/-
`examples.tape_codegen_lut` — **the lookup-table vocabulary extension, recorded → CSE'd →
codegen'd → landed**, on a small fully-decidable fixture.

`paradigm.lut_carrier`'s `LutInterp` extends the write-once vocabulary with a table fetch the
branchless `NumCarrier` alphabet cannot express; `paradigm.tape_codegen` lowers the recorded
`lutfetch:<table>` nodes to texture-object fetches (point mode: two point fetches + a
contraction-blocked fp32 lerp, bit-reproducible; hardware mode: one filtered fetch, 9-bit-weight
tolerance). This module certifies the extension end to end on a mixed arithmetic+fetch model:

* **recorder faithfulness** (computational): the recorded fetch node *stores* exactly the `Float`
  instance's value (`LutTable.refFetch` of the leaf values) — `#guard lutRecorderFaithful`;
* **re-interpretation faithfulness** (computational): `evalTapeT` at the recording environment
  reproduces the `Float`-instance model — `#guard lutEvalFaithful`;
* **the per-op step law** (`cOpT_lutfetch`, sorry-free): on any `lutfetch` name that resolves, the
  extended alphabet computes `LutTable.refFetch` — the alphabet entry the rendered
  `tl_lutfetch` device/stub helpers realise;
* **CSE table identity** (computational): two fetches into the *same* table at the same operands
  collapse, fetches into *different* tables do not (`#guard lutCseIdentity`) — the table name
  riding in the node name is exactly what `paradigm.tape_cse`'s `nodeKey` needs, resolving its
  scalar-baking hazard by construction;
* **landing well-formedness** (computational): `gen` with tables succeeds; launcher/kernel/stub
  arities agree (`inputs + tables + 2`); the CUDA TU bakes the table data, creates the texture
  once, and fetches through `tex1DLayered` (`__f*_rn` lerp in point mode, no ALU lerp in hardware
  mode); the stub TU passes the baked array — `#guard lutLandingHolds`.

The `∀`-environment lift of the two computational faithfulness checks — the `FaithfulT` bridge
and its capstone `lut_kernel_faithful` — lives in `examples.tape_codegen_lut_end_to_end`.

EXACTNESS SPLIT (stated once, load-bearing): every bit-exact claim here — and the recorded stored
values, and `evalTapeT` — is the **point-mode** semantics (`LutTable.refFetch`). Hardware-filtered
deployments carry a documented per-fetch tolerance `≤ 2⁻⁸·|Δsample|` (CUDA's 9-bit fixed-point
lerp weight, rounding unspecified) and are excluded from bit-exact claims by construction.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeCodegen
meta import PropertyKindCalculus.Torch.Paradigm.TapeCodegen

@[expose] public section Blanket

open Spec TorchLean
open Runtime.Autograd (Tape TapeM)
open PropertyKindCalculus.Paradigm (TapeBuilder NumCarrier LutTable LutInterp lutNodeName?)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)
open PropertyKindCalculus.Paradigm.TapeCodegen

namespace PropertyKindCalculus.Examples.TapeCodegenLut

/-! ### The fixture: a small layered table and a mixed arithmetic+fetch model -/

/-- 2 layers × 5 samples, non-uniform gaps (so the lerp is non-trivial). -/
def demoLut : LutTable :=
  { name := "demolut", width := 5, layers := 2
  , values := #[0.0, 0.5, 2.0, 4.5, 8.0,  10.0, 9.0, 7.0, 4.0, 0.0] }

/-- A second table with different content — the CSE-identity foil. -/
def demoLut2 : LutTable :=
  { name := "demolut2", width := 5, layers := 2
  , values := #[1.0, 1.5, 3.0, 5.5, 9.0,  11.0, 10.0, 8.0, 5.0, 1.0] }

/-- Written once over BOTH classes: the fetch plus ordinary arithmetic. The `[LutInterp α]`
context is the point — the model's dependence on tabulated data is visible in its type. -/
def lutModel {α : Type} [NumCarrier α] [LutInterp α] (layer u bias : α) : α :=
  LutInterp.lutFetch demoLut layer u + bias * bias

/-! ### Record at the tape carrier (meaningful leaf values, so the stored values are checkable) -/

abbrev TB := TapeBuilder Shape.scalar

/-- A named input leaf carrying a concrete recording value. -/
def inLeafV (nm : String) (v : Float) : TB :=
  ⟨TapeM.leaf (Tensor.full Shape.scalar v) (name := some nm)⟩

def envLayer : Float := 1.0
def envU     : Float := 2.25
def envBias  : Float := 0.5

/-- The recorded tape and its output id. -/
def lutRecord : Except String (Tape Float × Nat) := do
  let prog : TB := lutModel (inLeafV "layer" envLayer) (inLeafV "u" envU) (inLeafV "bias" envBias)
  let (id, t) ← TapeM.run Tape.empty prog.run
  pure (t, id)

/-- The `Float`-instance oracle: `refFetch 1 2.25` on row 1 `[10,9,7,4,0]` is `7 + 0.25·(4−7) =
6.25`, plus `0.5²` — `6.5`. -/
def oracle : Float := lutModel (α := Float) envLayer envU envBias

def recordEnv : String → Float := fun nm =>
  if nm == "layer" then envLayer else if nm == "u" then envU else envBias

def demoTables : String → Option LutTable := fun tn =>
  if tn == demoLut.name then some demoLut else none

/-- Recorder faithfulness, computationally: the output node's STORED value is bit-identical to the
`Float`-instance model at the recording inputs (the `TapeBuilder` instance stores the elementwise
`refFetch` by construction). -/
def lutRecorderFaithful : Bool :=
  match lutRecord with
  | .error _ => false
  | .ok (t, id) =>
    match t.getNode? id with
    | some n => (nodeScalar n).toBits == oracle.toBits
    | none => false

#guard lutRecorderFaithful

/-- Re-interpretation faithfulness, computationally: `evalTapeT` (the table-extended fp64
reference — the generated kernel's denotation) at the recording environment reproduces the
`Float`-instance model bit-for-bit. -/
def lutEvalFaithful : Bool :=
  match lutRecord with
  | .error _ => false
  | .ok (t, id) =>
    match evalTapeT demoTables recordEnv t with
    | .ok vals => (vals.getD id 0.0).toBits == oracle.toBits
    | .error _ => false

#guard lutEvalFaithful

/-! ### The per-op step law — the alphabet entry the rendered helpers realise -/

/-- On any node name that resolves to a table, the extended alphabet computes exactly
`LutTable.refFetch` — the fp64 point-mode semantics the CUDA/stub `tl_lutfetch` helpers
implement. -/
theorem cOpT_lutfetch {nm tn : String} (hn : lutNodeName? nm = some tn)
    (tables : String → Option LutTable) (tbl : LutTable) (ht : tables tn = some tbl)
    (l u : Float) :
    cOpT tables nm [l, u] = .ok (tbl.refFetch l u) := by
  simp only [cOpT, hn, ht]

/-! ### CSE table identity — the node name carries the table, so `nodeKey` distinguishes tables -/

/-- Two fetches into the SAME table at the same operands hash-cons to one node; fetches into
DIFFERENT tables at the same operands do not (their node names differ). Raw shapes: 7 nodes
(2×2 leaves + 2 fetches + add) → 4 after CSE when the tables coincide, 5 when they differ. -/
def lutCseIdentity : Bool :=
  let rec2 (tbl2 : LutTable) : Except String (Tape Float × Nat) := do
    let l := inLeafV "layer" envLayer
    let u := inLeafV "u" envU
    let prog : TB := LutInterp.lutFetch demoLut l u + LutInterp.lutFetch tbl2 l u
    let (id, t) ← TapeM.run Tape.empty prog.run
    pure (t, id)
  match rec2 demoLut, rec2 demoLut2 with
  | .ok (tSame, _), .ok (tDiff, _) =>
    (cseCompact tSame).1.nodes.size == 4 && (cseCompact tDiff).1.nodes.size == 5
  | _, _ => false

#guard lutCseIdentity

/-! ### Landing well-formedness with tables -/

def hasSub (s sub : String) : Bool := decide (1 < (s.splitOn sub).length)

/-- `gen` with the table succeeds; both filter modes emit well-formed landing TUs: arities agree
(`inputs + tables + 2`), the CUDA TU bakes the data + creates the texture once + fetches through
`tex1DLayered` (contraction-blocked lerp in point mode, none in hardware mode), the stub TU passes
the baked array behind the same launcher symbol. -/
def lutLandingHolds : Bool :=
  match lutRecord with
  | .error _ => false
  | .ok (t, id) =>
    match gen t [id] #[demoLut] .point, gen t [id] #[demoLut] .hardware with
    | .ok cgP, .ok cgH =>
      let cuP := emitCudaLanding "lut_demo" cgP
      let stP := emitStubLanding "lut_demo" cgP
      let cuH := emitCudaLanding "lut_demo" cgH
      (launchArgList cgP).length == (kernelParamList cgP).length
        && (stubParamList cgP).length == (kernelParamList cgP).length
        && (launchArgList cgP).length == cgP.inputs.size + cgP.tables.size + 2
        && cgP.tables.size == 1
        && hasSub cuP "static const float lut_demolut_data[10]"
        && hasSub cuP "tl_get_tex_demolut"
        && hasSub cuP "tex1DLayered<float>"
        && hasSub cuP "__fmul_rn"                 -- point mode: explicit lerp
        && hasSub cuP "cudaFilterModePoint"
        && hasSub cuH "cudaFilterModeLinear"      -- hardware mode: filtered fetch,
        && !(hasSub cuH "__fmul_rn")              -- no ALU lerp
        && hasSub stP "static const float lut_demolut_data[10]"
        && hasSub stP "lut_demo_launch"
        && hasSub cuP "lut_demo_launch"
        && hasSub stP "TL_LUTFETCH"
    | _, _ => false

#guard lutLandingHolds

/-- `gen` without the table is a hard error (an unresolved fetch cannot silently degrade). -/
def lutMissingTableRejected : Bool :=
  match lutRecord with
  | .error _ => false
  | .ok (t, id) =>
    match gen t [id] with
    | .error _ => true
    | .ok _ => false

#guard lutMissingTableRejected

/-! ## Axiom audit — sorry-free, standard axioms only. -/

/-- info: 'PropertyKindCalculus.Examples.TapeCodegenLut.cOpT_lutfetch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cOpT_lutfetch

/-- info: 'PropertyKindCalculus.Paradigm.TapeCodegen.evalTapeT_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PropertyKindCalculus.Paradigm.TapeCodegen.evalTapeT_none

end PropertyKindCalculus.Examples.TapeCodegenLut

end Blanket
