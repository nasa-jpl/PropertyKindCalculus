/-
`paradigm.tape_cse` — **common-subexpression elimination over a recorded tape** (WO3 (c),
the memoizing-tape stretch).

The thunk tape carrier (`paradigm.tape_carrier.TapeBuilder`) emits a *fresh* node every time a
sub-expression is named: the carrier is a deferred `TapeM` action, and running it re-emits the
whole sub-program at every reference. So a kernel like the whole `r_plrz` (`algorithm.dielectric_tape`)
rebuilds the shared ε prefix at every Fresnel reference and blows up to **hundreds of thousands**
of nodes (measured: ε′ 2 667, ε″ 1 335, r_plrz HH 342 079, VV 470 271 — for a kernel that is
morally ~150 distinct elementwise ops). That is value-correct but ruinous for "go fast": the
roofline/arithmetic-intensity analysis, and any eventual lowering to a fused CUDA kernel, want the
DAG of *distinct* sub-expressions, not its exponential unfolding.

**This pass recovers the DAG.** `cseCompact` hash-conses a recorded `Tape Float` by each node's
`(op-name, remapped-parent-ids, forward-value-bits)`: two nodes with the same op applied to the
same (already-canonicalised) inputs — equivalently, two builds of the same sub-expression — collapse
to one. It is **value-preserving** by construction: the canonical node keeps the stored forward
value the original node had, so the result read back is *bit-identical* to `runBuilder` (no
recomputation, no tolerance). Node COUNT shrinks; the result never moves. Because it touches only
the count, every `paradigm.tape_parity` theorem (`rPlrzTape_parity`, the `Evaluates` alphabet) holds
over the un-compacted carrier *unchanged* — CSE is orthogonal to parity, exactly as the carrier's
docstring promised.

**Soundness of the key.** The key would be unsafe only for an op that bakes a *scalar constant*
into the node (e.g. `scale`/`shift`/`clamp`-with-bounds), where two such nodes share `(name,
parents)` yet differ. The carrier's entire op alphabet is `const` (a value-keyed leaf) / `add` /
`sub` / `mul` / `div` / `min` / `max` / `exp` / `log` / `abs` / `sqrt` — every scalar enters as a
`const` *leaf* (keyed on its value), never baked into an op — so `(name, parents)` already
identifies each op node. We nonetheless fold the node's forward-value bits into the key for *every*
node, so the pass stays correct even if the carrier later grows a scalar-baking op: distinct values
⇒ distinct keys ⇒ never merged, while genuine duplicates (deterministic op, same inputs) carry
bit-identical values ⇒ still merged. Hence the collapse is exact common-subexpression elimination.

The one op family that *does* bake an identity into the node is the `LutInterp` vocabulary
extension (`paradigm.lut_carrier`): a recorded fetch is named `lutfetch:<table>`, so the table's
identity rides in the NAME component of the key and fetches into different tables never merge —
the hazard above, resolved by construction (witnessed by `examples.tape_codegen_lut`'s
`lutCseIdentity`). The obligation this shifts onto callers is that distinct tables carry distinct
names; `paradigm.tape_codegen`'s `gen` enforces it (`resolveTables` rejects duplicates).

Plain (not a `module`) file: imports the plain tape carrier.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeCarrier
public import Std.Data.HashMap

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open Spec TorchLean
open Runtime.Autograd
open PropertyKindCalculus.Paradigm (TapeBuilder)

namespace PropertyKindCalculus.Paradigm.TapeCSE

/-- The structural CSE key of a tape node: its op name, its parent ids *after* canonicalisation
(so duplicates of a shared input collapse before the node is keyed), and the bit pattern of its
stored forward value (disambiguates constant leaves, and bulletproofs the key against any future
scalar-baking op). Two nodes share a key iff they are the same op on the same canonical inputs. -/
def nodeKey (remap : Array Nat) (node : Node Float) : Option String × Array Nat × List UInt64 :=
  ( node.name
  , node.parents.map (fun p => remap.getD p p)
  , (TorchLean.Storage.toArray node.value.tensor.buffer).toList.map Float.toBits )

/-- **Hash-cons a recorded tape.** Walks the nodes in id order (parents precede children, so the
remap of every parent is already known), collapsing structurally-identical nodes onto one. Returns
the compacted tape and the `remap : oldId ↦ newId` array. Forward-value-preserving: each surviving
node carries the original's stored value, so reading any remapped id yields the original value. -/
def cseCompact (t : Tape Float) : Tape Float × Array Nat := Id.run do
  let mut newTape : Tape Float := Tape.empty
  let mut remap : Array Nat := Array.mkEmpty t.size
  let mut memo : Std.HashMap (Option String × Array Nat × List UInt64) Nat := {}
  for node in t.nodes do
    let key := nodeKey remap node
    match memo[key]? with
    | some nid =>
        remap := remap.push nid
    | none =>
        let remappedParents := node.parents.map (fun p => remap.getD p p)
        let (newTape', nid) := newTape.addNode { node with parents := remappedParents }
        newTape := newTape'
        memo := memo.insert key nid
        remap := remap.push nid
  pure (newTape, remap)

/-- Build a tape sub-program, CSE-compact it, and read back the result — returning the result
tensor, the **raw** node count (the carrier's unfolded emission), and the **compacted** node count
(the distinct sub-expressions). The tensor is bit-identical to `runBuilder b` (CSE preserves every
stored forward value); only the count shrinks. -/
def runBuilderCSE {s : Shape} (b : TapeBuilder s) :
    Except String (Tensor Float s × Nat × Nat) := do
  let (id, t) ← TapeM.run Tape.empty b.run
  let (t', remap) := cseCompact t
  let v ← Tape.requireValue (t := t') (s := s) (remap.getD id id)
  pure (v, Tape.size t, Tape.size t')

end PropertyKindCalculus.Paradigm.TapeCSE

end -- pkc-blanket-expose
end -- pkc-blanket
