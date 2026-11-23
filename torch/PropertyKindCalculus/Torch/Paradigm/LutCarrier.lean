/-
`paradigm.lut_carrier` — **`LutInterp`, the lookup-table vocabulary-EXTENSION class**: piecewise-
linear interpolation into a named, host-resident, layered 1-D table over a uniform abscissa.

WHY A NEW CLASS AND NOT A FUSED FORM. `FusedExp` (`paradigm.batch_carrier`) is a *fused form*: a
bit-exact single-op refinement of a hot sub-expression the base `[NumCarrier]` vocabulary can
already compose. A table lookup is different in kind: a data-dependent *gather* is inexpressible
in the branchless `NumCarrier` alphabet (no indexing, no comparison-to-`Bool`), so there is no
composed fallback to refine — `LutInterp` genuinely EXTENDS the vocabulary. A model that uses it
must carry `[LutInterp α]` in its instance context, so the dependence on tabulated data is visible
in the model's type — the sharpened form of the textbook's "was the look-up table an accelerator?"
verdict: the LUT can enter the verified write-once story, but only by explicit vocabulary
extension, and (in hardware-filtered deployments) only up to a stated tolerance.

SEMANTICS (the coordinate-convention SSOT lives downstream in the science model; this class fixes
the FETCH semantics). A `LutTable` holds `layers × width` float samples, layer-major, over a
uniform abscissa in grid coordinates `[0, width−1]`. `lutFetch tbl layer u` clamps `u` into
`[0, width−1]`, selects the (integral-valued, clamped) `layer`, and linearly interpolates between
the two neighbouring samples — the uniform-grid analogue of `np.interp`, and exactly what one
`tex1DLayered`-backed fetch computes on a GPU (point mode: bit-reproducibly in fp32; hardware
filter mode: up to the 9-bit-weight tolerance) and what the LibTorch lookup computes.

INSTANCES.
* `Float` — `LutTable.refFetch`, the fp64 reference/oracle (the `evalTapeT` denotation).
* `TapeBuilder s` — records ONE tape node `name := "lutfetch:<tbl.name>"`, `parents :=
  [layerId, uId]`, storing the elementwise `refFetch` of the parents' stored tensors. Forward-only
  (`requiresGrad := false`, empty backward). The table's identity travels in the node NAME, so
  `paradigm.tape_cse`'s `nodeKey` (which keys on the name) distinguishes fetches into different
  tables with no CSE change — the "scalar-baking op" hazard its docstring warns about is resolved
  by construction, PROVIDED distinct tables carry distinct names (the codegen rejects duplicates).
* Device — `LutTable.fetchProgram`, the fetch as a TorchLean `Kernel.Program Float32` over three
  inputs (layers, coordinates, samples). `Program.run` evaluates it in Lean on the CPU and as
  generated CUDA on the GPU, and `CudaT.lutFetchIO` runs it on resident device buffers. Running a
  kernel is an `IO` action, so `CudaT` has no pure `LutInterp` instance. Throughput deployments
  land the megakernel (`paradigm.tape_codegen`), whose generated launcher caches the texture.

A `module` file: imports the tape carrier, the CUDA carrier, and TorchLean's kernel frontend.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeCarrier
public import PropertyKindCalculus.Torch.Paradigm.CudaCarrier
public import TorchLean.NN.Kernel.Tensor
public import TorchLean.CUDA.Kernel.Launch
import TorchLean.CUDA.Kernel.Elab

@[expose] public section Blanket

open TorchLean TorchLean.Tensor
open TorchLean.LibTorch (Buffer)
open scoped Kernel

namespace PropertyKindCalculus.Paradigm

/-- A named, host-resident, layered 1-D lookup table over a uniform abscissa in grid coordinates
`[0, width−1]`. `name` is the table's codegen identity — it enters recorded node names, CSE keys,
and generated kernel parameter names — so distinct tables MUST carry distinct names
(`paradigm.tape_codegen`'s `gen` rejects duplicates). `values` is `layers·width` samples,
layer-major (`values[l·width + i]`). -/
structure LutTable where
  name   : String
  width  : Nat
  layers : Nat
  values : Array Float
deriving Inhabited, Repr

namespace LutTable

/-- The fp64 reference semantics of one fetch: clamp `u` to `[0, width−1]`, clamp the
integral-valued `layer` to `[0, layers−1]`, floor, and linearly interpolate — the uniform-grid
analogue of `np.interp`, and the `evalTapeT` denotation of a recorded `lutfetch` node. A NaN
coordinate or layer gives NaN for nonempty tables, as `min`/`max` and `clamp` propagate it. The deployed fp32 kernels (point mode) compute exactly this
in float32. -/
def refFetch (tbl : LutTable) (layer u : Float) : Float :=
  if tbl.width == 0 || tbl.layers == 0 then 0.0
  else if layer.isNaN || u.isNaN then layer + u
  else Id.run do
    let wmax := Float.ofNat (tbl.width - 1)
    let uc := max 0.0 (min wmax u)
    let lmax := Float.ofNat (tbl.layers - 1)
    let lc := max 0.0 (min lmax (layer + 0.5))
    let L := lc.toUInt64.toNat
    let j := uc.floor
    let f := uc - j
    let j0 := j.toUInt64.toNat
    let j1 := if j0 + 1 < tbl.width then j0 + 1 else tbl.width - 1
    let a := tbl.values[L * tbl.width + j0]!
    let b := tbl.values[L * tbl.width + j1]!
    return a + f * (b - a)

/-- The recorded node name carrying the table's identity: `lutfetch:<name>`. -/
def nodeName (tbl : LutTable) : String := s!"lutfetch:{tbl.name}"

end LutTable

/-- Recover the table name from a recorded `lutfetch:<name>` node name (`none` for every other
op) — how `paradigm.tape_codegen` recognises fetch nodes. -/
def lutNodeName? (nm : String) : Option String :=
  if nm.startsWith "lutfetch:" then some (nm.drop "lutfetch:".length).toString else none

/-- **The lookup-table vocabulary extension.** `lutFetch tbl layer u` = piecewise-linear
interpolation into `tbl` at grid coordinate `u`, in the layer selected by the integral-valued
`layer`. Unlike the `NumCarrier` alphabet this is a data-dependent gather; a model using it
carries `[LutInterp α]` explicitly. -/
class LutInterp (α : Type) where
  lutFetch : LutTable → α → α → α

/-- The fp64 reference instance — the oracle every deployment of the fetch is validated
against. -/
instance : LutInterp Float where
  lutFetch := LutTable.refFetch

/-- The recording action of one fetch — the `TapeBuilder` instance's body, named so the
end-to-end bridge (`examples.tape_codegen_lut_end_to_end`) can unfold its run: append one
`lutfetch:<name>` node whose stored value is the elementwise `refFetch` of the parents' stored
tensors. -/
def TapeBuilder.lutFetchM {s : Shape} (tbl : LutTable) (l u : TapeBuilder s) : TapeBuilder s :=
  ⟨do
    let lId ← l.run
    let uId ← u.run
    let t ← get
    let lVal : Tensor Float s ← liftM (TorchLean.Tape.requireValue (t := t) (s := s) lId)
    let uVal : Tensor Float s ← liftM (TorchLean.Tape.requireValue (t := t) (s := s) uId)
    let v := Tensor.zipWith (fun a b => tbl.refFetch a b) lVal uVal
    let (t', id) := Tape.addNode t
      { name := some tbl.nodeName
      , value := SomeTensor.ofTensor v
      , requiresGrad := false
      , parents := #[lId, uId]
      , backward := fun _ => .ok #[] }
    set t'
    pure id⟩

/-- The recording instance: one tape node per fetch, table identity in the node name, stored
value = elementwise `refFetch` of the parents' stored tensors (so recorder faithfulness is by
construction), forward-only. -/
instance {s : Shape} : LutInterp (TapeBuilder s) where
  lutFetch := TapeBuilder.lutFetchM

/-- **The fetch as a kernel**: `refFetch`'s float32 twin over inputs `0` (layers), `1`
(coordinates) and `2` (the `layers·width` samples, layer-major), for a nonempty table. A NaN
layer or coordinate gives NaN. -/
def LutTable.fetchProgram (width layers : UInt64) : Kernel.Program Float32 :=
  Program.of (fun (read : Kernel.Reader Float32) (i : UInt64) => (do
    let layer ← read 0 i
    let u ← read 1 i
    if layer ≤ layer then
      if u ≤ u then do
        let l := (layer + 0.5).toUInt64
        -- `over = 1` exactly when `l ≥ layers`, so `base` is row `min l (layers - 1)`.
        let over := 1 - 1 / (l / layers + 1)
        let base := (l - over * (l - (layers - 1))) * width
        -- Every branch interpolates, as `refFetch` does, so a NaN or infinite sample reaches the
        -- result at weight zero too.
        if (width - 1).toFloat32 ≤ u then do
          let a ← read 2 (base + (width - 1))
          pure (a + 0 * (a - a))
        else do
          let k := u.toUInt64
          -- `last = 1` exactly when `k + 1 ≥ width`, so `b` is sample `min (k + 1) (width - 1)`.
          let last := 1 - 1 / ((k + 1) / width + 1)
          let a ← read 2 (base + k)
          let b ← read 2 (base + (k + 1 - last))
          if u ≤ k.toFloat32 then
            -- Weight zero: `refFetch`'s `a + 0 * (b - a)` without forming `b - a`, which can
            -- overflow float32. `z` is `0` for finite samples and NaN otherwise.
            let z := (b - b) + (a - a)
            if a ≤ b then pure (a + z) else pure (a - z)
          else pure (a + (u - k.toFloat32) * (b - a))
      else pure (layer + u)
    else pure (layer + u) : Except Kernel.Error Float32))

/-- The device program of a table; meaningful when the table is nonempty. -/
def LutTable.program (tbl : LutTable) : Kernel.Program Float32 :=
  LutTable.fetchProgram tbl.width.toUInt64 tbl.layers.toUInt64

/-- One layered fetch on resident device buffers, through `LutTable.program` as generated CUDA.
The table upload is per call. An empty table reads as `0`, as `refFetch` does. -/
def CudaCarrier.CudaT.lutFetchIO {s : Shape} (tbl : LutTable)
    (layer u : CudaCarrier.CudaT s) : IO (CudaCarrier.CudaT s) := do
  if tbl.width == 0 || tbl.layers == 0 then return CudaCarrier.CudaT.const 0.0
  let fa := tbl.values.foldl (init := FloatArray.emptyWithCapacity tbl.values.size)
    FloatArray.push
  let table ← Buffer.ofFloatArrayIO fa
  let p := tbl.program
  let out ← Kernel.runBuffers .binary32 (fun x => (p.scalar.toBits x).toNat.toUInt64)
    p.expression #[layer.buf, u.buf, table] (Shape.size s).toUInt64
  return ⟨out⟩


end PropertyKindCalculus.Paradigm

end Blanket
