/-
# Validation probes — `runSharded`'s stitch and its column contract

Value probes for the CPU sharding driver (`PropertyKindCalculus.Torch.Paradigm.BatchCarrier`),
driven by host kernels on `FloatArray` columns so they evaluate without a device:

  * a well-formed kernel's per-chunk outputs are stitched back in pixel order, across an
    uneven split (`total % nChunks ≠ 0`) and for the inline `nChunks ≤ 1` path alike;
  * a kernel that returns the wrong number of output columns is REFUSED at the driver, with
    the chunk and both counts in the error — never stitched into an empty column — on the
    sharded and the inline path alike.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.BatchCarrier
meta import PropertyKindCalculus.Torch.Paradigm.BatchCarrier

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.BatchCarrier

open PropertyKindCalculus.Paradigm (runSharded)

/-- The pixel column `0, 1, …, n-1`. -/
def iota (n : Nat) : FloatArray := Id.run do
  let mut r := FloatArray.emptyWithCapacity n
  for i in [0:n] do r := r.push i.toFloat
  return r

/-- A row-independent two-output kernel: `(x, 2x)` per pixel. -/
def doubleK (_len : Nat) (cols : Array FloatArray) : IO (Array FloatArray) :=
  pure #[cols[0]!, ⟨cols[0]!.data.map (2.0 * ·)⟩]

/-- A kernel that breaks the contract: one column where `nOut = 2` are owed. -/
def shortK (_len : Nat) (cols : Array FloatArray) : IO (Array FloatArray) :=
  pure #[cols[0]!]

-- Three uneven chunks (2, 2, 1) of five pixels stitch back in order.
/-- info: #[#[0.000000, 1.000000, 2.000000, 3.000000, 4.000000], #[0.000000, 2.000000, 4.000000, 6.000000, 8.000000]] -/
#guard_msgs in
#eval do
  let outs ← runSharded 3 5 2 #[iota 5] doubleK
  return outs.map FloatArray.data

-- The inline path (`nChunks ≤ 1`) is the same stitch.
/-- info: #[#[0.000000, 1.000000, 2.000000, 3.000000, 4.000000], #[0.000000, 2.000000, 4.000000, 6.000000, 8.000000]] -/
#guard_msgs in
#eval do
  let outs ← runSharded 1 5 2 #[iota 5] doubleK
  return outs.map FloatArray.data

-- A short kernel is refused at the driver with the chunk and both counts.
/-- error: runSharded: chunk 0 of 3 returned 1 output columns, expected 2 -/
#guard_msgs in
#eval do
  let outs ← runSharded 3 5 2 #[iota 5] shortK
  return outs.map FloatArray.data

-- The inline path refuses the same kernel: it is chunk 0 of 1.
/-- error: runSharded: chunk 0 of 1 returned 1 output columns, expected 2 -/
#guard_msgs in
#eval do
  let outs ← runSharded 1 5 2 #[iota 5] shortK
  return outs.map FloatArray.data

end PropertyKindCalculus.Tests.BatchCarrier

end Blanket
