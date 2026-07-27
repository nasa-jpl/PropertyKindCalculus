/-
# Torch-tier validation probes — index

The TorchLean-backed validation probes: the kind layer over the `Torch` library's
batched-carrier machinery (the fused forms). Kept in its own tier because it is the one
tier that reaches the `Torch` library's `Paradigm` modules; the probes drive a host stub
carrier, so they build and evaluate without a GPU.
-/

import PropertyKindCalculus.Tests.Torch.FusedKinds
