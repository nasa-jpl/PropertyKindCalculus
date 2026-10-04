#!/usr/bin/env bash
# scripts/libtorch-cpu-sdk.sh — a CPU-only LibTorch SDK for the batched parity harnesses.
#
#   eval "$(scripts/libtorch-cpu-sdk.sh)"          # exports TORCHLEAN_LIBTORCH_CPU_HOME (+ installs once)
#   scripts/libtorch-cpu-sdk.sh --path             # print the SDK path only (installs if needed)
#
# `CudaT`'s device ops are `@[extern]` FFI into TorchLean's LibTorch bridge, and the default build
# links TorchLean's "unavailable" backend, so `lake exe ssprc_batched_parity` cannot run at all
# from a plain build. The bridge from a CPU-only SDK runs those ops on the host through ATen's CPU
# kernels — no GPU, no CUDA toolkit — which is what makes the harnesses runnable on a hosted
# runner. The SDK is the `torch/` directory of the CPU pip wheel: this script creates a venv
# under $TORCHLEAN_SDK_DIR (default ~/.cache/torchlean-libtorch-cpu), installs the pinned wheel
# once, and prints the export line. Then:
#
#   lake build -R -K libtorch=true -K libtorch_home="$TORCHLEAN_LIBTORCH_CPU_HOME" \
#              -K torchlean_build_dir=.lake/build ssprc_batched_parity mcm_batched_parity
#   lake exe ssprc_batched_parity && lake exe mcm_batched_parity
#
# `-K torchlean_build_dir=.lake/build` keeps TorchLean in the tree the libraries were already
# built in (only the bridge is new); omit it on a machine that also builds the CUDA flavour, so
# each flavour keeps its own TorchLean tree. The wheel is ~750 MB and needs no toolkit; the
# version is pinned to the one TorchLean's bridge was validated against. `cmake` (>= 3.22) and a
# C++17 compiler must be on PATH for the bridge's build.
set -euo pipefail

TORCH_VERSION="${TORCHLEAN_TORCH_VERSION:-2.11.0}"
SDK_DIR="${TORCHLEAN_SDK_DIR:-$HOME/.cache/torchlean-libtorch-cpu}"
VENV="$SDK_DIR/venv-$TORCH_VERSION"

if [ ! -f "$VENV/.installed" ]; then
  python3 -m venv "$VENV" >&2
  "$VENV/bin/pip" install --quiet --index-url https://download.pytorch.org/whl/cpu "torch==$TORCH_VERSION" >&2
  touch "$VENV/.installed"
fi
home="$("$VENV/bin/python" -c 'import os, torch; print(os.path.dirname(torch.__file__))' 2>/dev/null)"
[ -f "$home/share/cmake/Torch/TorchConfig.cmake" ] || { echo "!! $home is not a LibTorch SDK" >&2; exit 1; }
[ -e "$home/lib/libtorch_cuda.so" ] && { echo "!! $home is a CUDA SDK, not the CPU-only wheel" >&2; exit 1; }

case "${1:-}" in
  --path) echo "$home" ;;
  *) echo "export TORCHLEAN_LIBTORCH_CPU_HOME=$home" ;;
esac
