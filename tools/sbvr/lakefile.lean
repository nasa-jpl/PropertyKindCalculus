import Lake
open Lake DSL

/-!
# `hcp-check-sbvr` — `hcp-check` with SBVR.lean in process (TOOLS.md §6 Q1)

A Lake package of its own, so that the root package's pull-request builds, which have no token
for the private SBVR.lean, never resolve this `require`; it is built by `scripts/hcp-check-sbvr.sh`
where the credentials are. The checker is the root package's `tools/Tools/HcpCheck.lean`, the same
module, compiled here against SBVR.lean: the chain is loaded, checked and each vocabulary rendered by
the library's own functions instead of a `sbvr-check` subprocess.
-/

package «pkc-sbvr-tools» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]
  requiresModuleSystem := true

-- SBVR.lean at the revision the ladder's renderings are regenerated at (HCP/sbvr/rendered/);
-- move the pin and the renderings together (`scripts/hcp-check-sbvr.sh --fix-sbvr`).
require SBVR from git
  "https://github.com/Open-MBEE/SBVR.lean" @ "4579362728bed7736d1ddfcdcca426704c95dc5f"

/-- The checker module itself, `../Tools/HcpCheck.lean`, not a copy. -/
lean_lib Tools where
  srcDir := ".."
  roots := #[`Tools.HcpCheck]

/-- `lake exe hcp-check-sbvr [--root DIR] [--fix-excerpts] [--fix-sbvr]`: `hcp-check --sbvr`, the
SBVR observations made in process. -/
@[default_target]
lean_exe «hcp-check-sbvr» where
  root := `HcpCheckSbvr
