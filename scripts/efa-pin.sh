# The commit of Open-MBEE/engineering-foundation-architecture this repository reads: its Foundation
# vocabulary (scripts/foundation-vocabulary.sh → HCP/sbvr/foundation.yaml) and its HCP assurance gate
# (scripts/hcp-assurance.sh → `lake exe hcp-gate`, built in .lake/efa). One pin, so the vocabulary and the gate that
# judges the chain built on it move together. Sourced, not run.
EFA_COMMIT="${EFA_COMMIT:-5a35feb26b1c2174c19caeff0e02280e8bef7856}"
EFA_REPO=https://github.com/Open-MBEE/engineering-foundation-architecture
