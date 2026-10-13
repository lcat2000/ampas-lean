#!/usr/bin/env bash
# Tier 2: a second, independently written Lean kernel.
#
# lean4lean (Mario Carneiro) is a from-scratch reimplementation of Lean's
# kernel in Lean, positioned upstream as an external checker. It checks
# inductive declarations, and it documents its deliberate divergences from
# the C++ kernel in its own divergences.md. Certification in this suite
# requires BOTH Lean kernels to accept a submission.
#
# Pinned to the revision the reference run used (reference/lean4lean_pin.json).
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
PIN=$(python3 -c "import json;print(json.load(open('reference/lean4lean_pin.json'))['revision'])")
REPO=$(python3 -c "import json;print(json.load(open('reference/lean4lean_pin.json'))['repo'])")

mkdir -p build
cd build
if [ ! -d lean4lean ]; then
  git clone "$REPO" lean4lean
fi
cd lean4lean
git fetch --all --tags
git checkout "$PIN"
echo "lean4lean at $(git rev-parse HEAD)"

# lean4lean declares its own toolchain; it is built with the toolchain it
# declares, not this suite's, and the reference run recorded the difference.
lake build lean4lean || {
  cat <<'EOF'

The link step failed. On some Lean distributions the C compiler or library
paths recorded in the toolchain are wrong (a conda build records placeholder
paths). harness/relink.py links the executable with the system compiler
against the system gmp/libuv/openssl; see docs/build-notes.md.
EOF
  exit 1
}
echo
echo "built: $ROOT/build/lean4lean/.lake/build/bin/lean4lean"
echo "./scripts/verify.sh will pick it up automatically."
