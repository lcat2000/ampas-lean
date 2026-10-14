#!/usr/bin/env bash
# Bootstrap the core tier: pinned Lean toolchain, trusted reference oleans,
# and the third check's provenance baseline. No Mathlib, no C toolchain, no
# network beyond elan's toolchain download.
#
#   ./scripts/bootstrap.sh
#
# Afterwards ./scripts/verify.sh runs the highest tier your machine supports.
set -euo pipefail
cd "$(dirname "$0")/.."
# `python3` does not exist in Git Bash on Windows -- the python.org installer
# ships python.exe and the py launcher. Pick whichever is there, so a reviewer
# on Windows is not stopped by the name of an interpreter.
PY=${PYTHON:-}
if [ -z "$PY" ]; then
  for c in python3 python py; do
    if command -v "$c" >/dev/null 2>&1; then PY=$c; break; fi
  done
fi
if [ -z "$PY" ]; then echo "no python interpreter found (tried python3, python, py)" >&2; exit 1; fi

ROOT=$PWD

say() { printf '\n== %s\n' "$*"; }

say "Lean toolchain"
if ! command -v lake >/dev/null 2>&1; then
  if ! command -v elan >/dev/null 2>&1; then
    echo "elan not found. Install it, then re-run:"
    echo "  Linux/macOS: curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y"
    echo '               source "$HOME/.elan/env"'
    echo "  Windows:     curl -O --location https://elan.lean-lang.org/elan-init.ps1"
    echo "               powershell -ExecutionPolicy Bypass -f elan-init.ps1"
    exit 1
  fi
fi
# lean-toolchain pins the version; elan honours it from this directory
lean --version
echo "toolchain pinned by ./lean-toolchain: $(cat lean-toolchain)"

say "Trusted reference (reference/AmpasRef)"
# One `sorry` warning per frozen statement is expected: the reference
# statements are deliberately unproved. They are the statements a submission
# must prove.
lake build AmpasRef
TRUSTED="$ROOT/.lake/build/lib/lean"
test -f "$TRUSTED/AmpasRef/Guards.olean"
echo "trusted oleans: $TRUSTED"

say "Auditor"
# Optional. The driver falls back to `lean --run harness/Audit.lean`, which
# needs no C toolchain and is about 3x slower. Linking fails outright on some
# Lean distributions (see docs/build-notes.md), so a failure here is not fatal.
if lake build audit 2>/dev/null; then
  cp -f .lake/build/bin/audit harness/audit
  echo "compiled auditor: harness/audit"
else
  echo "could not link the auditor executable; the driver will interpret"
  echo "harness/Audit.lean instead (slower, same results). See docs/build-notes.md."
fi

say "Third-check provenance baseline"
# Regenerated locally on purpose. The committed copy is the artifact of the
# reference run; if yours differs, your toolchain built different oleans and
# that is worth knowing before you read any verdict.
mkdir -p build
LEAN_PATH="$TRUSTED" "$PY" harness/make_baseline.py \
  build/kernel_baseline.json AmpasRef.Guards AmpasRef.Challenge
if cmp -s build/kernel_baseline.json reference/kernel_baseline.json; then
  echo "baseline matches the committed reference-run baseline"
else
  echo "NOTE: your baseline differs from reference/kernel_baseline.json."
  echo "      Expected if your toolchain is not the pinned one. The verify"
  echo "      script uses YOURS; declarations outside it are reported as"
  echo "      introduced assumptions rather than silently trusted."
fi

say "Done"
cat <<EOF
Next:
  ./scripts/verify.sh                 run every tier this machine supports
  ./scripts/build-lean4lean.sh        add the second kernel (tier 2)
  ./scripts/build-mathlib-tier.sh     add the Mathlib claims (tier 3, ~20 min)
EOF
