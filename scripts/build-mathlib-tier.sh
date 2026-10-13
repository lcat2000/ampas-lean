#!/usr/bin/env bash
# Tier 3: the Mathlib-backed claims.
#
# Builds Mathlib at the pinned revision FROM SOURCE. On two cores this takes
# roughly 20 minutes for the dependency cone this suite needs; it is not the
# whole of Mathlib.
#
# `lake exe cache get` would be far faster where it works. The reference run
# could not use it (the cache host was reachable but served an archive format
# the pinned toolchain's `leantar` could not read), so the recorded run is a
# from-source build and reference/mathlib_pin.json says so. Try the cache
# first; falling back to source changes nothing about the result.
set -euo pipefail
cd "$(dirname "$0")/../mathlib-tier"

echo "== resolving dependencies at the pinned revisions"
lake update -R 2>/dev/null || lake update
python3 ../scripts/check_mathlib_pin.py

echo "== trying the prebuilt cache"
if lake exe cache get 2>/dev/null; then
  echo "cache used"
else
  echo "cache unavailable; building from source (~20 min on two cores)"
fi

echo "== building"
lake build AmpasRefMathlib
echo
echo "built: $(pwd)/.lake/build/lib/lean/AmpasRef/ChallengeMathlib.olean"
echo "./scripts/verify.sh will now run tier 3."
