#!/usr/bin/env bash
# Sign every attestation in the repository with one key.
#
# Why a script rather than three commands: `ampas_review.py sign` works on the
# catalogue AMPAS_CLAIMS selects, and the 13 claims live in three catalogues.
# Signing them by hand means three invocations, and forgetting one leaves those
# attestations signed by the previous key while reference/reviewer_key.json
# names the new one -- records verifiable against no committed key at all.
# tests/test_third_check.py fails on exactly that, but not doing it wrong is
# better than detecting it afterwards.
#
# This needs no Lean. Signing reads the frozen attestation records, signs them
# and writes them back; it touches neither the auditor nor a kernel. Only
# `verify` needs a toolchain, and CI runs that for you after you push.
#
# Usage:
#   scripts/sign_attestations.sh ~/.ampas/ampas-reviewer.pem kai-chang-2026-10
set -euo pipefail

KEY="${1:-}"
KEY_ID="${2:-}"
if [ -z "$KEY" ] || [ -z "$KEY_ID" ]; then
  echo "usage: $0 <private-key.pem> <key-id>" >&2
  exit 2
fi
if [ ! -f "$KEY" ]; then
  echo "no such private key: $KEY" >&2
  exit 2
fi

cd "$(dirname "$0")/.."

for cat in reference/claims.json \
           reference/claims_mathlib.json \
           reference/claims_fermat.json; do
  echo "== $cat"
  AMPAS_CLAIMS="$cat" python3 harness/ampas_review.py sign \
      --key "$KEY" --key-id "$KEY_ID"
done

echo
echo "== checking every attestation now carries one key id"
python3 -m pytest tests/test_third_check.py -q \
    -k "signed_by_the_one_recorded_key or claims_no_more_than_its_custody"

echo
echo "== refreshing SHA256SUMS"
python3 scripts/sha256sums.py

cat <<'NOTE'

Signed. What is NOT yet checked: that each signature verifies and that nothing
has drifted since freezing -- that needs Lean. Push, and CI re-verifies with
the toolchain. A green run means the signatures check out against the public
key you just committed.

Do not commit the private key. `git status` should show no .pem.
NOTE
