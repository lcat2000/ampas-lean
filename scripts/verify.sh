#!/usr/bin/env bash
# Run the highest tier this machine supports and report what was actually
# checked. Every tier is self-contained: a failure in a higher tier never
# makes a lower tier's result less valid, and the script says which tiers ran.
#
#   ./scripts/verify.sh            every tier available
#   ./scripts/verify.sh 0          just the offline tier (no Lean needed)
#   ./scripts/verify.sh 1          offline + core-kernel tier
#
# Tiers
#   0  no Lean.    The third check's scope tests against fixed forgery
#                  exports, and the integrity of the JSON records.
#   1  Lean only.  The 16-submission core corpus through compile, kernel
#                  replay, the third check and the auditor; the formalization
#                  sign-off and its drift detection.
#   2  + lean4lean A second, independently written kernel re-checks the same
#                  oleans. Certification requires both Lean kernels.
#   3  + Mathlib   The Mathlib-backed claim and the external validation pair
#                  (Fermat 1640 / Euler 1732).
set -uo pipefail
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
WANT=${1:-9}
FAILED=0
RAN=""

say()  { printf '\n\033[1m== %s\033[0m\n' "$*"; }
note() { printf '   %s\n' "$*"; }
run()  { if "$@"; then return 0; else FAILED=1; return 1; fi; }

export AMPAS_THIRD_CHECK=1
TRUSTED="$ROOT/.lake/build/lib/lean"
[ -f "$ROOT/build/kernel_baseline.json" ] \
  && export AMPAS_KERNEL_BASELINE="$ROOT/build/kernel_baseline.json"

# ---------------------------------------------------------------- tier 0
say "Tier 0 — offline (no Lean required)"
note "the third check's scope, pinned against fixed forgery exports"
run "$PY" -m pytest tests/test_third_check.py -q -k "not pipeline" && RAN="$RAN 0"

[ "$WANT" -lt 1 ] && { say "Stopping at tier $WANT"; exit $FAILED; }

# ---------------------------------------------------------------- tier 1
if ! command -v lean >/dev/null 2>&1; then
  say "Tier 1 skipped — no lean on PATH"
  note "run ./scripts/bootstrap.sh first"
  exit $FAILED
fi
if [ ! -f "$TRUSTED/AmpasRef/Guards.olean" ]; then
  say "Tier 1 skipped — trusted reference not built"
  note "run ./scripts/bootstrap.sh first"
  exit $FAILED
fi

export AMPAS_TRUSTED_OLEAN="$TRUSTED"
say "Tier 1 — core corpus and the formalization sign-off"
note "16 submissions: 4 genuine, 12 attacks"
mkdir -p build
run "$PY" harness/ampas_lean.py corpus/manifest.json \
      --out build/corpus_core.json >/dev/null \
  && run "$PY" scripts/check_expectations.py build/corpus_core.json
note "which layer caught each attack"
run "$PY" harness/ablation.py build/corpus_core.json --out build/ablation.json >/dev/null \
  && "$PY" -c "
import json
rows = json.load(open('build/ablation.json'))
for r in rows:
    print(f\"     {r['attack']:28}{r['verdict']:9} {', '.join(r['signals'])}\")"
note "sign-off, guards and drift detection"
run "$PY" harness/ampas_review.py verify --out build/review_verification.json
note "bounded counterexample search against the frozen statements (reproduces reference/counterexample_search.json)"
run "$PY" harness/counterexample.py --out build/counterexample_search.json
note "bounded derivation search: PL-BOGUS must be refuted, and the kernel must accept the witness"
run "$PY" harness/derivation_search.py --out build/derivation_search.json
note "triangulation: each equivalence must relate the two statements on record (ASSUMPTIONS A1d for what that is worth)"
run "$PY" harness/triangulate.py --out build/triangulation.json
run "$PY" -m pytest tests/test_math_verification.py tests/test_review_drift.py \
      tests/test_third_check.py tests/test_counterexample.py tests/test_derivation_search.py \
      tests/test_triangulation.py tests/test_portability.py -q
RAN="$RAN 1"

[ "$WANT" -lt 2 ] && { say "Stopping at tier $WANT"; exit $FAILED; }

# ---------------------------------------------------------------- tier 2
L4L=${AMPAS_LEAN4LEAN:-$ROOT/build/lean4lean/.lake/build/bin/lean4lean}
if [ -x "$L4L" ]; then
  export AMPAS_LEAN4LEAN="$L4L"
  say "Tier 2 — second independent kernel (lean4lean)"
  run "$PY" harness/ampas_lean.py corpus/manifest.json \
        --out build/corpus_twokernels.json >/dev/null \
    && run "$PY" scripts/check_expectations.py build/corpus_twokernels.json --require-two-kernels
  RAN="$RAN 2"
else
  say "Tier 2 skipped — lean4lean not built"
  note "./scripts/build-lean4lean.sh"
fi

[ "$WANT" -lt 3 ] && { say "Stopping at tier $WANT"; exit $FAILED; }

# ---------------------------------------------------------------- tier 3
MT="$ROOT/mathlib-tier"
if [ -f "$MT/.lake/build/lib/lean/AmpasRef/ChallengeMathlib.olean" ]; then
  say "Tier 3 — Mathlib claim and the external validation pair"
  MLPATH=$("$PY" scripts/mathlib_path.py)
  export AMPAS_EXTRA_LEAN_PATH="$MLPATH"
  # one directory holding every trusted AmpasRef module, core and tier: Lean
  # resolves a module against the first path entry that has its root directory
  # and does not search on, so the two build trees cannot simply be chained
  run "$PY" scripts/merge_trusted.py build/trusted-mathlib || exit $FAILED
  export AMPAS_TRUSTED_OLEAN="$ROOT/build/trusted-mathlib"
  LEAN_PATH="$AMPAS_TRUSTED_OLEAN:$MLPATH" "$PY" harness/make_baseline.py \
      build/kernel_baseline_mathlib.json AmpasRef.ChallengeMathlib >/dev/null \
    && export AMPAS_KERNEL_BASELINE="$ROOT/build/kernel_baseline_mathlib.json"
  note "Mathlib-backed claim (Euclid, over Mathlib's Nat.Prime)"
  export AMPAS_CLAIMS="$ROOT/reference/claims_mathlib.json"
  run "$PY" harness/ampas_lean.py corpus/manifest.json \
        --out build/corpus_mathlib.json >/dev/null \
    && run "$PY" scripts/check_expectations.py build/corpus_mathlib.json

  note "counterexample search over the Mathlib claim"
  AMPAS_CLAIMS="$ROOT/reference/claims_mathlib.json" \
    run "$PY" harness/counterexample.py --out build/counterexample_search_mathlib.json

  note "external validation: Fermat's false claim (1640) vs Euler's refutation (1732)"
  LEAN_PATH="$AMPAS_TRUSTED_OLEAN:$MLPATH" "$PY" harness/make_baseline.py \
      build/kernel_baseline_fermat.json AmpasRef.GuardsFermat AmpasRef.ChallengeFermat >/dev/null
  export AMPAS_CLAIMS="$ROOT/reference/claims_fermat.json"
  export AMPAS_KERNEL_BASELINE="$ROOT/build/kernel_baseline_fermat.json"
  run "$PY" harness/ampas_lean.py corpus/manifest_fermat.json \
        --out build/fermat_validation.json >/dev/null \
    && run "$PY" scripts/check_expectations.py build/fermat_validation.json
  # the search's own external validation: Fermat's claim must die at n = 5,
  # and Euler's refutation of it must not
  note "counterexample search over the validation pair"
  run "$PY" harness/counterexample.py --out build/counterexample_search_fermat.json
  unset AMPAS_CLAIMS
  RAN="$RAN 3"
else
  say "Tier 3 skipped — the Mathlib tier is not built"
  note "./scripts/build-mathlib-tier.sh   (~20 min, builds Mathlib from source)"
fi

say "Summary"
note "tiers run:$RAN"
if [ "$FAILED" = 0 ]; then
  note "all checks passed"
  note "results in build/; what each file means: evidence/INDEX.md"
else
  note "SOMETHING FAILED — see the output above"
fi
exit $FAILED
