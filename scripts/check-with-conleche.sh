#!/usr/bin/env bash
# Check an AMPAS submission with con-leche, a checker that is different in KIND
# from the two this suite runs: if it accepts a declaration set, that set is
# PROVED (in Lean) to have a model in set theory.
#
# ROADMAP 1.3. This is deliberately NOT part of scripts/verify.sh: it needs a
# second 3 GB Lean toolchain, a 660-job build of the checker and its proofs, a
# build of lean4export at this suite's own toolchain, and a ~333 MB NDJSON
# export per submission. Making that the default would make a clean checkout
# unverifiable on an ordinary machine. The recorded evaluation, with the
# measured results, is reference/conleche_evaluation.json.
#
# Usage:
#   ./scripts/check-with-conleche.sh <module> [<lean file>]
#
#   ./scripts/check-with-conleche.sh Genuine corpus/Genuine.lean
#   ./scripts/check-with-conleche.sh AmpasRef.Guards        # declines: see below
#
# WHAT TO EXPECT, from the runs recorded on 2026-10-14:
#   * a genuine submission's closure is ACCEPTED (58107 declarations, 43 s);
#   * AmpasRef.Guards is DECLINED, because this suite states each frozen claim
#     as `theorem ... := sorry` and con-leche refuses sorryAx in a value. That
#     is about AMPAS's design, not about con-leche: check a SUBMISSION;
#   * A04_native_lie is DECLINED -- for its non-standard axiom, which is the
#     layer AMPAS's axiom policy already occupies, not the model proof;
#   * A06_wrong_statement is ACCEPTED. A real proof of the wrong statement is
#     a theorem, and no kernel of any kind decides whether it is the claim it
#     was filed under.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK="${AMPAS_CONLECHE_WORK:-$ROOT/build/conleche-tier}"
CL_REV="${AMPAS_CONLECHE_REV:-dd695ca631306626e3bff8df30208fc594779d75}"
CL_TOOLCHAIN="v4.35.0-rc3"
EXPORT_TAG="${AMPAS_LEAN4EXPORT_TAG:-v4.33.0}"
JOBS="${AMPAS_CONLECHE_JOBS:-2}"

MOD="${1:-}"
SRC="${2:-}"
[ -z "$MOD" ] && { sed -n '1,30p' "$0" | sed 's/^# \{0,1\}//'; exit 2; }

say()  { printf '\n\033[1m== %s\033[0m\n' "$*"; }
note() { printf '   %s\n' "$*"; }
die()  { printf '   FAILED: %s\n' "$*" >&2; exit 1; }

mkdir -p "$WORK"
command -v lean >/dev/null 2>&1 || die "no lean on PATH; run ./scripts/bootstrap.sh first"

# ---------------------------------------------------------------- the checker
say "con-leche $CL_REV"
if [ ! -x "$WORK/con-leche/.lake/build/bin/con-leche" ]; then
  note "cloning and building — the FULL build, proofs included. A verified"
  note "kernel whose verification you have not built is not evidence."
  [ -d "$WORK/con-leche" ] || git clone -q https://github.com/leanprover/con-leche.git "$WORK/con-leche" \
    || die "clone failed"
  ( cd "$WORK/con-leche" && git checkout -q "$CL_REV" ) || die "revision $CL_REV not found"
  if [ ! -x "$WORK/tc/bin/lean" ]; then
    note "fetching Lean $CL_TOOLCHAIN (con-leche's toolchain; this suite pins 4.33.0)"
    mkdir -p "$WORK/tc"
    URL="https://github.com/leanprover/lean4/releases/download/$CL_TOOLCHAIN/lean-${CL_TOOLCHAIN#v}-linux.tar.zst"
    curl -sSL -o "$WORK/lean-tc.tar.zst" "$URL" || die "could not fetch $URL"
    if command -v unzstd >/dev/null 2>&1; then
      unzstd -q -f "$WORK/lean-tc.tar.zst" -o "$WORK/lean-tc.tar" || die "unzstd failed"
    else
      python3 - "$WORK/lean-tc.tar.zst" "$WORK/lean-tc.tar" <<'PY' || die "no zstd and python zstandard unavailable"
import sys
import zstandard
with open(sys.argv[1], "rb") as f, open(sys.argv[2], "wb") as o:
    zstandard.ZstdDecompressor().copy_stream(f, o)
PY
    fi
    tar -xf "$WORK/lean-tc.tar" -C "$WORK/tc" --strip-components=1 || die "untar failed"
    rm -f "$WORK/lean-tc.tar" "$WORK/lean-tc.tar.zst"
  fi
  ( cd "$WORK/con-leche" && PATH="$WORK/tc/bin:$PATH" lake build ) || die "con-leche build failed"
fi
CL="$WORK/con-leche/.lake/build/bin/con-leche"
note "binary: $CL"

say "the consistency theorem's axioms"
cat > "$WORK/AxCheck.lean" <<'EOF'
import ConLeche.MainTheorem
#print axioms ConLeche.no_False_declaration
#print axioms ConLeche.model_exists
EOF
PATH="$WORK/tc/bin:$PATH" LEAN_PATH="$WORK/con-leche/.lake/build/lib/lean" \
  lean "$WORK/AxCheck.lean" || die "could not print the theorem's axioms"
note "no sorryAx above means the proof is complete for the three standard axioms."
note "It is still CONDITIONAL on [SetTheory V]; the bridge that discharges that"
note "from Mathlib's ZFSet is a separate upstream package this script does not build."

# ------------------------------------------------------------- the exporter
say "lean4export $EXPORT_TAG"
if [ ! -d "$WORK/lean4export" ]; then
  git clone -q https://github.com/leanprover/lean4export.git "$WORK/lean4export" || die "clone failed"
fi
( cd "$WORK/lean4export" && git checkout -q "$EXPORT_TAG" ) || die "tag $EXPORT_TAG not found"
# built with THIS suite's toolchain, because it has to read this suite's oleans.
# It is run with `lean --run` rather than as a linked binary: some toolchain
# builds cannot link an executable (a conda-packaged 4.33.0 here could not).
( cd "$WORK/lean4export" && lake build Export >/dev/null 2>&1 ) || true

# ---------------------------------------------------------------- the export
say "exporting $MOD"
EXTRA=""
if [ -n "$SRC" ]; then
  mkdir -p "$WORK/src"
  cp "$ROOT/$SRC" "$WORK/src/$MOD.lean" 2>/dev/null || cp "$SRC" "$WORK/src/$MOD.lean" \
    || die "cannot read $SRC"
  ( cd "$ROOT" && LEAN_PATH="$ROOT/.lake/build/lib/lean" \
      lean -o "$WORK/src/$MOD.olean" "$WORK/src/$MOD.lean" ) || die "compile failed"
  EXTRA="$WORK/src"
fi
NDJSON="$WORK/$MOD.ndjson"
LEAN_PATH="$WORK/lean4export/.lake/build/lib/lean:$ROOT/.lake/build/lib/lean${EXTRA:+:$EXTRA}${AMPAS_EXTRA_LEAN_PATH:+:$AMPAS_EXTRA_LEAN_PATH}" \
  lean --run "$WORK/lean4export/Main.lean" "$MOD" > "$NDJSON" || die "export failed"
note "$(wc -l < "$NDJSON") records, $(du -h "$NDJSON" | cut -f1)"
head -1 "$NDJSON" | grep -q '"version":"3.1.0"' \
  || note "WARNING: the export does not declare format 3.1.0; con-leche may refuse it"

# ----------------------------------------------------------------- the check
say "checking with con-leche (--verified: the mode the theorem is about)"
START=$(date +%s)
"$CL" --verified "--jobs=$JOBS" "$NDJSON"
RC=$?
note "exit $RC after $(( $(date +%s) - START ))s"
case $RC in
  0) note "ACCEPTED. This set has a model in any set theory satisfying the" ;
     note "interface the theorem assumes. It says NOTHING about whether these" ;
     note "statements are the claims they are filed under: see the A06 run in" ;
     note "reference/conleche_evaluation.json, which con-leche accepts." ;;
  *) note "NOT accepted. Read the message: a 'not implemented yet' line is a" ;
     note "DECLINE, not a rejection on the merits, and a decline is not" ;
     note "evidence that a proof is wrong." ;;
esac
exit $RC
