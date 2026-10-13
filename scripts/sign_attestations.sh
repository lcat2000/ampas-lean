#!/usr/bin/env bash
# Thin wrapper. The work is in scripts/sign_attestations.py, because signing
# has to happen on the reviewer's own machine and that machine may not have a
# POSIX shell -- a bash-only wrapper was unrunnable in PowerShell, which is
# where it was actually tried.
#
#   scripts/sign_attestations.sh ~/.ampas/ampas-reviewer.pem kai-chang-2026-10
set -euo pipefail
exec python3 "$(dirname "$0")/sign_attestations.py" "$@"
