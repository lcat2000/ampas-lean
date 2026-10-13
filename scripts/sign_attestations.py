#!/usr/bin/env python3
"""Sign every attestation in the repository with one key. Works anywhere
Python does -- including PowerShell, which is where this is actually run.

Why a wrapper at all: `ampas_review.py sign` works on the catalogue
AMPAS_CLAIMS selects, and the 13 claims live in three catalogues. Signing them
by hand is three invocations, and forgetting one leaves those attestations
carrying the previous key's signature while reference/reviewer_key.json names
the new one -- records that verify against no committed key at all, with a
summary that still reports "signature: present". The offline test suite fails
on exactly that, but not doing it wrong is better than detecting it after.

This needs no Lean. Signing reads the frozen attestation records, signs them
and writes them back; it touches neither the auditor nor a kernel. Only
`verify` needs a toolchain, and CI runs that after you push.

    python scripts/sign_attestations.py ~/.ampas/ampas-reviewer.pem kai-chang-2026-10
"""
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CATALOGUES = ["reference/claims.json",
              "reference/claims_mathlib.json",
              "reference/claims_fermat.json"]


def run(args: list[str], env: dict | None = None) -> int:
    print("  $ " + " ".join(args), flush=True)
    return subprocess.run(args, cwd=str(ROOT), env=env).returncode


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(__doc__)
        print("usage: python scripts/sign_attestations.py <private-key.pem> <key-id>",
              file=sys.stderr)
        return 2
    key, key_id = argv
    key_path = Path(os.path.expanduser(key)).resolve()
    if not key_path.is_file():
        print(f"no such private key: {key_path}", file=sys.stderr)
        return 2

    py = sys.executable or "python"
    for cat in CATALOGUES:
        print(f"== {cat}")
        env = dict(os.environ)
        env["AMPAS_CLAIMS"] = str(ROOT / cat)
        # The harness reads UTF-8 files; on a machine whose locale is not UTF-8
        # the default encoding would be used instead. The code names its
        # encoding everywhere now, and this belt-and-braces line means a
        # stale checkout of the harness still works here.
        env.setdefault("PYTHONUTF8", "1")
        rc = run([py, "harness/ampas_review.py", "sign",
                  "--key", str(key_path), "--key-id", key_id], env)
        if rc != 0:
            print(f"signing {cat} failed; stopping so the keys do not end up mixed",
                  file=sys.stderr)
            return rc

    print("\n== checking every attestation now carries one key id")
    rc = run([py, "-m", "pytest", "tests/test_counterexample.py",
              "tests/test_third_check.py", "-q", "-k", "not pipeline"])
    if rc != 0:
        return rc

    print("\n== refreshing SHA256SUMS")
    rc = run([py, "scripts/sha256sums.py"])
    if rc != 0:
        return rc

    print("""
Signed. What is NOT yet checked: that each signature verifies and that nothing
has drifted since freezing -- that needs Lean. Push, and CI re-verifies with
the toolchain. A green run means the signatures check out against the public
key you just committed.

Do not commit the private key. `git status` should show no .pem.""")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
