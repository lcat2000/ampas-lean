#!/usr/bin/env python3
"""Compare a driver result file against the expected verdicts in the manifest.

A suite that merely prints verdicts proves nothing: the point is that each
submission's verdict matches what the manifest said it should be BEFORE the
run, and that a rejection happened for a real reason rather than because
something failed to compile or ran out of CPU.

    python3 scripts/check_expectations.py build/corpus_core.json
    python3 scripts/check_expectations.py build/corpus_twokernels.json --require-two-kernels

Exit status 0 only if every submission matched.
"""
import argparse
import json
import sys
from pathlib import Path


def main(argv) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("results")
    ap.add_argument("--require-two-kernels", action="store_true",
                    help="also require that both Lean kernels ran and agreed")
    a = ap.parse_args(argv)

    rows = json.loads(Path(a.results).read_text(encoding="utf-8"))["results"]
    bad = []
    for r in rows:
        mod = r["module"]
        expected = r.get("expected")
        certs = [c["certified"] for c in r["claims"]]
        got = "certified_all" if certs and all(certs) else "rejected"

        inconclusive = bool(r.get("resource_exhausted")) or any(
            c.get("inconclusive") for c in r["claims"])
        if inconclusive:
            # No verdict was reached, so "expected X, got Y" would misdescribe
            # it. Still a failure of the run -- nothing was verified -- but a
            # different kind, with a different remedy.
            bad.append((mod, "INCONCLUSIVE: a checker hit a resource limit "
                             f"({r.get('resource_exhausted') or 'see the claim reasons'}). "
                             "Nothing was verified either way; re-run on an unloaded "
                             "machine or raise AMPAS_MEM_BYTES / AMPAS_CPU_SECONDS."))
        elif expected and got != expected:
            bad.append((mod, f"expected {expected}, got {got}"))

        # A rejection must rest on a verdict, not on an accident.
        if got == "rejected" and expected == "rejected" and not inconclusive:
            if not r["compiled"]:
                bad.append((mod, "rejected only because it did not compile; "
                                 "that tests the compiler, not the checks"))

        # A certification must not rest on an unexplained disagreement.
        if got == "certified_all":
            tc = r.get("third_check", {})
            if tc.get("unadjudicated_disagreement"):
                bad.append((mod, f"certified despite an unadjudicated third-check "
                                 f"disagreement: {tc.get('unadjudicated')}"))
            if tc.get("run") and tc.get("introduced_assumptions"):
                bad.append((mod, f"certified while the third check reported assumptions "
                                 f"it did not cover: {tc['introduced_assumptions'][:5]}"))

        if a.require_two_kernels:
            if r["kernel_replay_independent"] is None:
                bad.append((mod, "the second kernel did not run"))
            elif r["kernel_agreement"] != "agree":
                bad.append((mod, f"kernels disagree: {r['kernel_agreement']}"))

    width = max((len(r["module"]) for r in rows), default=10) + 2
    for r in rows:
        certs = [c["certified"] for c in r["claims"]]
        got = "certified_all" if certs and all(certs) else "rejected"
        flag = " " if got == r.get("expected") else "!"
        tc = r.get("third_check", {}).get("status", "-")
        inc = bool(r.get("resource_exhausted")) or any(
            c.get("inconclusive") for c in r["claims"])
        shown = "INCONCLUSIVE" if inc else got
        if inc:
            flag = "?"
        print(f"   {flag} {r['module']:{width}}{shown:15}{tc}")

    if bad:
        print(f"\n   {len(bad)} PROBLEM(S):", file=sys.stderr)
        for mod, why in bad:
            print(f"     {mod}: {why}", file=sys.stderr)
        return 1
    print(f"   {len(rows)} submission(s), all as the manifest expected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
