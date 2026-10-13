#!/usr/bin/env python3
"""Run the bounded counterexample search over a claim catalogue.

See harness/Counterexample.lean for what the search means, and ASSUMPTIONS.md
A6 for what it does not establish. The short version: finding a counterexample
is decisive -- the frozen statement is false. Finding none is not evidence
that it is true, and it says nothing at all about whether the statement says
what the claim's text says.

The per-claim bounds live in reference/counterexample_bounds.json rather than
here, so the box a result came from is a committed, reviewable number instead
of a default buried in code. Raising a bound is a change to the record.

Usage:
  python3 harness/counterexample.py [--out build/counterexample_search.json]
  AMPAS_CLAIMS=reference/claims_fermat.json python3 harness/counterexample.py
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CATALOGUE = Path(os.environ.get("AMPAS_CLAIMS", ROOT / "reference" / "claims.json"))
BOUNDS = ROOT / "reference" / "counterexample_bounds.json"
DEFAULT_OUT = ROOT / "build" / "counterexample_search.json"


def lean_root() -> Path:
    from ampas_lean import _lean_root  # the one place Lean detection lives
    return _lean_root()


def search_one(module: str, decl: str, bound: int, exists_bound: int,
               extra_path: str, timeout: int) -> dict:
    req = ROOT / ".cex_req.json"
    req.write_text(json.dumps({"module": module, "decl": decl,
                               "bound": bound, "exists_bound": exists_bound}))
    env = dict(os.environ)
    root = lean_root()
    env["PATH"] = f"{root / 'bin'}:{env.get('PATH', '')}"
    # AMPAS_TRUSTED_OLEAN first, as everywhere else in the harness: at tier 3
    # it is the merged directory holding every trusted AmpasRef module, and
    # Lean resolves a module against the FIRST path entry that has its root
    # directory without searching on, so chaining the two build trees instead
    # would silently miss the tier's own statements.
    paths = [os.environ.get("AMPAS_TRUSTED_OLEAN",
                            str(ROOT / ".lake" / "build" / "lib" / "lean"))]
    if extra_path:
        paths.append(extra_path)
    env["LEAN_PATH"] = ":".join(p for p in paths if p)
    started = time.monotonic()
    try:
        r = subprocess.run(
            [str(root / "bin" / "lean"), "--run", str(ROOT / "harness" / "Counterexample.lean"),
             str(req)],
            capture_output=True, text=True, env=env, timeout=timeout, cwd=str(ROOT))
    except subprocess.TimeoutExpired:
        # A search killed by the clock has reached no verdict. Reporting this
        # as "no counterexample" would turn a resource limit into evidence,
        # which is the mistake A5 exists to prevent.
        return {"decl": decl, "outcome": "INCONCLUSIVE",
                "reason": f"search exceeded {timeout}s",
                "bound": bound, "exists_bound": exists_bound}
    finally:
        req.unlink(missing_ok=True)
    elapsed = round(time.monotonic() - started, 1)
    if r.returncode != 0 or not r.stdout.strip():
        return {"decl": decl, "outcome": "INCONCLUSIVE",
                "reason": (r.stderr or r.stdout).strip()[-800:],
                "bound": bound, "exists_bound": exists_bound}
    try:
        rec = json.loads(r.stdout.strip().splitlines()[-1])
        # Points where a hypothesis fails say nothing about the conclusion,
        # and points that could not be decided say nothing either. Only the
        # remainder actually exercised the statement, so that is the number
        # the record reports -- `resolved` conflated the first two with it.
        if "box_size" in rec:
            rec["checked_points"] = (rec["box_size"] - rec.get("vacuous_points", 0)
                                     - rec.get("unresolved_points", 0))
            rec.pop("resolved_points", None)
    except json.JSONDecodeError:
        return {"decl": decl, "outcome": "INCONCLUSIVE",
                "reason": "search produced no parsable record",
                "stdout": r.stdout[-400:]}
    rec["seconds"] = elapsed
    return rec


def bounds_for(claim_id: str) -> tuple[int, int, int]:
    cfg = json.loads(BOUNDS.read_text())
    d = cfg.get("default", {})
    c = cfg.get("claims", {}).get(claim_id, {})
    return (int(c.get("bound", d.get("bound", 12))),
            int(c.get("exists_bound", d.get("exists_bound", 64))),
            int(c.get("timeout_seconds", d.get("timeout_seconds", 300))))


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(DEFAULT_OUT))
    ap.add_argument("--claim", action="append", help="limit to these claim ids")
    args = ap.parse_args(argv)

    cat = json.loads(CATALOGUE.read_text())
    module = cat["reference_module"]
    extra = os.environ.get("AMPAS_EXTRA_LEAN_PATH", "")

    # Bind every search to the statement it actually ran against. Without
    # this, a statement could be edited after a clean search and keep the
    # clean result: the freeze would see "searched, nothing found" about a
    # statement that no longer exists. The hash is taken from the auditor's
    # own structural serialization, the same one the freeze pins, so the two
    # are comparable by construction rather than by agreement between two
    # implementations.
    from ampas_review import _audit, sha256_str
    fz = _audit({"mode": "freeze", "reference_module": module,
                 "trusted_modules": cat["trusted_modules"],
                 "theorems": [c["theorem"] for c in cat["claims"]]})
    stmt_hash = {t["name"]: sha256_str(t["statement"])
                 for t in fz["freeze"] if "statement" in t}

    results = []
    for claim in cat["claims"]:
        cid = claim["id"]
        if args.claim and cid not in args.claim:
            continue
        bound, eb, timeout = bounds_for(cid)
        rec = search_one(module, claim["theorem"], bound, eb, extra, timeout)
        rec["claim"] = cid
        rec["statement_sha256"] = stmt_hash.get(claim["theorem"])
        declared_false = (claim.get("control") or {}).get("target_claim_is_true") is False
        rec["declared_false_control"] = declared_false
        # The cross-check that gives this any teeth: a refuted statement must
        # already be annotated as a false-claim control, and a statement
        # annotated as false must actually be refutable. Either mismatch is a
        # finding about the catalogue, not about the search.
        waiver = (json.loads(BOUNDS.read_text()).get("claims", {})
                  .get(cid, {}).get("falsity_not_searchable"))
        if rec["outcome"] == "REFUTED":
            rec["consistency"] = ("OK" if declared_false
                                  else "REFUTED_BUT_NOT_DECLARED_FALSE")
        elif declared_false:
            # The record says this statement is false. If the search cannot
            # corroborate that, the gap is stated here rather than left to a
            # reader to notice, and a waiver has to name the reason -- which
            # is why PL-BOGUS's falsity (a derivability fact, not a numeric
            # one) does not quietly pass as "searched, nothing found".
            if waiver:
                rec["consistency"] = "OK"
                rec["falsity_not_searchable"] = waiver
            else:
                rec["consistency"] = "DECLARED_FALSE_BUT_SEARCH_DID_NOT_REFUTE"
        else:
            rec["consistency"] = "OK"
        results.append(rec)
        w = f" witness={rec.get('witness')}" if rec.get("witness") else ""
        extra_note = "" if rec["consistency"] == "OK" else f"  [{rec['consistency']}]"
        print(f"{cid:14s} {rec['outcome']:26s}{w}{extra_note}", flush=True)
        if rec.get("reason") and rec["outcome"] != "REFUTED":
            print(f"               reason: {rec['reason'][:160]}", flush=True)

    out = {"catalogue": os.path.relpath(CATALOGUE.resolve(), ROOT),
           "reference_module": module,
           "searched_on": time.strftime("%Y-%m-%d"),
           "searches": results}
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(out, indent=2) + "\n")
    print(f"\n-> {args.out}")
    bad = [r for r in results if r["consistency"] != "OK"]
    return 1 if bad else 0


if __name__ == "__main__":
    sys.path.insert(0, str(ROOT / "harness"))
    raise SystemExit(main(sys.argv[1:]))
