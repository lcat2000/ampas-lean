#!/usr/bin/env python3
"""Run `harness/kernel3` against the Lean Kernel Arena suite.

ROADMAP 6. `kernel3` has five specification passes, each differentially
tested, and four adversarial vectors — all four written by this repository.
"Thirteen attacks with recorded catching layers is evidence that those
thirteen are caught, and nothing more" applies to the third check as much as
to the corpus, and nothing here can fix it from the inside.

The [Lean Kernel Arena](https://arena.lean-lang.org/) publishes 198 tests for
exactly this layer: `bad/` (must be REJECTED, including 19 regressions for
real Lean kernel bugs) and `good/` (must be ACCEPTED). They are third-party
and adversarial.

    python3 harness/arena_run.py <out.json> <path to the extracted corpus>

**The number that matters is `wrongly_accepted`.** A `bad/` test that comes
back accepted is a soundness hole in `kernel3` that no vector written here
would have found. Everything else — declines, rejections of `good/` tests —
is a statement about coverage, which was never in doubt: `kernel3` checks the
term layer and assumes the specification layer, and the arena contains plenty
it has no opinion about.

TWO CONFIGURATIONS, reported separately, because they answer different
questions:

  * `term_only` — `kernel3.check.check_env` with no trusted baseline, which is
    what AMPAS's third check does today. Its expected weakness is exactly the
    one ASSUMPTIONS A3 records: a forged inductive specification is ACCEPTED,
    because the specification layer is assumed rather than checked and the
    provenance gate that contains it has no baseline to work from here.
  * `with_spec_passes` — the same, plus `positivity`, `recursor`, `iota`,
    `safety` and `declaration`.
    This is what ROADMAP 2a–2c added, and the arena is the first external
    test of it.

A declaration set is ACCEPTED when nothing objects: no type error, no
unproved theorem, and (in the second configuration) no VIOLATION from any
pass. `introduced_assumptions` is NOT treated as an objection — every arena
test declares its own inductives, so counting those would reject all 198 and
measure nothing. They are counted and reported instead, because an acceptance
that rests on an unchecked specification is weaker than one that does not,
and the record has to say which it is.

Each test runs in its own subprocess with a timeout, so a crash or a runaway
is a DECLINE for that test rather than the end of the run. A decline is not
evidence about a proof — not a rejection on the merits — and is reported in
its own column.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

WORKER = r'''
import json, sys
sys.setrecursionlimit(%(rec)d)
sys.path.insert(0, %(harness)r)
from kernel3.ndjson import parse_ndjson
from kernel3.check import check_env
from kernel3 import positivity, recursor, iota, safety, declaration

path = sys.argv[1]
out = {"frontend": "ok"}
try:
    env = parse_ndjson(path)
except Exception as e:
    print(json.dumps({"outcome": "DECLINED", "mechanism": "frontend",
                      "detail": f"{type(e).__name__}: {e}"[:300]}))
    raise SystemExit(0)

try:
    r = check_env(env)
except Exception as e:
    print(json.dumps({"outcome": "DECLINED", "mechanism": "checker crash",
                      "detail": f"{type(e).__name__}: {e}"[:300]}))
    raise SystemExit(0)

out["checked"] = r["checked"]
out["total"] = r["total"]
out["type_errors"] = [[str(a), str(b)[:160]] for a, b in r["errors"][:3]]
out["unproved_theorems"] = [str(x) for x in r.get("unproved_theorems", [])][:5]
out["introduced_assumptions"] = len(r.get("introduced_assumptions", []))

passes = {}
for name, mod in (("positivity", positivity), ("recursor", recursor),
                  ("iota", iota), ("safety", safety),
                  ("declaration", declaration)):
    try:
        p = mod.check_env(env)
        passes[name] = {"checked": p["checked"], "ok": len(p["ok"]),
                        "violations": [[n, w[:160]] for n, w in p["violations"][:3]],
                        "unclassified": len(p["unclassified"])}
    except Exception as e:
        passes[name] = {"error": f"{type(e).__name__}: {e}"[:200]}
out["passes"] = passes
print(json.dumps(out))
'''


def run_one(path: Path, timeout: int, rec: int) -> dict:
    src = WORKER % {"harness": str(HERE), "rec": rec}
    t0 = time.monotonic()
    try:
        p = subprocess.run([sys.executable, "-I", "-c", src, str(path)],
                           capture_output=True, text=True, encoding="utf-8",
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"outcome": "DECLINED", "mechanism": "timeout",
                "detail": f"no verdict in {timeout}s",
                "seconds": round(time.monotonic() - t0, 1)}
    secs = round(time.monotonic() - t0, 1)
    if p.returncode != 0 or not p.stdout.strip():
        tail = (p.stderr or "").strip().splitlines()
        return {"outcome": "DECLINED", "mechanism": "worker died",
                "detail": (tail[-1] if tail else f"exit {p.returncode}")[:300],
                "seconds": secs}
    try:
        rec_out = json.loads(p.stdout.strip().splitlines()[-1])
    except json.JSONDecodeError:
        return {"outcome": "DECLINED", "mechanism": "worker output unreadable",
                "detail": p.stdout[-300:], "seconds": secs}
    rec_out["seconds"] = secs
    return rec_out


def classify(r: dict) -> tuple[str, str, list]:
    """(term_only, with_spec_passes, reasons). ACCEPTED | REJECTED | DECLINED."""
    if r.get("outcome") == "DECLINED":
        return "DECLINED", "DECLINED", [r.get("mechanism", "?")]
    reasons = []
    objected = False
    if r.get("type_errors"):
        objected = True
        reasons.append(f"type error: {r['type_errors'][0][0]}")
    if r.get("unproved_theorems"):
        objected = True
        reasons.append(f"unproved theorem: {r['unproved_theorems'][0]}")
    term = "REJECTED" if objected else "ACCEPTED"

    spec_objected = objected
    for name, p in (r.get("passes") or {}).items():
        if p.get("error"):
            reasons.append(f"{name} pass crashed: {p['error'][:60]}")
            continue
        if p.get("violations"):
            spec_objected = True
            reasons.append(f"{name}: {p['violations'][0][0]}")
    spec = "REJECTED" if spec_objected else "ACCEPTED"
    return term, spec, reasons


def main(argv) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("corpus")
    ap.add_argument("--timeout", type=int, default=180)
    ap.add_argument("--recursion-limit", type=int, default=60000)
    ap.add_argument("--only", help="substring filter on the test's relative path")
    a = ap.parse_args(argv)

    corpus = Path(a.corpus)
    tests = sorted(corpus.rglob("*.ndjson"))
    if a.only:
        tests = [t for t in tests if a.only in str(t.relative_to(corpus))]
    if not tests:
        print(f"arena_run: no .ndjson tests under {corpus}", file=sys.stderr)
        return 2

    rows = []
    for t in tests:
        rel = str(t.relative_to(corpus))
        expected = "REJECTED" if rel.startswith("bad/") else "ACCEPTED"
        r = run_one(t, a.timeout, a.recursion_limit)
        term, spec, reasons = classify(r)
        rows.append({
            "test": rel,
            "group": rel.split("/")[1] if "/" in rel else "",
            "expected": expected,
            "term_only": term,
            "with_spec_passes": spec,
            "reasons": reasons[:4],
            "declarations_checked": r.get("checked"),
            "introduced_assumptions": r.get("introduced_assumptions"),
            "unclassified_specs": sum(
                p.get("unclassified", 0) for p in (r.get("passes") or {}).values()
                if isinstance(p, dict)),
            "mechanism": r.get("mechanism"),
            "detail": r.get("detail"),
            "seconds": r.get("seconds"),
        })
        mark = "  " if term == expected or term == "DECLINED" else "!!"
        print(f"{mark} {rel:46} expected={expected:9} term={term:9} "
              f"+specs={spec:9} {r.get('seconds')}s", flush=True)

    def tally(key: str) -> dict:
        return {
            "wrongly_accepted": sum(1 for r in rows
                                    if r["expected"] == "REJECTED" and r[key] == "ACCEPTED"),
            "wrongly_rejected": sum(1 for r in rows
                                    if r["expected"] == "ACCEPTED" and r[key] == "REJECTED"),
            "correct": sum(1 for r in rows if r[key] == r["expected"]),
            "declined": sum(1 for r in rows if r[key] == "DECLINED"),
        }

    report = {
        "schema": "ampas-arena-run/1",
        "recorded_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "corpus": {
            "source": "https://arena.lean-lang.org/lean-arena-tests.tar.gz",
            "tests": len(rows),
            "must_be_rejected": sum(1 for r in rows if r["expected"] == "REJECTED"),
            "must_be_accepted": sum(1 for r in rows if r["expected"] == "ACCEPTED"),
        },
        "per_test_timeout_seconds": a.timeout,
        "totals": {"term_only": tally("term_only"),
                   "with_spec_passes": tally("with_spec_passes")},
        "results": rows,
    }
    Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    with open(a.out, "w", encoding="utf-8", newline="\n") as f:
        json.dump(report, f, indent=2, ensure_ascii=False)
        f.write("\n")

    print()
    for cfg in ("term_only", "with_spec_passes"):
        t = report["totals"][cfg]
        print(f"{cfg:18} wrongly_accepted={t['wrongly_accepted']:3} "
              f"wrongly_rejected={t['wrongly_rejected']:3} "
              f"correct={t['correct']:3} declined={t['declined']:3}")
    print(f"\n-> {a.out}")
    # A wrongly ACCEPTED bad test is the only outcome that is a defect rather
    # than a limit, in either configuration.
    worst = max(report["totals"][c]["wrongly_accepted"] for c in report["totals"])
    return 1 if worst else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
