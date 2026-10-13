#!/usr/bin/env python3
"""Check the formalization-triangulation pairs (ROADMAP 5.2).

For each claim with a second rendering, this runs
harness/CheckTriangulation.lean and records what came back: whether the
equivalence theorem relates the two statements on record, what it rests on,
and the provenance of both renderings.

Read ASSUMPTIONS A1d before reading a result. The finding this round produced
is about the method, not about any claim: **equivalence of propositions is
vacuous between two true statements.** Any two theorems are equivalent,
whatever they say, so an equivalence proof cannot distinguish a faithful
rendering from a different true one --
`Ampas.Triangulation.indistinguishable` proves exactly that, with "the sum of
two evens is even" and "the product of two evens is even". Triangulation
therefore detects only a rendering whose error makes it FALSE, which is
largely what harness/counterexample.py already does. It is not the fidelity
check ROADMAP 5.2 described.

What the pairs still buy, stated without inflation: each one rules out a
misreading of that claim that would have changed its truth value, and each
`Iff` is a kernel-checked obligation rather than a reviewer's assurance that
two renderings "say the same thing".

Usage:
  python3 harness/triangulate.py --out build/triangulation.json
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
PAIRS = ROOT / "reference" / "triangulation.json"


def _bin(name: str):
    from ampas_lean import lean_exe
    return lean_exe(name)


def check(pair: dict, module: str, timeout: int) -> dict:
    req = ROOT / ".tri_req.json"
    req.write_text(json.dumps({"module": module, "equiv_decl": pair["equivalence"],
                               "left": pair["frozen"], "right": pair["alternative"]}),
                   encoding="utf-8", newline="\n")
    env = dict(os.environ)
    root = _bin("lean").parent.parent
    env["PATH"] = f"{root / 'bin'}:{env.get('PATH', '')}"
    env["LEAN_PATH"] = os.environ.get(
        "AMPAS_TRUSTED_OLEAN", str(ROOT / ".lake" / "build" / "lib" / "lean"))
    try:
        r = subprocess.run([str(_bin("lean")), "--run",
                            str(ROOT / "harness" / "CheckTriangulation.lean"), str(req)],
                           capture_output=True, text=True, encoding="utf-8",
                           env=env, cwd=str(ROOT), timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"outcome": "INCONCLUSIVE", "reason": f"exceeded {timeout}s"}
    finally:
        req.unlink(missing_ok=True)
    if r.returncode != 0 or not r.stdout.strip():
        return {"outcome": "INCONCLUSIVE",
                "reason": ((r.stderr or r.stdout) or "").strip()[-700:]}
    try:
        return json.loads(r.stdout.strip().splitlines()[-1])
    except json.JSONDecodeError:
        return {"outcome": "INCONCLUSIVE", "reason": "unparsable output"}


def verdict(rec: dict) -> str:
    if rec.get("outcome") == "INCONCLUSIVE":
        return "INCONCLUSIVE"
    if not rec.get("is_theorem") or rec.get("uses_sorry"):
        return "REJECTED"
    if not rec.get("relates_the_named_statements"):
        return "RELATES_SOMETHING_ELSE"
    return "EQUIVALENT"


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(ROOT / "build" / "triangulation.json"))
    args = ap.parse_args(argv)

    cfg = json.loads(PAIRS.read_text(encoding="utf-8"))
    module = cfg["module"]
    results = []
    for pair in cfg["pairs"]:
        t0 = time.monotonic()
        rec = check(pair, module, int(cfg.get("timeout_seconds", 600)))
        rec["claim"] = pair["claim"]
        rec["outcome"] = verdict(rec)
        rec["provenance"] = pair["provenance"]
        rec["strength"] = pair["strength"]
        rec["seconds"] = round(time.monotonic() - t0, 1)
        rec["consistency"] = ("OK" if rec["outcome"] == pair["expect"]
                              else f"EXPECTED_{pair['expect']}_GOT_{rec['outcome']}")
        results.append(rec)
        extra = "" if rec["consistency"] == "OK" else f"  [{rec['consistency']}]"
        print(f"{pair['claim']:14s} {rec['outcome']:22s} {rec['strength']}{extra}",
              flush=True)
        if rec.get("reason"):
            print(f"               {rec['reason'][:160]}", flush=True)

    out = {"checked_on": time.strftime("%Y-%m-%d"), "module": module,
           "method_limit": cfg["method_limit"], "pairs": results}
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(out, indent=2, ensure_ascii=False) + "\n",
                              encoding="utf-8", newline="\n")
    print(f"\n-> {args.out}")
    return 1 if any(r["consistency"] != "OK" for r in results) else 0


if __name__ == "__main__":
    sys.path.insert(0, str(ROOT / "harness"))
    raise SystemExit(main(sys.argv[1:]))
