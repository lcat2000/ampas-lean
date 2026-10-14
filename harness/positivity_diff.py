#!/usr/bin/env python3
"""Differentially test the positivity pass against a Lean-accepted environment.

ROADMAP 2 requires it: `harness/kernel3/positivity.py` WIDENS what can be
accepted, so before anything is allowed to read its verdict, it has to be run
over declaration sets both Lean kernels already accept.

The asymmetry is the whole point, and it is what this script enforces:

  * a VIOLATION here is a bug in THIS PASS, not a finding about Lean. Lean's
    own kernel accepted the declaration, and lean4lean accepted the same
    environment in the tier-1 run; if this pass calls one of them
    non-strictly-positive then its rule is wrong, and a wrong rule that
    rejects today can accept tomorrow. So any violation exits non-zero.
  * UNCLASSIFIED is not a failure. It is the pass declining to decide, which
    is the direction a mistake is allowed to go. The count is recorded rather
    than tolerated silently, so growth in it is visible.
  * OK over Lean's own inductives says only that this pass agrees with Lean
    where it has an opinion. It does NOT make the pass a specification
    checker: positivity is one of three properties `kernel3` assumes (the
    others are the recursor's shape and the iota rules), so the provenance
    gate stays exactly as it is.

Usage:
    positivity_diff.py <out.json> <label=specs...>   # one or more .specs exports

`label` names the environment the export came from (`AmpasRef.Guards`, say),
because the export file itself is a build artefact in a temporary directory
and its file name would not tell a later reader which declaration set was
covered. A bare path is accepted and labelled by its file name.

A `.specs` export comes from `harness/Export.lean --specs <module> <out>`,
which writes every assumed declaration of the environment -- i.e. the
inductive specifications, which is exactly what this pass reads.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from datetime import date, timezone, datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from kernel3.parse import parse_export            # noqa: E402
from kernel3.positivity import check_env          # noqa: E402


def lean_version() -> str:
    exe = os.environ.get("AMPAS_LEAN", "lean")
    for cand in (exe, exe + ".exe"):
        try:
            r = subprocess.run([cand, "--version"], capture_output=True,
                               text=True, encoding="utf-8", timeout=60)
        except (OSError, subprocess.SubprocessError):
            continue
        if r.returncode == 0:
            return r.stdout.strip()
    return "unknown"


def split_label(arg: str) -> tuple[str, Path]:
    """`label=path`, or a bare path labelled by its file name.

    Split on the FIRST `=` only, and only when what precedes it is not itself
    a path: `C:\\tmp\\x.specs` must not be read as label `C`.
    """
    if "=" in arg:
        label, rest = arg.split("=", 1)
        if label and not any(c in label for c in (os.sep, "/", ":")):
            return label, Path(rest)
    return Path(arg).name, Path(arg)


def run_one(label: str, path: Path) -> dict:
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(60000)
    try:
        env = parse_export(str(path))
    finally:
        sys.setrecursionlimit(old)
    r = check_env(env)
    return {
        "environment": label,
        "specs": path.name,
        "declarations_in_export": len(env.order),
        "inductives_checked": r["checked"],
        "ok": len(r["ok"]),
        "violations": r["violations"],
        "unclassified": r["unclassified"],
    }


def main(argv) -> int:
    if len(argv) < 2:
        print(__doc__)
        return 2
    out_path = Path(argv[0])
    sets = []
    for arg in argv[1:]:
        label, p = split_label(arg)
        if not p.exists():
            print(f"positivity_diff: missing export {p}", file=sys.stderr)
            return 2
        sets.append(run_one(label, p))

    violations = sum(len(s["violations"]) for s in sets)
    checked = sum(s["inductives_checked"] for s in sets)
    ok = sum(s["ok"] for s in sets)
    uncl = sum(len(s["unclassified"]) for s in sets)

    report = {
        "schema": "ampas-positivity-differential/1",
        "recorded_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "lean": lean_version(),
        "totals": {
            "inductives_checked": checked,
            "ok": ok,
            "violations": violations,
            "unclassified": uncl,
        },
        "sets": sets,
        "means": [
            "Every inductive in these exports was accepted by Lean's own kernel",
            "when the modules were built, so a VIOLATION would be a bug in",
            "harness/kernel3/positivity.py and this run exits non-zero on one.",
            "",
            "UNCLASSIFIED is the pass declining to decide, which is the safe",
            "direction; the count is here so growth in it is visible.",
            "",
            "What this run does NOT establish: that a specification which comes",
            "back OK is checked. Positivity is one of three properties kernel3",
            "assumes about an inductive -- the recursor's shape and the iota",
            "rules are the other two, and neither is checked anywhere in this",
            "repository. kernel3's provenance gate is what stops a forged",
            "specification producing a clean result, and this pass does not",
            "relax it.",
        ],
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(report, f, indent=2, ensure_ascii=False)
        f.write("\n")

    for s in sets:
        print(f"{s['environment']}: checked={s['inductives_checked']} "
              f"ok={s['ok']} violations={len(s['violations'])} "
              f"unclassified={len(s['unclassified'])}")
    for s in sets:
        for name, why in s["violations"]:
            print(f"  VIOLATION {name}: {why}", file=sys.stderr)
    if violations:
        print(f"positivity_diff: {violations} violation(s) over a Lean-accepted "
              f"environment -- the pass is wrong, not Lean", file=sys.stderr)
        return 1
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
