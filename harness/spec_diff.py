#!/usr/bin/env python3
"""Differentially test a specification pass against a Lean-accepted environment.

ROADMAP 2 requires it of every one of these passes. `harness/kernel3` assumes
three properties of an inductive declaration — strict positivity, the
recursor's shape, and the iota rules — and each pass that checks one of them
WIDENS what could be accepted. So before anything is allowed to read a pass's
verdict, it has to be run over declaration sets both Lean kernels already
accept.

The asymmetry is the whole point, and it is what this script enforces:

  * a VIOLATION here is a bug in THE PASS, not a finding about Lean. Lean's
    own kernel accepted the declaration, and lean4lean accepted the same
    environment in the tier-1 run; if a pass calls one of them ill-formed then
    its rule is wrong, and a wrong rule that rejects today can accept
    tomorrow. So any violation exits non-zero.
  * UNCLASSIFIED is not a failure. It is the pass declining to decide, which
    is the direction a mistake is allowed to go. The count is recorded, and
    broken down by cause, so growth in it is visible rather than silent.
  * OK over Lean's own declarations says only that the pass agrees with Lean
    where it has an opinion. It does NOT make `kernel3` a specification
    checker while any of the three properties is still assumed, so the
    provenance gate stays exactly as it is.

Usage:
    spec_diff.py --pass positivity|recursor <out.json> <label=specs...>

`label` names the environment an export came from (`AmpasRef.Guards`, say),
because the export file itself is a build artefact in a temporary directory
and its file name would not tell a later reader which declaration set was
covered. A bare path is accepted and labelled by its file name.

A `.specs` export comes from `harness/Export.lean --specs <module> <out>`,
which writes every *assumed* declaration of the environment. That is exactly
what these passes read — and also why some decline: a field typed `a ≠ 0`
cannot be decided without `Ne`, which is a definition and therefore not in the
export. Those are counted under their own cause.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from kernel3.parse import parse_export            # noqa: E402
from kernel3 import positivity as _positivity     # noqa: E402
from kernel3 import recursor as _recursor         # noqa: E402
from kernel3 import iota as _iota                 # noqa: E402
from kernel3 import safety as _safety             # noqa: E402

# Each pass: the module, the schema its record carries, the declaration kind it
# reads, and the causes an UNCLASSIFIED can have. Naming the causes here rather
# than grepping the reason strings is deliberate: a reworded reason once
# emptied the ablation table's signals, and the fix was to tag at the source.
PASSES = {
    "positivity": {
        "module": _positivity,
        "schema": "ampas-positivity-differential/1",
        "reads": "inductive specifications",
        "causes": [
            ("nested inductive", ("nested-inductive", "needs the nested case")),
            ("conclusion not the inductive", ("conclusion is not an application",)),
            ("constructor not in export", ("is not in the export",)),
            ("binder count", ("binders but the declaration",)),
        ],
    },
    "recursor": {
        "module": _recursor,
        "schema": "ampas-recursor-differential/1",
        "reads": "recursors",
        "causes": [
            ("field type not in export", (_recursor.FIELD_TYPE_NOT_IN_EXPORT,)),
            ("nested auxiliary recursor", ("auxiliary recursor",)),
            ("mutual Prop large elimination", ("mutual Prop",)),
            ("constructor not in export", ("is not in the export",)),
            ("motive shape", ("motive", "major premise", "conclusion is not an applied")),
        ],
    },
    "safety": {
        "module": _safety,
        "schema": "ampas-safety-differential/1",
        "reads": "every declaration's unsafe/partial flag",
        "causes": [],
    },
    "iota": {
        "module": _iota,
        "schema": "ampas-iota-differential/1",
        "reads": "the iota rules of every recursor",
        "causes": [
            ("nested auxiliary recursor", (_iota.NESTED,)),
            ("declaration not in export", (_iota.NOT_IN_EXPORT,)),
            ("could not derive the expected rule",
             ("could not derive", "could not place", "fewer binders")),
            ("recursive field shape", ("not applied to the parameters",)),
        ],
    },
}

MEANS = {
    "positivity": [
        "Every inductive in these exports was accepted by Lean's own kernel",
        "when the modules were built, so a VIOLATION would be a bug in",
        "harness/kernel3/positivity.py and this run exits non-zero on one.",
        "",
        "UNCLASSIFIED is the pass declining to decide, which is the safe",
        "direction; the counts by cause are here so growth in it is visible.",
        "",
        "What this run does NOT establish: that a specification which comes",
        "back OK is checked. Positivity is one of three properties kernel3",
        "assumes about an inductive -- the recursor's shape and the iota",
        "rules are the other two. kernel3's provenance gate is what stops a",
        "forged specification producing a clean result, and this pass does",
        "not relax it.",
    ],
    "iota": [
        "Every rule in these exports was generated by Lean itself, so a",
        "VIOLATION would be a bug in harness/kernel3/iota.py and this run exits",
        "non-zero on one. The pass re-derives each rule's right-hand side from",
        "the constructor and the recursor and compares it, so an OK here means",
        "the stored rule IS the derived one, not merely that it looks plausible.",
        "",
        "UNCLASSIFIED is the pass declining to decide, and nested inductives'",
        "auxiliary recursors are nearly all of it.",
        "",
        "What this run does NOT establish: that the export came from Lean. All",
        "three passes check a declaration against the rules Lean would have",
        "followed; none shows that Lean produced it. That is what the provenance",
        "gate is for, and ASSUMPTIONS A3 is written against that boundary.",
    ],
    "safety": [
        "Neither exporter emits an unsafe or partial declaration by default --",
        "lean4export needs --export-unsafe and harness/Export.lean has no",
        "equivalent -- so a VIOLATION here would mean a declaration reached the",
        "file that the exporter did not vouch for, and this run exits non-zero",
        "on one.",
        "",
        "What this run does NOT establish: that the flag means what it says. It",
        "reads a field. The arena's 140_falseFromUnsafe and",
        "141_falseFromPartial are what showed the field was being dropped.",
    ],
    "recursor": [
        "Every recursor in these exports was generated and accepted by Lean's",
        "own kernel when the modules were built, so a VIOLATION would be a bug",
        "in harness/kernel3/recursor.py and this run exits non-zero on one.",
        "",
        "UNCLASSIFIED is the pass declining to decide. Two causes dominate and",
        "neither is about the recursor: a field type that needs a definition",
        "the --specs export does not carry, and the auxiliary recursors a",
        "nested inductive generates over the nesting type.",
        "",
        "What this run does NOT establish: that the iota rules are right. This",
        "pass counts them and checks which constructor each belongs to; it",
        "does not check that a rule computes what the constructor's fields say",
        "it should. The iota rules are the third assumed property and remain",
        "unchecked, so kernel3's provenance gate is unchanged.",
    ],
}


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


def by_cause(unclassified, causes) -> dict:
    counts = {}
    for _name, why in unclassified:
        label = "other"
        for cause, needles in causes:
            if any(n in why for n in needles):
                label = cause
                break
        counts[label] = counts.get(label, 0) + 1
    return counts


def run_one(label: str, path: Path, spec: dict) -> dict:
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(60000)
    try:
        env = parse_export(str(path))
    finally:
        sys.setrecursionlimit(old)
    r = spec["module"].check_env(env)
    return {
        "environment": label,
        "specs": path.name,
        "declarations_in_export": len(env.order),
        "checked": r["checked"],
        "ok": len(r["ok"]),
        "violations": r["violations"],
        "unclassified": r["unclassified"],
        "unclassified_by_cause": by_cause(r["unclassified"], spec["causes"]),
    }


def main(argv) -> int:
    if len(argv) < 4 or argv[0] != "--pass" or argv[1] not in PASSES:
        print(__doc__)
        return 2
    name = argv[1]
    spec = PASSES[name]
    out_path = Path(argv[2])

    sets = []
    for arg in argv[3:]:
        label, p = split_label(arg)
        if not p.exists():
            print(f"spec_diff: missing export {p}", file=sys.stderr)
            return 2
        sets.append(run_one(label, p, spec))

    violations = sum(len(s["violations"]) for s in sets)
    report = {
        "schema": spec["schema"],
        "pass": name,
        "reads": spec["reads"],
        "recorded_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "lean": lean_version(),
        "totals": {
            "checked": sum(s["checked"] for s in sets),
            "ok": sum(s["ok"] for s in sets),
            "violations": violations,
            "unclassified": sum(len(s["unclassified"]) for s in sets),
        },
        "sets": sets,
        "means": MEANS[name],
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(report, f, indent=2, ensure_ascii=False)
        f.write("\n")

    for s in sets:
        print(f"{s['environment']}: checked={s['checked']} ok={s['ok']} "
              f"violations={len(s['violations'])} "
              f"unclassified={len(s['unclassified'])}")
        for cause, n in sorted(s["unclassified_by_cause"].items()):
            print(f"    unclassified, {cause}: {n}")
    for s in sets:
        for decl, why in s["violations"]:
            print(f"  VIOLATION {decl}: {why}", file=sys.stderr)
    if violations:
        print(f"spec_diff: the {name} pass reports {violations} violation(s) "
              f"over a Lean-accepted environment -- the pass is wrong, not Lean",
              file=sys.stderr)
        return 1
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
