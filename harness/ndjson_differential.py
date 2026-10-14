#!/usr/bin/env python3
"""Differentially test kernel3's two frontends against each other.

`harness/kernel3/ndjson.py` exists so that `kernel3` can be run against the
[Lean Kernel Arena](https://arena.lean-lang.org/) — its first external,
adversarial measurement, for the layer it occupies. But the frontend is a
TRANSLATION, and a translation can be the thing that fails: if it drops a
declaration, mangles a de Bruijn index or misreads a field, the arena numbers
measure this repository's reader rather than its checker. In the worst
direction, too — a dropped declaration is one `kernel3` cannot object to, so
the error would look like a clean result.

So before any arena number is believed: export the SAME Lean environment
through both exporters, read each with its own frontend, and compare the
resulting `Env` declaration by declaration using `kernel3`'s own
`decl_fingerprint` — the function the provenance gate already trusts to tell
two declarations apart.

    python3 harness/ndjson_differential.py <out.json> <ampas.export> <lean4export.ndjson>

The two exporters do not agree on WHICH declarations to emit: AMPAS's
`harness/Export.lean` walks a dependency closure from named roots, while
lean4export emits a module's whole transitive closure. So the comparison is on
the INTERSECTION of the two name sets, and the report carries both set sizes so
a shrinking intersection cannot hide a frontend that quietly stopped reading
things. Any fingerprint mismatch inside the intersection is a failure, and the
script exits non-zero on one.

This proved its worth immediately: the first version of the frontend dropped
`proj`'s `typeName`, which is exactly what the arena's `proj-non-structure` and
`proj-of-*-prop` bug tests are about.
"""
from __future__ import annotations

import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from kernel3.parse import parse_export            # noqa: E402
from kernel3.ndjson import parse_ndjson           # noqa: E402
from kernel3.check import decl_fingerprint        # noqa: E402


def fingerprints(env) -> dict:
    out = {}
    for name in env.order:
        d = env.get(name)
        if d is None:
            continue
        out[str(name)] = f"{d.kind}:{decl_fingerprint(d)}"
    return out


def compare(ampas_path: str, ndjson_path: str) -> dict:
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(60000)
    try:
        a = fingerprints(parse_export(ampas_path))
        b = fingerprints(parse_ndjson(ndjson_path))
    finally:
        sys.setrecursionlimit(old)

    shared = sorted(set(a) & set(b))
    mismatches = [{"declaration": n, "ampas_frontend": a[n], "ndjson_frontend": b[n]}
                  for n in shared if a[n] != b[n]]
    return {
        "ampas_export": {"file": os.path.basename(ampas_path), "declarations": len(a)},
        "ndjson_export": {"file": os.path.basename(ndjson_path), "declarations": len(b)},
        "shared_declarations": len(shared),
        "agreed": len(shared) - len(mismatches),
        "mismatches": mismatches,
        "only_in_ampas_export": len(set(a) - set(b)),
        "only_in_ndjson_export": len(set(b) - set(a)),
    }


def main(argv) -> int:
    if len(argv) != 3:
        print(__doc__)
        return 2
    out_path, ampas_path, ndjson_path = Path(argv[0]), argv[1], argv[2]
    for p in (ampas_path, ndjson_path):
        if not Path(p).exists():
            print(f"ndjson_differential: missing {p}", file=sys.stderr)
            return 2

    r = compare(ampas_path, ndjson_path)
    report = {
        "schema": "ampas-ndjson-frontend-differential/1",
        "recorded_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        **r,
        "means": [
            "The same Lean environment, exported by two different exporters and",
            "read by kernel3's two frontends, gives the SAME declaration",
            "fingerprints wherever both exporters emitted the declaration.",
            "",
            "A mismatch would be a bug in harness/kernel3/ndjson.py, not a",
            "finding about Lean, and this run exits non-zero on one.",
            "",
            "`only_in_*` are the two exporters' different closure rules --",
            "AMPAS's walks from named roots, lean4export's takes a module's",
            "whole closure -- and not a sign of a dropped declaration. What",
            "would be that sign is `shared_declarations` falling: it is",
            "reported so that a frontend which quietly stopped reading records",
            "cannot pass by comparing fewer and fewer things.",
            "",
            "What this does NOT establish: that either frontend reads the",
            "arena's files correctly. The arena corpus contains declaration",
            "shapes this environment has no instance of, and for those the only",
            "guard is that harness/kernel3/ndjson.py RAISES on a record kind it",
            "does not know rather than skipping it.",
        ],
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(report, f, indent=2, ensure_ascii=False)
        f.write("\n")

    print(f"AMPAS export : {report['ampas_export']['declarations']} declarations")
    print(f"NDJSON export: {report['ndjson_export']['declarations']} declarations")
    print(f"shared       : {report['shared_declarations']}  agreed: {report['agreed']}")
    if report["mismatches"]:
        for m in report["mismatches"][:10]:
            print(f"  MISMATCH {m['declaration']}: "
                  f"{m['ampas_frontend']} vs {m['ndjson_frontend']}", file=sys.stderr)
        print(f"ndjson_differential: {len(report['mismatches'])} fingerprint "
              f"mismatch(es) -- the NDJSON frontend is wrong, not Lean",
              file=sys.stderr)
        return 1
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
