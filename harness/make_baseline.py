#!/usr/bin/env python3
"""Build the provenance baseline for the third check (harness/kernel3).

The third check re-derives every declaration's *type*, but it does not derive
that an inductive *specification* is legitimate — positivity, the shape of the
generated recursor, its iota rules (harness/kernel3/REVIEW.md, F-2). So it
must not vouch for an inductive it has never seen. The baseline is the set of
fingerprints of every assumed declaration (inductive, constructor, recursor,
quotient constant) of the TRUSTED core: Init plus the reference modules. At
check time, anything outside it is reported as an introduced assumption.

The fingerprint covers the declaration's type and every field of its
specification — for a recursor, that includes each rule's right-hand side —
so a forged recursor cannot pass as a baseline one.

Usage (LEAN_PATH must hold the trusted oleans; add Mathlib's for --mathlib):

    python3 harness/make_baseline.py reference/kernel_baseline.json \\
        AmpasRef.Guards AmpasRef.Challenge
"""
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from kernel3.parse import parse_export            # noqa: E402
from kernel3.check import baseline_fingerprints   # noqa: E402

LEAN = Path(os.environ.get("AMPAS_LEAN_BIN", "")) / "lean" if os.environ.get(
    "AMPAS_LEAN_BIN") else Path("lean")


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 2
    out = Path(argv[0])
    modules = argv[1:]
    fps, counts = set(), {}
    with tempfile.TemporaryDirectory() as td:
        for mod in modules:
            exp = Path(td) / f"{mod}.specs"
            r = subprocess.run([str(LEAN), "--run", str(HERE / "Export.lean"),
                                "--specs", mod, str(exp)],
                               capture_output=True, text=True)
            if r.returncode != 0 or not exp.exists():
                print(f"export of {mod} failed:\n{r.stdout}{r.stderr}", file=sys.stderr)
                return 1
            env = parse_export(str(exp))
            f = baseline_fingerprints(env)
            counts[mod] = len(f)
            fps |= f
    out.write_text(json.dumps(sorted(fps), indent=0) + "\n")
    print(f"{len(fps)} distinct assumed declarations -> {out}")
    for m, n in counts.items():
        print(f"  {m}: {n}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
