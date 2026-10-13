#!/usr/bin/env python3
"""Check the resolved Mathlib revisions against reference/mathlib_pin.json.

Lake records what it actually resolved in lake-manifest.json. If that drifts
from the pin, every Mathlib-backed verdict is about a different library than
the one the recorded run used, so the run says so loudly instead of carrying
on quietly.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
pin = json.loads((ROOT / "reference" / "mathlib_pin.json").read_text(encoding="utf-8"))
man_path = ROOT / "mathlib-tier" / "lake-manifest.json"
if not man_path.exists():
    print("no lake-manifest.json yet; run `lake update` in mathlib-tier/", file=sys.stderr)
    raise SystemExit(1)
man = json.loads(man_path.read_text(encoding="utf-8"))
got = {p["name"]: p.get("rev") for p in man.get("packages", [])}

want = {"mathlib": pin["revision"]}
for d in pin.get("dependencies", []):
    want[d["name"]] = d["revision"]

bad = []
for name, rev in want.items():
    if name not in got:
        bad.append(f"{name}: not resolved")
    elif got[name] != rev:
        bad.append(f"{name}: pinned {rev[:12]}, resolved {str(got[name])[:12]}")

if bad:
    print("MATHLIB PIN MISMATCH:", file=sys.stderr)
    for b in bad:
        print("  " + b, file=sys.stderr)
    print("\nThe recorded Mathlib results are for the pinned revisions. Fix the\n"
          "manifest or treat tier-3 results as being about a different library.",
          file=sys.stderr)
    raise SystemExit(1)
print(f"   mathlib pin OK: {len(want)} package(s) at the pinned revisions")
