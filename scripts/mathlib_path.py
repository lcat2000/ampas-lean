#!/usr/bin/env python3
"""Print the LEAN_PATH entries for the built Mathlib tier, colon separated.

Lake puts each package's oleans under .lake/packages/<pkg>/.lake/build/lib/lean
(and the tier's own under mathlib-tier/.lake/build/lib/lean). The driver needs
all of them, and hardcoding the list would rot with every dependency change.
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TIER = ROOT / "mathlib-tier"
parts = []
own = TIER / ".lake" / "build" / "lib" / "lean"
if own.is_dir():
    parts.append(own)
pkgs = TIER / ".lake" / "packages"
if pkgs.is_dir():
    for d in sorted(pkgs.iterdir()):
        lib = d / ".lake" / "build" / "lib" / "lean"
        if lib.is_dir():
            parts.append(lib)
if not parts:
    print("mathlib tier not built: run ./scripts/build-mathlib-tier.sh", file=sys.stderr)
    raise SystemExit(1)
print(":".join(str(p) for p in parts))
