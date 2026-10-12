#!/usr/bin/env python3
"""Assemble one trusted-olean directory for the Mathlib tier.

Lean resolves a module name against the first LEAN_PATH entry that holds the
module's root directory and then requires the file to be there — it does not
keep searching later entries. So a tier-3 submission importing AmpasRef.Defs
fails if the tier's build directory holds some AmpasRef modules (the
Mathlib-backed statements) while Defs lives in the core package's build
directory. Adding both to LEAN_PATH does not help, for the same reason.

So the trusted set for tier 3 is assembled explicitly here, in one directory,
by symlink. That also makes "what is trusted at tier 3" a single thing a
reviewer can list, rather than an ordering accident.

    python3 scripts/merge_trusted.py build/trusted-mathlib
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORE = ROOT / ".lake" / "build" / "lib" / "lean"
TIER = ROOT / "mathlib-tier" / ".lake" / "build" / "lib" / "lean"


def main(argv) -> int:
    if len(argv) != 1:
        print(__doc__)
        return 2
    out = Path(argv[0])
    if not out.is_absolute():
        out = ROOT / out
    for src, what in ((CORE, "core"), (TIER, "Mathlib tier")):
        if not (src / "AmpasRef").is_dir():
            print(f"the {what} reference is not built ({src}); "
                  f"run bootstrap.sh / build-mathlib-tier.sh", file=sys.stderr)
            return 1

    dst = out / "AmpasRef"
    if out.exists():
        for p in sorted(out.rglob("*"), reverse=True):
            p.unlink() if p.is_file() or p.is_symlink() else p.rmdir()
    dst.mkdir(parents=True, exist_ok=True)

    linked = []
    for src in (CORE, TIER):
        for f in sorted((src / "AmpasRef").glob("*.olean")):
            target = dst / f.name
            if target.exists() or target.is_symlink():
                target.unlink()
            target.symlink_to(f.resolve())
            linked.append(f.name)
    print(f"   trusted set for tier 3: {len(linked)} modules -> {out}")
    for name in linked:
        print(f"     AmpasRef.{name[:-6]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
