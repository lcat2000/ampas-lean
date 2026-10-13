#!/usr/bin/env python3
"""Regenerate SHA256SUMS over the sources and the recorded evidence.

Build output (.lake/, build/) and the platform-specific compiled auditor are
deliberately excluded: they are reproduced by scripts/bootstrap.sh rather than
committed. Verify with `sha256sum -c SHA256SUMS`.
"""
import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
INCLUDE = ["*.md", "LICENSE", "NOTICE", "lean-toolchain", "lakefile.toml",
           ".gitignore", ".github/workflows/*.yml",
           "reference/**/*", "corpus/**/*", "harness/**/*", "tests/**/*",
           "evidence/**/*", "unreviewed/**/*", "scripts/*",
           "mathlib-tier/lakefile.toml", "mathlib-tier/lean-toolchain",
           "mathlib-tier/src/**/*"]
EXCLUDE_PARTS = {"__pycache__", ".lake", ".pytest_cache"}


def main() -> int:
    seen, files = set(), []
    for pat in INCLUDE:
        for f in sorted(ROOT.glob(pat)):
            if not f.is_file():
                continue
            rel = f.relative_to(ROOT)
            if set(rel.parts) & EXCLUDE_PARTS or f.suffix == ".pyc":
                continue
            if rel.name.startswith(".tmp_") or rel.name == "audit":
                continue
            if str(rel) in seen:
                continue
            seen.add(str(rel))
            files.append((rel, f))
    lines = [f"{hashlib.sha256(f.read_bytes()).hexdigest()}  {rel}"
             for rel, f in sorted(files, key=lambda t: str(t[0]))]
    (ROOT / "SHA256SUMS").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"{len(lines)} files -> SHA256SUMS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
