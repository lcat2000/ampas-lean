"""The harness must not depend on the machine's locale (no Lean needed).

The bug this exists to prevent happened: every `read_text()` in the harness
used the platform default encoding, so on a Windows machine with a Traditional
Chinese locale (cp950) reading `reference/claims.json` -- UTF-8, with em
dashes and Chinese in the reviewer's own recorded basis -- raised
UnicodeDecodeError and the signing step died three times in a row. The
repository had never been run anywhere but Linux, so nothing caught it.

It matters more here than in most projects: SHA256SUMS and the
content-addressed freeze hash BYTES. An encoding or line-ending conversion
changes hashes that are supposed to change only when meaning changes, so a
locale difference can look exactly like statement drift.
"""
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
# This file is excluded from its own scan: it carries the patterns it looks
# for as string literals, so including it would make the check report itself.
SOURCES = sorted(p for p in set(
    list((ROOT / "harness").glob("*.py"))
    + list((ROOT / "scripts").glob("*.py"))
    + list((ROOT / "tests").glob("*.py"))) if p.name != Path(__file__).name)


def _calls(src: str, needle: str) -> list[str]:
    """Every call of `needle`, with its balanced argument list."""
    out, i = [], 0
    while True:
        j = src.find(needle, i)
        if j < 0:
            return out
        k = j + len(needle)
        depth = 1
        while depth and k < len(src):
            if src[k] == "(":
                depth += 1
            elif src[k] == ")":
                depth -= 1
            k += 1
        out.append(src[j:k])
        i = k


@pytest.mark.parametrize("path", SOURCES, ids=lambda p: p.name)
def test_text_file_io_names_its_encoding(path):
    src = path.read_text(encoding="utf-8")
    bad = []
    for needle in (".read_text(", ".write_text("):
        for call in _calls(src, needle):
            if "encoding=" not in call:
                bad.append(call.split("\n")[0][:80])
    for call in _calls(src, "open("):
        # binary mode has no encoding, and `Json.parse`-style byte reads are fine
        if re.search(r'["\'][rwa]b\+?["\']', call) or "encoding=" in call:
            continue
        bad.append(call.split("\n")[0][:80])
    assert not bad, (
        f"{path.name}: text file I/O without an explicit encoding, which uses "
        f"the machine's locale:\n  " + "\n  ".join(bad))


@pytest.mark.parametrize("path", SOURCES, ids=lambda p: p.name)
def test_subprocess_output_names_its_encoding(path):
    """`text=True` decodes a child's output with the locale encoding too, and
    the counterexample searcher's own reasons contain characters cp950 cannot
    represent (`∃`, `≤`) -- so a reason would crash the reader rather than be
    reported."""
    src = path.read_text(encoding="utf-8")
    for call in _calls(src, "subprocess.run("):
        if "text=True" in call:
            assert "encoding=" in call, (
                f"{path.name}: subprocess.run(text=True) without an encoding")


def test_line_endings_are_pinned():
    """SHA256SUMS and the freeze hash bytes, so a CRLF checkout changes hashes
    that should change only when meaning does."""
    ga = ROOT / ".gitattributes"
    assert ga.exists(), "no .gitattributes: a Windows checkout rewrites line endings"
    text = ga.read_text(encoding="utf-8")
    assert "eol=lf" in text


def test_no_shell_only_step_in_the_signing_path():
    """Signing is the one step that must happen on the reviewer's own machine,
    whatever machine that is. A bash-only wrapper made it unrunnable in
    PowerShell, which is where it was actually tried."""
    py = ROOT / "scripts" / "sign_attestations.py"
    assert py.exists(), (
        "scripts/sign_attestations.py is missing: the signing wrapper must be "
        "runnable without a POSIX shell")
    src = py.read_text(encoding="utf-8")
    for cat in ("claims.json", "claims_mathlib.json", "claims_fermat.json"):
        assert cat in src, f"the wrapper does not cover {cat}"
