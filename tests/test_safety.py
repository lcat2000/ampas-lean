"""The fourth specification pass: `unsafe` and `partial` (ROADMAP 6c).

Lean marks a declaration `unsafe` or `partial` when it is not checked the way
a proof must be: `unsafe` opts out of the kernel's guarantees, `partial` out of
the termination requirement — so a `partial def` can be a non-terminating loop
whose type claims it returns `False`.

`kernel3` accepted both of the arena's tests for this
(`bad/tutorial/140_falseFromUnsafe`, `141_falseFromPartial`) because the NDJSON
frontend read the `safety` and `isUnsafe` fields and threw them away. **Nothing
written in this repository could have found it**: `harness/Export.lean` has no
such field to drop, so AMPAS's own exports cannot contain an unsafe
declaration. It took a corpus built by someone else.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
from kernel3 import safety                                   # noqa: E402
from kernel3.safety import check_env, declared_safety, UNSAFE_KINDS  # noqa: E402
from kernel3.parse import Decl, Env                          # noqa: E402
from kernel3.terms import Name, sort, ZERO                    # noqa: E402


def env_with(*flags) -> Env:
    env = Env()
    for i, f in enumerate(flags):
        d = Decl("def", Name.mk((f"d{i}",)), sort(ZERO), [])
        if f is not None:
            d.safety = f
        env.add(d)
    return env


def test_unsafe_and_partial_are_violations():
    r = check_env(env_with("unsafe", "partial"))
    assert len(r["violations"]) == 2
    assert {n for n, _ in r["violations"]} == {"d0", "d1"}
    for _, why in r["violations"]:
        assert "may not" in why or "may depend" in why


def test_safe_and_absent_are_both_safe():
    """Absent means safe on purpose: neither exporter emits an unsafe
    declaration by default, so a declaration with no flag is one the exporter
    vouched for. Treating absent as suspect would reject every AMPAS export,
    whose format has no such field at all."""
    r = check_env(env_with("safe", None))
    assert r["violations"] == []
    assert len(r["ok"]) == 2
    assert declared_safety(Decl("def", Name.mk(("x",)), sort(ZERO), [])) == "safe"


def test_the_flag_is_a_violation_and_never_a_decline():
    """There is nothing undecidable about reading a field, so this pass has no
    UNCLASSIFIED outcome -- unlike the other three, which all have shapes they
    cannot judge."""
    r = check_env(env_with("unsafe", "partial", "safe", None))
    assert r["unclassified"] == []
    assert r["checked"] == 4
    assert r["checked"] == len(r["ok"]) + len(r["violations"])


def test_both_kinds_lean_uses_are_covered():
    assert set(UNSAFE_KINDS) == {"unsafe", "partial"}


def test_the_module_says_why_it_is_not_part_of_the_term_checker():
    doc = safety.__doc__ or ""
    assert "under review" in doc
    assert "changes no verdict" in doc
    assert "--export-unsafe" in doc


def test_the_frontend_carries_the_flag_rather_than_dropping_it():
    """The actual bug was in the reader, not in any checker: it parsed both
    fields and discarded them."""
    src = (ROOT / "harness" / "kernel3" / "ndjson.py").read_text(encoding="utf-8")
    assert "_mark_safety" in src
    assert src.count("_mark_safety(d,") >= 4, (
        "every declaration kind that can carry the flag must be marked")
    assert "threw them away" in src


def test_the_differential_record_shows_no_unsafe_declaration_in_the_libraries():
    """If the real exports contained one, this pass would reject every AMPAS
    run -- so the differential is what makes it safe to treat the flag as a
    violation rather than a warning."""
    p = ROOT / "evidence" / "safety_differential.json"
    if not p.exists():
        import pytest
        pytest.skip("run scripts/verify.sh at tier 3 to produce it")
    d = json.loads(p.read_text(encoding="utf-8"))
    assert d["totals"]["violations"] == 0
    assert d["totals"]["checked"] > 10000
