"""Offline tests for kernel provenance and re-verification (ROADMAP 1).

What these guard is not that provenance is recorded -- it is that a clean
provenance block cannot be read as more than it says. The dangerous sentence
this machinery could produce is "no known bugs", and it would be produced by
an advisory list that is empty, stale, or maintained by nobody. So the tests
are mostly about wording and dates.
"""
import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
ADV = ROOT / "reference" / "kernel_advisories.json"


def advisories() -> dict:
    return json.loads(ADV.read_text(encoding="utf-8"))


def test_the_advisory_list_is_dated_and_attributed():
    """A clean advisory result is worth exactly what the list's maintenance is
    worth, so the date and the maintainer have to be in the file."""
    a = advisories()
    assert a.get("last_reviewed"), "no last_reviewed date"
    assert a.get("reviewed_by"), "nobody is named as maintaining this list"
    # a date, not a mood
    import datetime
    datetime.date.fromisoformat(a["last_reviewed"])


def test_the_list_says_it_is_not_an_all_clear():
    """The failure mode here is the opposite of the usual one: the mechanism
    producing a confident clean answer from a list nobody updated."""
    text = ADV.read_text(encoding="utf-8")
    for phrase in ("not say the kernel is sound",
                   "NOT a substitute for upstream advisories",
                   "last_reviewed"):
        assert phrase in text, f"the advisory list does not warn: {phrase!r}"


def test_no_advisory_invents_an_affected_range():
    """An entry whose affected range this repository has not established must
    leave `affected` empty and say why. Filling in a plausible range would
    turn a guess into a confident machine verdict -- and the matcher would
    then produce AFFECTED or clean results from fiction."""
    for a in advisories()["advisories"]:
        assert "affected" in a, f"{a['id']}: no affected field"
        if not a["affected"]:
            assert a.get("affected_not_established"), (
                f"{a['id']}: empty affected range with no explanation of why "
                f"it is empty")
        assert a.get("source") or a.get("kind"), f"{a['id']}: unsourced"


def test_a_clean_advisory_result_is_worded_as_a_statement_about_the_list():
    """`means` is what a reader actually reads. It must scope the claim to the
    list and the date, and must not say the kernels are sound."""
    import provenance
    st = provenance.advisory_status("Lean (version 4.33.0, commit abc, Release)", None)
    means = st["means"]
    assert "NOT that the kernels have no known soundness bugs" in means
    assert st["advisories_last_reviewed"] == advisories()["last_reviewed"]
    assert "list_sha256" in st, (
        "the record must pin WHICH list it consulted, or a later edit to the "
        "list silently changes what an old record claimed")


def test_the_matcher_fires_when_an_advisory_names_the_kernel():
    """Proved by injection rather than assumed: an advisory naming a version
    must match a record using it. A matcher that never matches would make
    every certificate clean forever."""
    import provenance
    hit = provenance.advisory_status(
        "Lean (version 4.33.0, commit abc, Release)", None)
    # the committed list deliberately matches nothing
    assert hit["matched"] == []

    # inject one in memory and re-run the same logic
    import json as _json
    original = ADV.read_text(encoding="utf-8")
    d = _json.loads(original)
    d["advisories"].append({"id": "TEST", "kind": "injected",
                            "affected": {"lean_versions": ["4.33.0"]}})
    try:
        ADV.write_text(_json.dumps(d), encoding="utf-8", newline="\n")
        fired = provenance.advisory_status(
            "Lean (version 4.33.0, commit abc, Release)", None)
        assert [m["id"] for m in fired["matched"]] == ["TEST"], (
            "an advisory naming this Lean version did not match")
        assert "see `matched`" in fired["means"]
    finally:
        ADV.write_text(original, encoding="utf-8", newline="\n")


def test_reverification_distinguishes_metadata_from_re_execution():
    """A record whose kernels match the live ones is EXPECTED to reproduce.
    Saying it DID reproduce would be a claim about an execution that never
    happened, which is the shape of mistake this repository keeps finding."""
    import reverify
    src = (ROOT / "harness" / "reverify.py").read_text(encoding="utf-8")
    assert "It does not re-run anything" in src
    for state in ("AFFECTED", "KERNEL_CHANGED", "NO_PROVENANCE", "SAME_KERNEL"):
        assert state in src, f"{state} is not a reported state"
    # the no-rerun report must say so in the record, not only on stdout
    assert "Nothing was re-executed" in src


def test_records_without_provenance_are_reported_as_such_not_as_clean():
    """Every stored record from before 2026-10-14 predates provenance. The
    honest answer about them is that their kernel cannot be identified -- not
    that nothing is wrong with them."""
    import reverify
    state, notes = reverify.classify({"results": []}, {})
    assert state == "NO_PROVENANCE"
    assert notes and "cannot be identified" in notes[0]


def test_a_verdict_record_carries_its_provenance():
    """The point of the whole item: a certificate names the kernel that issued
    it. Checked on whatever the latest local run produced; skipped when there
    is none, since CI tier 0 has no build/."""
    p = ROOT / "build" / "corpus_core.json"
    if not p.exists():
        pytest.skip("no local run on disk")
    d = json.loads(p.read_text(encoding="utf-8"))
    prov = d.get("provenance")
    assert prov, "the verdict record does not name the kernel that issued it"
    assert prov.get("lean", {}).get("sha256"), "no hash of the lean binary"
    assert prov.get("primary_kernel"), "no record of the primary kernel"
    assert prov.get("toolchain_pin"), "no toolchain pin recorded"
    assert prov.get("advisories", {}).get("advisories_last_reviewed")
