"""Offline tests for formalization triangulation (no Lean needed).

The thing these pin is not that the equivalences hold -- the kernel settles
that -- but that the RECORD cannot be read as claiming more than the method
delivers. The finding this work produced is that equivalence of propositions
is vacuous between two true statements, so an equivalence proof cannot
distinguish a faithful rendering of a claim from a different true one. A
record that reported three green EQUIVALENT lines and nothing else would be
read as a fidelity check, which it is not.

So: the limit must be stated in the record, the provenance of each rendering
must be stated, and a pair that tests almost nothing must say so.
"""
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
PAIRS = ROOT / "reference" / "triangulation.json"
RESULTS = ROOT / "reference" / "triangulation_results.json"


def cfg() -> dict:
    return json.loads(PAIRS.read_text(encoding="utf-8"))


def results() -> dict:
    return {r["claim"]: r
            for r in json.loads(RESULTS.read_text(encoding="utf-8"))["pairs"]}


def test_the_record_states_the_method_limit():
    """Without this, three EQUIVALENT lines read as evidence of fidelity."""
    limit = cfg()["method_limit"]
    for key in ("finding", "proved_by", "demonstration", "consequence",
                "what_remains"):
        assert limit.get(key), f"method_limit is missing {key}"
    assert "vacuous" in limit["finding"].lower()
    assert limit["proved_by"] == "Ampas.Triangulation.indistinguishable", (
        "the limit must name the theorem that proves it, not merely assert it")
    assert (RESULTS.read_text(encoding="utf-8").find("method_limit") >= 0), (
        "the results file must carry the limit too; a reader looking at "
        "outcomes should not have to find it in another file")


def test_the_limit_is_a_theorem_in_the_reference():
    """`indistinguishable` must exist, and be the pair the record describes --
    two different claims, both true, proved equivalent."""
    src = (ROOT / "reference" / "AmpasRef" / "Triangulation.lean").read_text(
        encoding="utf-8")
    assert "theorem indistinguishable" in src
    assert "IsEven (a + b)" in src and "IsEven (a * b)" in src, (
        "the demonstration must actually relate the sum and product claims")


@pytest.mark.parametrize("pair", cfg()["pairs"], ids=lambda p: p["claim"])
def test_every_pair_records_its_provenance_and_strength(pair):
    prov = pair["provenance"]
    assert "independent" in prov and "saw_the_other" in prov, (
        f"{pair['claim']}: provenance must say whether the two renderings were "
        f"independent, since that is what a successful equivalence is worth")
    assert prov["frozen_by"] and prov["alternative_by"]
    assert pair["strength"], f"{pair['claim']}: no strength recorded"
    assert pair["why"], f"{pair['claim']}: no stated reason the pair is useful"


def test_provenance_is_not_overclaimed():
    """Both renderings are currently by one author. If a pair ever claims
    independence, it must name two different authors -- otherwise the word is
    doing work the record does not support."""
    for pair in cfg()["pairs"]:
        prov = pair["provenance"]
        if prov["independent"]:
            assert prov["frozen_by"] != prov["alternative_by"], (
                f"{pair['claim']}: claims independent formalization but names "
                f"the same author for both renderings")
            assert prov["saw_the_other"] is False, (
                f"{pair['claim']}: claims independence while recording that "
                f"one rendering saw the other")
    assert cfg()["provenance_note"], "no overall provenance note"


def test_at_least_one_pair_is_labelled_weak_and_at_least_one_informative():
    """A suite of only-weak pairs would look identical to a suite of
    informative ones on a pass/fail summary. Labelling is the only thing that
    distinguishes them, so both labels have to be in use."""
    strengths = [p["strength"] for p in cfg()["pairs"]]
    assert any(s.startswith("weak") for s in strengths), (
        "no pair is labelled weak; if one tests almost nothing, say so")
    assert any(s == "informative" for s in strengths)


@pytest.mark.parametrize("pair", cfg()["pairs"], ids=lambda p: p["claim"])
def test_the_equivalence_relates_the_named_statements(pair):
    """An `Iff` between two other propositions compiles fine. The checker
    resolves both sides by name; this asserts the recorded result says it
    did."""
    r = results()[pair["claim"]]
    assert r["outcome"] == pair["expect"], (
        f"{pair['claim']}: expected {pair['expect']}, got {r['outcome']}")
    if r["outcome"] == "EQUIVALENT":
        assert r["is_theorem"]
        assert r["relates_the_named_statements"], (
            f"{pair['claim']}: the equivalence does not relate the two "
            f"statements on record")
        assert r["relates_up_to_defeq"]
        assert not r["uses_sorry"]
        assert r["left"] == pair["frozen"] and r["right"] == pair["alternative"]


def test_the_frozen_side_is_not_proved_in_the_triangulation_module():
    """The frozen statements are `sorry` stubs by design -- they are what a
    submission must prove. If one were proved inside the reference, the
    reference would be answering its own questions."""
    for r in results().values():
        assert r["left_proved_here"] is False, (
            f"{r['claim']}: the frozen statement is proved inside the "
            f"reference module, which it must not be")
