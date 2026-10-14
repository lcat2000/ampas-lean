"""The con-leche evaluation record (ROADMAP 1.3b) and what it may claim.

con-leche is a checker different in KIND from the two this suite runs: if it
accepts a declaration set, a theorem proved in Lean says that set has a model
in set theory. It was built in full and run on four AMPAS inputs on
2026-10-14.

These tests guard the record's honesty rather than the checker, which is
upstream's. Three of the four runs are easy to overclaim, and the session that
produced them had just finished correcting exactly that kind of overclaim
about lean4lean (ROADMAP 1.3a):

  * the genuine-submission acceptance is the result the item asked for;
  * the A04 decline is the AXIOM layer, which this suite already has, not the
    model proof — and "not implemented yet" is a decline, not a rejection;
  * the A06 acceptance is the finding that matters, and it is negative: a
    verified kernel accepts a genuine proof of the wrong statement, so A1 is
    not a gap a stronger kernel closes;
  * the theorem is conditional on a set theory whose instantiation was not
    built here.
"""
import json
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
REC = ROOT / "reference" / "conleche_evaluation.json"
DOC = ROOT / "docs" / "CONLECHE-EVALUATION.md"
SCRIPT = ROOT / "scripts" / "check-with-conleche.sh"

rec = json.loads(REC.read_text(encoding="utf-8"))
RUNS = {r["input"].split(" ")[0]: r for r in rec["runs"]}


def run_for(fragment: str) -> dict:
    for r in rec["runs"]:
        if fragment in r["input"]:
            return r
    raise AssertionError(f"no run for {fragment}")


def flat(x) -> str:
    return " ".join(x) if isinstance(x, list) else str(x)


# -------------------------------------------------- what was actually built
def test_the_proof_lane_was_built_not_just_the_binary():
    assert "660" in rec["checker"]["built"]
    assert "proof lane" in rec["checker"]["built"]
    assert "MainTheorem" in rec["checker"]["built"]


def test_the_theorems_axioms_are_recorded_and_sorry_free():
    th = rec["the_theorem"]
    assert set(th["axioms_checked_here"]) == {"propext", "Classical.choice", "Quot.sound"}
    assert th["no_sorry"] is True
    assert "#print axioms" in th["how_checked"]


def test_the_undischarged_hypothesis_is_recorded():
    """The theorem is `(V : Type w) [SetTheory V] → …`. Reporting it as an
    unconditional soundness guarantee would be the overclaim this record
    exists to avoid."""
    text = flat(rec["the_theorem"]["the_hypothesis_not_discharged_here"])
    assert "SetTheory V" in text
    assert "CONDITIONAL" in text or "conditional" in text
    assert "NOT BUILT" in text.upper()
    assert "carneiro" in text.lower()


# ----------------------------------------------------------- the four runs
def test_a_genuine_submission_is_accepted():
    r = run_for("Genuine.lean")
    assert r["outcome"] == "ACCEPTED"
    assert r["declarations_in_export"] > 50000
    assert r["seconds"] < 120


def test_the_reference_environment_declines_for_our_own_reason():
    """It contains `sorry` by design: the reference module states claims, it
    does not prove them. Recording this as a con-leche limitation would put the
    blame in the wrong place."""
    r = run_for("AmpasRef.Guards")
    assert r["outcome"] == "DECLINED"
    assert "sorryAx" in r["message"]
    assert "AMPAS's design" in flat(r["reading"])


def test_the_a04_decline_is_not_credited_to_the_model_proof():
    """Both Lean kernels accept A04. con-leche does not — for its axiom
    restriction, the layer this suite's axiom policy already occupies. This is
    the test that fails if the record ever starts claiming the verified kernel
    caught something the Lean kernels missed."""
    r = run_for("A04_native_lie")
    assert r["outcome"] == "DECLINED"
    reading = flat(r["reading"])
    assert "AXIOM RESTRICTION" in reading.upper()
    assert "NATIVE_EVALUATION" in reading
    assert "did no work" in reading
    assert "decline" in reading.lower() and "not a rejection" in reading.lower()
    assert "1.3a" in reading, "the parallel with the lean4lean overclaim must stay"


def test_a06_is_accepted_and_the_record_says_what_that_means():
    """The headline, and it is negative. If this ever flips to DECLINED in a
    rerun, the record is wrong and the claim in A1/1.3b has to be rewritten,
    not quietly updated."""
    r = run_for("A06_wrong_statement")
    assert r["outcome"] == "ACCEPTED"
    reading = flat(r["reading"])
    assert "wrong statement" in reading
    assert "statement comparator" in reading
    assert re.search(r"any kernel|ANY kernel", reading)


def test_every_run_records_its_cost():
    for r in rec["runs"]:
        assert isinstance(r["seconds"], int) and r["seconds"] > 0, r["input"]
        assert isinstance(r["peak_rss_gib"], float), r["input"]


# ------------------------------------------------------------- the verdict
def test_the_verdict_separates_what_it_adds_from_what_it_does_not():
    v = rec["verdict"]
    assert v["is_different_in_kind"] is True
    assert v["would_integrating_it_strengthen_a_certificate"] is True
    adds = v["what_it_adds"]
    assert "model in set theory" in adds
    nots = flat(v["what_it_does_not_add"])
    assert "fidelity" in nots
    assert "A06" in nots and "A04" in nots
    assert "conditional" in nots.lower()


def test_the_integration_decision_says_cost_not_doubt():
    """An optional tier is a defensible choice and a suspicious one; the record
    has to say which it is."""
    text = flat(rec["verdict"]["integration_decision"])
    assert "OPTIONAL" in text.upper()
    assert "cost, not doubt" in text
    assert "4.35.0-rc3" in text and "4.33.0" in text
    assert "nothing silently" in text.lower() or "not claim" in text.lower()


def test_third_party_numbers_are_marked_as_not_ours():
    t = rec["third_party_evidence_not_produced_here"]
    assert "arena.lean-lang.org" in t["source"]
    note = flat(t["note"])
    assert "not this repository's" in note
    assert "round was in progress" in note, (
        "a benchmark read mid-round must say so")


def test_the_authorship_of_the_checker_is_recorded_neutrally():
    """It matters here, and the record should neither hide it nor lean on it."""
    note = flat(rec["checker"]["authorship_note"])
    assert "Claude" in note
    assert "machine-checked theorem" in note


# ------------------------------------------------- the doc and the script
def test_the_document_and_the_record_agree_on_every_outcome():
    doc = DOC.read_text(encoding="utf-8")
    for r in rec["runs"]:
        word = "accepted" if r["outcome"] == "ACCEPTED" else "declined"
        assert word in doc.lower()
    for r in rec["runs"]:
        if r.get("declarations_in_export") and r["outcome"] == "ACCEPTED":
            assert str(r["declarations_in_export"]) in doc, r["input"]


def test_the_script_warns_what_each_outcome_does_and_does_not_mean():
    src = SCRIPT.read_text(encoding="utf-8")
    assert "--verified" in src
    assert "A06" in src, "the script must say that a wrong statement is accepted"
    assert "DECLINE, not a rejection" in src
    assert "verification you have not built" in src


def test_the_script_is_not_wired_into_the_default_verification():
    verify = (ROOT / "scripts" / "verify.sh").read_text(encoding="utf-8")
    assert "check-with-conleche" not in verify, (
        "a 3 GB toolchain and a 660-job build must not be in the default path")
