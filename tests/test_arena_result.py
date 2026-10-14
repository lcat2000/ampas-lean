"""The arena result (ROADMAP 6c) and what it may claim.

`harness/kernel3`'s first external, adversarial measurement: 198 third-party
tests for the layer it occupies. The result is poor — 23 of 72 bad tests
accepted — and these tests exist so the record stays poor until the checker
improves, rather than being softened in the retelling.
"""
import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))

REC = ROOT / "evidence" / "arena_run.json"
DOC = ROOT / "docs" / "ARENA-RESULT.md"

rec = json.loads(REC.read_text(encoding="utf-8"))
RESULTS = rec["results"]
BY_TEST = {r["test"]: r for r in RESULTS}


def flat(x) -> str:
    return " ".join(x) if isinstance(x, list) else str(x)


# ------------------------------------------------------------ the corpus
def test_the_corpus_is_the_published_one():
    c = rec["corpus"]
    assert c["source"] == "https://arena.lean-lang.org/lean-arena-tests.tar.gz"
    assert c["tests"] == 198
    assert c["must_be_rejected"] == 72
    assert c["must_be_accepted"] == 126


def test_both_configurations_are_reported():
    """`term_only` is what AMPAS runs today; `with_spec_passes` is what 2a-2c
    added. Reporting only the better one would hide what the third check
    actually does in the pipeline."""
    assert set(rec["totals"]) == {"term_only", "with_spec_passes"}
    for cfg in rec["totals"].values():
        assert set(cfg) == {"wrongly_accepted", "wrongly_rejected",
                            "correct", "declined"}


# ------------------------------------------------- the number that matters
def test_the_wrongly_accepted_count_is_not_softened():
    t = rec["totals"]
    assert t["term_only"]["wrongly_accepted"] == 28
    assert t["with_spec_passes"]["wrongly_accepted"] == 23


def test_the_totals_are_recomputable_from_the_rows():
    """A tally that does not follow from the per-test rows is a claim, not a
    measurement. Same lesson as the ablation table and the A01 label."""
    for cfg in ("term_only", "with_spec_passes"):
        wa = sum(1 for r in RESULTS
                 if r["expected"] == "REJECTED" and r[cfg] == "ACCEPTED")
        wr = sum(1 for r in RESULTS
                 if r["expected"] == "ACCEPTED" and r[cfg] == "REJECTED")
        dec = sum(1 for r in RESULTS if r[cfg] == "DECLINED")
        cor = sum(1 for r in RESULTS if r[cfg] == r["expected"])
        assert rec["totals"][cfg] == {"wrongly_accepted": wa,
                                      "wrongly_rejected": wr,
                                      "correct": cor, "declined": dec}, cfg


def test_the_record_compares_itself_to_the_other_checkers():
    """23 against 0 for con-leche and lean4lean. A record that omitted the
    comparison would read better than the result is."""
    text = flat(rec["analysis"]["what_is_not_claimed"])
    assert "con-leche" in text and "lean4lean" in text
    assert "0" in text


# --------------------------------------- what the passes bought and cost
def test_the_five_the_passes_catch_are_named():
    gained = [r["test"] for r in RESULTS
              if r["expected"] == "REJECTED"
              and r["term_only"] == "ACCEPTED"
              and r["with_spec_passes"] == "REJECTED"]
    assert len(gained) == 5, gained
    names = " ".join(gained)
    for n in ("large-elim-prop-bool", "nat-rec-rules", "indNeg"):
        assert n in names


def test_the_three_false_rejections_the_passes_cause_are_named_as_a_bug():
    """Not reported as a scope limit: the iota pass decides recursiveness
    syntactically where Lean decides it after delta-reduction, so it rejects
    valid rules."""
    caused = [r["test"] for r in RESULTS
              if r["expected"] == "ACCEPTED"
              and r["term_only"] != "REJECTED"
              and r["with_spec_passes"] == "REJECTED"]
    assert len(caused) == 3, caused
    assert all("reduceCtorParam" in c for c in caused), caused
    text = flat(rec["analysis"]["what_the_passes_cost"])
    assert "delta-reduction" in text or "δ-reduction" in text
    assert "could not have found this" in text


def test_the_record_says_the_differential_could_not_have_found_it():
    """The reason this matters beyond the three tests: a clean differential
    over 3410 recursors is not evidence about shapes the libraries lack."""
    text = flat(rec["analysis"]["what_the_passes_cost"])
    assert "Init and Mathlib" in text
    assert "3410" in text


def test_the_good_bad_pair_is_recorded():
    """055 and 056 are the same shape in the two directions, and the pass gets
    both wrong. Nothing states the problem better, so the record keeps it."""
    assert BY_TEST["good/tutorial/055_reduceCtorParam.mk.ndjson"]["with_spec_passes"] == "REJECTED"
    assert BY_TEST["bad/tutorial/056_reduceCtorType.mk.ndjson"]["with_spec_passes"] == "ACCEPTED"
    assert "055" in flat(rec["analysis"]["what_the_passes_cost"])


# ----------------------------------------------------- honesty of the rest
def test_every_wrongly_accepted_test_is_assigned_a_cause():
    causes = rec["analysis"]["wrongly_accepted_by_cause"]
    assigned = {n for xs in causes.values() for n in xs}
    actual = {r["test"].split("/")[-1].replace(".ndjson", "")
              for r in RESULTS
              if r["expected"] == "REJECTED" and r["with_spec_passes"] == "ACCEPTED"}
    assert actual == assigned, (actual ^ assigned)


def test_the_four_that_are_our_own_bugs_are_called_bugs():
    text = flat(rec["analysis"]["what_is_not_claimed"]).lower()
    assert "large-elim-param" in text
    assert "orphan-rec" in text
    assert "accepting direction" in text
    assert "out of scope" in text


def test_the_declines_distinguish_the_reader_from_the_checker():
    text = flat(rec["analysis"]["declines"])
    assert "READER" in text or "reader" in text
    assert "timeout is not a verdict" in text
    dec = [r["test"] for r in RESULTS if r["with_spec_passes"] == "DECLINED"]
    assert len(dec) == 10
    assert sum(1 for t in dec if "dup" in t.lower()) == 6


def test_the_containment_in_our_own_pipeline_is_not_used_as_an_excuse():
    text = flat(rec["analysis"]["headline"])
    assert "provenance gate" in text
    assert "not an excuse" in text
    assert "unknown provenance" in text


def test_the_document_and_the_record_agree():
    doc = DOC.read_text(encoding="utf-8")
    for cfg, n in (("term_only", 28), ("with_spec_passes", 23)):
        assert str(n) in doc
    assert "055" in doc and "056" in doc
    assert "not an excuse" in doc


# ---------------------------------------------------------------------------
# After the five fixes (same day). The before-record above stays untouched, so
# the improvement is a diff rather than a number edited in place.
AFTER = ROOT / "evidence" / "arena_run_after_fixes.json"
after = json.loads(AFTER.read_text(encoding="utf-8"))


def test_the_improvement_is_recorded_as_a_comparison_not_a_replacement():
    c = after["comparison"]
    assert c["against"].startswith("evidence/arena_run.json")
    assert c["before"] == rec["totals"], (
        "the comparison must quote the before-record's own totals")


def test_wrongly_accepted_fell_and_wrongly_rejected_returned_to_baseline():
    b = after["comparison"]["before"]["with_spec_passes"]
    a = after["comparison"]["after"]["with_spec_passes"]
    assert (b["wrongly_accepted"], a["wrongly_accepted"]) == (23, 9)
    assert (b["wrongly_rejected"], a["wrongly_rejected"]) == (12, 9)
    # the passes now cost nothing: 9 is the term layer's own figure
    assert a["wrongly_rejected"] == after["totals"]["term_only"]["wrongly_rejected"]


def test_the_after_totals_are_recomputable_from_its_own_rows():
    for cfg in ("term_only", "with_spec_passes"):
        wa = sum(1 for r in after["results"]
                 if r["expected"] == "REJECTED" and r[cfg] == "ACCEPTED")
        assert after["totals"][cfg]["wrongly_accepted"] == wa, cfg


def test_the_three_false_rejections_became_declines_not_acceptances():
    """The iota fix had to move them out of REJECTED without moving them into
    a wrong ACCEPTED: they are good tests, so accepting them is correct, and
    the pass reaching that by declining is the honest route."""
    for name in after["comparison"]["false_rejections_removed"]:
        row = next(r for r in after["results"] if name in r["test"])
        assert row["with_spec_passes"] == "ACCEPTED", name
        assert row["expected"] == "ACCEPTED", name


def test_the_six_incidental_catches_are_called_incidental():
    """The fixes targeted five tests and the count moved by fourteen. An
    unexplained improvement is as suspicious as an unexplained regression, and
    six of the fourteen are rejected by a rule that has nothing to do with
    their defect."""
    inc = after["comparison"]["the_six_incidental_catches"]
    assert len(inc["tests"]) == 6
    assert "0 motives" in inc["all_rejected_by"]
    why = " ".join(inc["why_this_is_not_a_capability"])
    assert "does not check inductive well-formedness" in why
    assert "STUB" in why or "stub" in why
    assert "would accept these six again" in why
    assert "scores mechanisms" in why


def test_the_remaining_nine_are_scope_and_say_which_scope():
    s = after["comparison"]["still_wrongly_accepted"]
    assert s["count"] == 9
    named = sum(len(v) for k, v in s.items()
                if isinstance(v, list) and k not in ("reading",))
    assert named == 9, "every remaining miss must be under a named cause"
    why = " ".join(s["reading"])
    assert "not bugs in it" in why
    assert "full kernel" in why
    assert "047" in why and "049" in why, (
        "the two that would look like the incidental six must be named")


def test_the_document_carries_both_numbers():
    doc = DOC.read_text(encoding="utf-8")
    assert "23 → 9" in doc
    assert "12 → 9" in doc
    assert "caught for the wrong reason" in doc
