"""The historical corpus (ROADMAP 6) and what it is allowed to claim.

Three episodes where the verdict was settled by someone else, long before this
repository existed: Mersenne's 1644 list at p = 67 against Cole's 1903
factorization, Euler's 1769 sum-of-powers conjecture at n = 5 against Lander
and Parkin's 1966 counterexample, and the universal over-reading of Euler's
1772 polynomial against its failure at n = 40.

The corpus's structural weakness is that it was written by whoever wrote the
harness. A claim drawn from history is the one kind that cannot have been
tuned to this suite: the right answer is not ours to set. What IS still ours,
and is therefore what these tests guard, is the **formalization** — whether
each Lean statement says what the historical sentence says — and the honesty
of the records: that a false claim is recorded as false with an external
citation, that no sign-off is claimed that nobody gave, and that a search
which cannot reach a counterexample says so rather than reading as evidence.
"""
import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))

CAT = ROOT / "reference" / "claims_history.json"
MANIFEST = ROOT / "corpus" / "manifest_history.json"
BOUNDS = ROOT / "reference" / "counterexample_bounds.json"
RESULTS = ROOT / "evidence" / "history_validation.json"
ABLATION = ROOT / "evidence" / "ablation_external.json"
SEARCH = ROOT / "reference" / "counterexample_search_history.json"

catalogue = json.loads(CAT.read_text(encoding="utf-8"))
manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
CLAIMS = {c["id"]: c for c in catalogue["claims"]}

FALSE_CLAIMS = {"MERSENNE-67", "EULER-SUM-5", "EULER-POLY"}
TRUE_CLAIMS = {"COLE-67", "LANDER-PARKIN", "EULER-POLY-40"}


# ------------------------------------------------- the catalogue's honesty
def test_every_claim_is_either_a_false_control_or_a_refutation():
    assert set(CLAIMS) == FALSE_CLAIMS | TRUE_CLAIMS
    for cid in FALSE_CLAIMS:
        assert CLAIMS[cid].get("control"), cid
    for cid in TRUE_CLAIMS:
        assert CLAIMS[cid].get("guards"), cid


@pytest.mark.parametrize("cid", sorted(FALSE_CLAIMS))
def test_a_false_claim_says_so_in_the_field_the_harness_reads(cid):
    """`target_claim_is_true: false` is what harness/counterexample.py checks.
    An earlier draft of this catalogue wrote `target_claim_is: "false"`, which
    reads correctly to a human and is invisible to the code -- the search
    reported REFUTED_BUT_NOT_DECLARED_FALSE against MERSENNE-67 and that is
    how it was found."""
    ctl = CLAIMS[cid]["control"]
    assert ctl.get("target_claim_is_true") is False
    assert ctl.get("must_never_be_certified") is True
    assert ctl.get("why_false")
    assert ctl.get("refuted_by") in TRUE_CLAIMS


@pytest.mark.parametrize("cid", sorted(FALSE_CLAIMS))
def test_the_reason_a_claim_is_false_cites_someone_outside_this_repository(cid):
    """The whole point of a historical claim is that the verdict is external.
    A `why_false` that argued the point itself would give that away."""
    why = CLAIMS[cid]["control"]["why_false"]
    assert any(y in why for y in ("1903", "1966", "41 * 41")), why


@pytest.mark.parametrize("cid", sorted(FALSE_CLAIMS))
def test_faithful_is_scoped_to_the_target_claim_not_its_truth(cid):
    """`faithful: true` on a false claim must not read as "this is true". The
    note that separates the two was a reviewer's finding on the Fermat pair
    (2026-10-13) and applies to every control added since."""
    ctl = CLAIMS[cid]["control"]
    note = ctl.get("note_on_faithful", "")
    assert "TARGET CLAIM" in note or "formalizes" in note, cid
    assert CLAIMS[cid]["review"]["faithful"] is True


def test_no_sign_off_is_claimed_that_nobody_gave():
    """These six formalizations are the assistant's. Nobody has reviewed them.
    Every review block must say so -- in `reviewed_by` and `confirmed_by`,
    which is where a reader looks, not only in the catalogue's notes."""
    for cid, c in CLAIMS.items():
        r = c["review"]
        assert "PENDING" in r["reviewed_by"], cid
        assert r["confirmed_by"] == "PENDING", cid
        assert r["confirmed_on"] is None, cid
        assert r["confirmation_mode"] == "none", cid
    assert "PENDING" in catalogue["notes"]


def test_the_catalogue_names_what_is_still_this_repositorys_to_get_wrong():
    """A corpus drawn from history fixes the verdict, not the formalization.
    If this sentence goes, the catalogue starts reading as though external
    provenance settled everything."""
    notes = catalogue["notes"]
    assert "FORMALIZATION" in notes or "formalization" in notes
    assert "not this repository's to set" in notes or "not ours to set" in notes


# ----------------------------------------------------- manifest and corpus
def test_every_submission_targets_a_claim_in_this_catalogue():
    for s in manifest["submissions"]:
        for cid in s["claims"]:
            assert cid in CLAIMS, (s["module"], cid)


def test_no_submission_against_a_false_claim_is_expected_to_certify():
    for s in manifest["submissions"]:
        if any(c in FALSE_CLAIMS for c in s["claims"]):
            assert s["expected"] == "rejected", s["module"]


def test_both_halves_of_every_pair_are_exercised():
    """A system that rejected everything would pass the false half of all
    three episodes. Each true refutation needs a submission expected to
    CERTIFY, or the pair proves nothing."""
    certifying = {c for s in manifest["submissions"]
                 if s["expected"] == "certified_all" for c in s["claims"]}
    assert TRUE_CLAIMS <= certifying, TRUE_CLAIMS - certifying


def test_each_submission_file_exists():
    for s in manifest["submissions"]:
        assert (ROOT / "corpus" / s["file"]).exists(), s["file"]


# -------------------------------------------------------- the search boxes
@pytest.mark.parametrize("cid", sorted(FALSE_CLAIMS | TRUE_CLAIMS))
def test_every_claim_has_a_recorded_search_box_with_a_reason(cid):
    """A bound is part of what a NO_COUNTEREXAMPLE result means, so it lives in
    the reference tree with the reason it was chosen."""
    b = json.loads(BOUNDS.read_text(encoding="utf-8"))["claims"]
    assert cid in b, cid
    assert b[cid].get("why"), cid


def test_the_unreachable_counterexample_is_recorded_as_a_limit():
    """EULER-SUM-5 is false and this search cannot find its counterexample:
    Lander and Parkin's witness needs 144 in five variables. The box must say
    that plainly, because a NO_COUNTEREXAMPLE result on a false claim is the
    one result most easily misread as evidence."""
    why = json.loads(BOUNDS.read_text(encoding="utf-8"))["claims"]["EULER-SUM-5"]["why"]
    assert "144" in why
    assert "FALSE" in why or "false" in why
    assert "NO_COUNTEREXAMPLE" in why


def test_the_reachable_counterexample_is_claimed_as_reachable():
    """EULER-POLY's counterexample at n = 40 sits inside the box, so the search
    must refute it on its own. If it ever does not, that is a defect in the
    search rather than a fact about the claim, and the box says so."""
    why = json.loads(BOUNDS.read_text(encoding="utf-8"))["claims"]["EULER-POLY"]["why"]
    assert "40" in why
    assert "defect in the search" in why


# ------------------------------------------------------ the stored results
@pytest.mark.skipif(not RESULTS.exists(), reason="run tier 3 to produce it")
def test_the_stored_results_match_the_manifest():
    res = json.loads(RESULTS.read_text(encoding="utf-8"))["results"]
    by_mod = {r["module"]: r for r in res}
    assert len(by_mod) == len(manifest["submissions"])
    for s in manifest["submissions"]:
        r = by_mod[s["module"]]
        certs = [c["certified"] for c in r["claims"]]
        got = "certified_all" if certs and all(certs) else "rejected"
        assert got == s["expected"], s["module"]


@pytest.mark.skipif(not RESULTS.exists(), reason="run tier 3 to produce it")
def test_no_false_claim_was_ever_certified():
    """The one outcome that would be a defect rather than a finding."""
    res = json.loads(RESULTS.read_text(encoding="utf-8"))["results"]
    for r in res:
        for c in r["claims"]:
            if c["claim"] in FALSE_CLAIMS:
                assert not c["certified"], (r["module"], c["claim"])


@pytest.mark.skipif(not RESULTS.exists(), reason="run tier 3 to produce it")
def test_no_attack_was_rejected_only_by_failing_to_compile():
    """A submission that does not build is rejected by the build, which is
    evidence about nothing. Every attack here must compile and be rejected by
    a named layer."""
    res = json.loads(RESULTS.read_text(encoding="utf-8"))["results"]
    for r in res:
        if r.get("expected") != "rejected":
            continue
        assert r["compiled"], r["module"]


@pytest.mark.skipif(not ABLATION.exists(), reason="run tier 3 to produce it")
def test_every_external_attack_has_an_attributed_layer():
    """The gap this corpus exposed: ablation.py identified attacks by an `A`
    naming prefix, so all four Fermat attacks and all eight history ones fell
    out of the table -- and the table then said "0 attacks, all rejected:
    True" about the corpus added precisely to answer "the corpus was written
    by whoever wrote the harness"."""
    rows = json.loads(ABLATION.read_text(encoding="utf-8"))
    assert rows, "the external ablation table is empty"
    for r in rows:
        assert r["verdict"] == "REJECTED", r["attack"]
        assert r["signals"], r["attack"]
    names = {r["attack"] for r in rows}
    assert "MersenneSorry" in names
    assert "FermatWeaker" in names, (
        "the Fermat attacks are still missing from the attribution table")


@pytest.mark.skipif(not ABLATION.exists(), reason="run tier 3 to produce it")
def test_more_than_one_layer_fires_across_the_external_corpus():
    """If every external attack were caught by one layer, the other layers
    would be doing nothing on externally-set claims whatever the core table
    shows."""
    rows = json.loads(ABLATION.read_text(encoding="utf-8"))
    fired = {s for r in rows for s in r["signals"]}
    assert len(fired) >= 3, fired


def test_ablation_identifies_attacks_from_the_record_not_the_module_name():
    """Source-level, because the naming-convention version looked right and
    silently covered only one corpus."""
    import ablation
    assert ablation.is_attack({"expected": "rejected"})
    assert not ablation.is_attack({"expected": "certified_all"})
    assert not ablation.is_attack({"module": "A99_looks_like_an_attack"})
    src = (ROOT / "harness" / "ablation.py").read_text(encoding="utf-8")
    assert 'startswith("A")' not in src


@pytest.mark.skipif(not SEARCH.exists(), reason="run tier 3 to produce it")
def test_the_search_refuted_the_reachable_claim_and_not_the_other():
    rec = json.loads(SEARCH.read_text(encoding="utf-8"))
    by = {s["claim"]: s for s in rec["searches"]}
    assert by["EULER-POLY"]["outcome"] == "REFUTED", by["EULER-POLY"]
    assert by["EULER-SUM-5"]["outcome"] == "NO_COUNTEREXAMPLE"
    assert by["EULER-SUM-5"].get("consistency") == "OK", (
        "a false claim the search cannot reach must still be recorded "
        "consistently, by its refuting claim or a stated reason")
