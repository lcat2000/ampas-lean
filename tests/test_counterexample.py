"""Offline tests for the bounded counterexample search (no Lean needed).

These pin what a clean search result is allowed to mean. The failure mode they
exist to prevent is the one that makes every other gate decorative: a result
that reads as "attacked and survived" when the search never ran, ran against a
different statement, or could not decide anything at all.

They run against the COMMITTED records, so they also catch a record that was
regenerated without the attestations being re-frozen.
"""
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent

CATALOGUES = [
    ("reference/claims.json", "reference/counterexample_search.json",
     "reference/attestations"),
    ("reference/claims_mathlib.json", "reference/counterexample_search_mathlib.json",
     "reference/attestations-mathlib"),
    ("reference/claims_fermat.json", "reference/counterexample_search_fermat.json",
     "reference/attestations-fermat"),
]

OUTCOMES = {"REFUTED", "NO_COUNTEREXAMPLE", "NO_COUNTEREXAMPLE_PARTIAL",
            "NOT_SEARCHABLE", "INCONCLUSIVE"}


def load(cat_rel, cex_rel, _attest):
    cat = json.loads((ROOT / cat_rel).read_text(encoding="utf-8"))
    cex = json.loads((ROOT / cex_rel).read_text(encoding="utf-8"))
    return cat, {r["claim"]: r for r in cex["searches"]}


@pytest.mark.parametrize("cat_rel,cex_rel,attest", CATALOGUES)
def test_every_claim_has_a_search_record(cat_rel, cex_rel, attest):
    cat, recs = load(cat_rel, cex_rel, attest)
    for c in cat["claims"]:
        r = recs.get(c["id"])
        assert r is not None, f"{c['id']}: no counterexample search on record"
        assert r["outcome"] in OUTCOMES, f"{c['id']}: unknown outcome {r['outcome']}"
        assert r.get("statement_sha256"), (
            f"{c['id']}: the search record names no statement, so nothing ties it "
            f"to what was actually searched")


@pytest.mark.parametrize("cat_rel,cex_rel,attest", CATALOGUES)
def test_the_signed_attestation_carries_the_same_search(cat_rel, cex_rel, attest):
    """The record in the file and the record under the signature must agree.

    They can diverge in the direction that matters: re-running the search and
    committing the result WITHOUT re-freezing leaves the attestations vouching
    for an older search while the file shows the newer one."""
    cat, recs = load(cat_rel, cex_rel, attest)
    for c in cat["claims"]:
        p = ROOT / attest / f"{c['id']}.json"
        if not p.exists():
            pytest.skip(f"{c['id']} is not frozen")
        block = json.loads(p.read_text(encoding="utf-8")).get("counterexample_search")
        assert block, f"{c['id']}: the attestation records no counterexample search"
        f = recs[c["id"]]
        for k in ("outcome", "statement_sha256", "bound", "exists_bound"):
            assert block.get(k) == f.get(k), (
                f"{c['id']}: the signed attestation says {k}={block.get(k)!r} but "
                f"{cex_rel} says {f.get(k)!r} -- re-freeze after re-searching")
        assert block["statement_sha256"] == json.loads(p.read_text(encoding="utf-8"))["statement_sha256"], (
            f"{c['id']}: the search inside the attestation is about a different "
            f"statement than the attestation itself freezes")


@pytest.mark.parametrize("cat_rel,cex_rel,attest", CATALOGUES)
def test_a_refuted_statement_must_be_a_declared_control(cat_rel, cex_rel, attest):
    cat, recs = load(cat_rel, cex_rel, attest)
    for c in cat["claims"]:
        if recs[c["id"]]["outcome"] != "REFUTED":
            continue
        ctrl = c.get("control") or {}
        assert ctrl.get("target_claim_is_true") is False, (
            f"{c['id']}: refuted by counterexample {recs[c['id']].get('witness')} "
            f"but not annotated as a false-claim control")
        assert ctrl.get("must_never_be_certified") is True


@pytest.mark.parametrize("cat_rel,cex_rel,attest", CATALOGUES)
def test_an_undecidable_search_is_never_a_pass(cat_rel, cex_rel, attest):
    """NOT_SEARCHABLE and INCONCLUSIVE are gaps, and a claim the record calls
    FALSE must either be refuted mechanically or carry a stated reason why the
    search cannot reach its falsity. Silence is what this forbids."""
    cat, recs = load(cat_rel, cex_rel, attest)
    for c in cat["claims"]:
        r = recs[c["id"]]
        if r["outcome"] in ("NOT_SEARCHABLE", "INCONCLUSIVE"):
            assert r.get("reason"), f"{c['id']}: {r['outcome']} without a reason"
        declared_false = (c.get("control") or {}).get("target_claim_is_true") is False
        if declared_false and r["outcome"] != "REFUTED":
            # Something must back the falsity: this search, the bounded
            # derivation search whose witness the kernel checked, or a stated
            # reason why neither can reach it. Silence is what is forbidden.
            assert r.get("refuted_by") or r.get("falsity_not_searchable"), (
                f"{c['id']}: recorded as false, not refuted by this search, no "
                f"derivation refutation on record, and no stated reason why "
                f"neither can reach it")
        assert r.get("consistency") == "OK", (
            f"{c['id']}: unresolved finding {r.get('consistency')}")


def test_the_fermat_claim_is_refuted_at_n_equals_five():
    """The external validation the whole search was built against.

    Fermat (c. 1640) asserted every F_n is prime having checked F_0..F_4;
    Euler (1732) refuted it at F_5. A search that cannot reproduce that has no
    claim on anyone's trust, so the witness is pinned rather than described."""
    recs = {r["claim"]: r for r in json.loads(
        (ROOT / "reference" / "counterexample_search_fermat.json").read_text(encoding="utf-8"))["searches"]}
    r = recs["FERMAT-CLAIM"]
    assert r["outcome"] == "REFUTED"
    assert r["witness"] == [5], f"expected the counterexample at n=5, got {r['witness']}"
    # Euler's refutation itself must survive: a search that refuted both would
    # be refuting the statement rather than the claim.
    assert recs["FERMAT-F5"]["outcome"].startswith("NO_COUNTEREXAMPLE")


def test_a_partial_box_says_how_partial():
    """`NO_COUNTEREXAMPLE` over a box that was mostly undecided means much less
    than one over a box that was not, so the counts have to be there."""
    for _, cex_rel, _ in CATALOGUES:
        for r in json.loads((ROOT / cex_rel).read_text(encoding="utf-8"))["searches"]:
            if not r["outcome"].startswith("NO_COUNTEREXAMPLE"):
                continue
            assert "box_size" in r and "checked_points" in r, f"{r['claim']}: no counts"
            assert r["checked_points"] <= r["box_size"]
            if r["outcome"].endswith("PARTIAL"):
                assert r.get("unresolved_points", 0) > 0, (
                    f"{r['claim']}: reported PARTIAL with nothing unresolved")
            else:
                assert r.get("unresolved_points", 0) == 0


def test_the_bounds_are_committed_and_explained():
    """The box is part of what a result means, so it lives in the reference
    tree where changing it is reviewable -- not in a default inside the code."""
    b = json.loads((ROOT / "reference" / "counterexample_bounds.json").read_text(encoding="utf-8"))
    assert b["default"]["bound"] >= 1 and b["default"]["exists_bound"] >= 1
    for cid, c in b.get("claims", {}).items():
        assert c.get("why") or c.get("falsity_not_searchable"), (
            f"{cid}: a per-claim box with no stated reason for it")
