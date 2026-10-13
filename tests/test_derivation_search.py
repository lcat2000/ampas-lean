"""Offline tests for the bounded derivation search (no Lean needed).

Two things are pinned here, and they are different in kind:

  * PL-BOGUS is REFUTED, and the refutation was accepted by the Lean kernel
    after being checked against the frozen statement. That is a proof the
    statement is false.
  * The other three are NO_DERIVATION, which is not a proof of anything. It
    says no derivation was found inside a stated universe. The record must
    carry that universe, and these tests fail if it does not, because
    "searched, nothing found" without a bound is a sentence that sounds like
    evidence and is not.

The tests also check the thing a search is most likely to get wrong in a way
nobody notices: that what the refutation negates is the frozen statement and
not something adjacent to it. That is the FermatWeaker failure mode, applied
to refutations instead of proofs.
"""
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "reference" / "derivation_search.json"
CLAIMS = ROOT / "reference" / "claims.json"


def records() -> dict:
    return {r["claim"]: r
            for r in json.loads(RECORD.read_text(encoding="utf-8"))["searches"]}


def test_all_four_independence_claims_are_covered():
    """These four are exactly the claims the numeric search reports
    NOT_SEARCHABLE, which is why this search exists."""
    recs = records()
    numeric = {r["claim"]: r for r in json.loads(
        (ROOT / "reference" / "counterexample_search.json").read_text(encoding="utf-8")
    )["searches"]}
    unreachable = {c for c, r in numeric.items() if r["outcome"] == "NOT_SEARCHABLE"}
    assert unreachable <= set(recs), (
        f"claims the numeric search cannot reach and this one does not cover: "
        f"{sorted(unreachable - set(recs))}")


@pytest.mark.parametrize("claim", ["PL-IND", "PL-AXIOM-IND", "EL-IND"])
def test_a_negative_result_states_its_bound(claim):
    r = records()[claim]
    assert r["outcome"] == "NO_DERIVATION"
    b = r["bound"]
    if claim == "EL-IND":
        assert b["parts"], "no bound for either part"
        for part in b["parts"]:
            assert part["derivable"] is False
            assert part["bound"]["term_universe"] > 0
            assert part["bound"]["axiom_instances"] > 0
            # a capped universe is a weaker result and has to say so
            assert "universe_capped" in part["bound"]
    else:
        assert b["formula_universe"] > 0 and b["rounds"] > 0
        assert b["formulas_derived"] > b["axiom_instances"] // 100, (
            "implausibly few formulas derived for the instances generated")
        assert b["fragment"] in ("A1,A2,MP", "A1,A2,A3,MP")
    assert r["why"], f"{claim}: no stated reason for what the result means"


def test_pl_bogus_is_refuted_and_the_kernel_said_so():
    """The payoff. Before this, PL-BOGUS was a declared-false control whose
    falsity rested on a reviewer's reading: nothing in the repository proved
    it false, only that nobody could prove it true."""
    r = records()["PL-BOGUS"]
    assert r["outcome"] == "REFUTED"
    k = r["kernel"]
    assert k["elaborates"], "the witness did not even elaborate"
    assert k["kernel_replay"] and k["kernel_replay_fresh"], (
        "elaboration is not the kernel; both replays must accept the witness")
    sc = k["statement_check"]
    assert sc["is_theorem"], "a refutation that is not a theorem proves nothing"
    assert sc["negates_frozen_statement_structurally"], (
        "the witness refutes something OTHER than the frozen statement")
    assert sc["negates_frozen_statement_up_to_defeq"]
    assert not sc["uses_sorry"], "a refutation resting on sorry is worthless"
    assert sc["axioms"] == [], (
        f"expected no axioms at all; got {sc['axioms']}")
    assert not sc["foreign_statement_constants"], (
        "the refutation's statement mentions constants the trusted reference "
        "does not define, so it could be about its own version of Derives")
    assert r["derivation"], "refuted with no derivation recorded"


def test_the_recorded_derivation_is_a_well_formed_proof():
    """Each step is an axiom instance, a hypothesis, or modus ponens on two
    EARLIER steps. A step citing a later one would be a cycle the kernel would
    catch, but the record should not contain one in the first place."""
    r = records()["PL-BOGUS"]
    steps = r["derivation"]
    for n, s in enumerate(steps):
        assert s["rule"] in ("hyp", "a1", "a2", "a3", "mp"), s["rule"]
        assert s["formula"].startswith("("), s["formula"]
    assert steps[-1]["rule"] == "mp", "the last step should conclude by MP"
    assert len(steps) >= 3


def test_the_false_control_no_longer_rests_on_a_waiver():
    """PL-BOGUS used to carry `falsity_not_searchable` in the bounds file --
    a stated admission that nothing mechanical backed its falsity. With a
    kernel-checked refutation on record, that waiver must be gone, or the
    repository is claiming less than it can show."""
    b = json.loads((ROOT / "reference" / "counterexample_bounds.json")
                   .read_text(encoding="utf-8"))
    pl = b["claims"].get("PL-BOGUS", {})
    assert "falsity_not_searchable" not in pl, (
        "PL-BOGUS still has a falsity waiver, but it is refuted by the "
        "derivation search; remove the waiver or explain why it is still needed")
    assert pl.get("why")


def test_every_declared_false_control_is_refuted_somewhere():
    """The invariant the gate enforces, checked offline across both searches:
    a claim the catalogue says is FALSE must be refuted by the numeric search,
    or by a kernel-checked derivation, or carry a stated waiver. Never by
    silence."""
    numeric = {r["claim"]: r for r in json.loads(
        (ROOT / "reference" / "counterexample_search.json").read_text(encoding="utf-8")
    )["searches"]}
    derivation = records()
    bounds = json.loads((ROOT / "reference" / "counterexample_bounds.json")
                        .read_text(encoding="utf-8"))["claims"]
    for c in json.loads(CLAIMS.read_text(encoding="utf-8"))["claims"]:
        if (c.get("control") or {}).get("target_claim_is_true") is not False:
            continue
        cid = c["id"]
        ok = (numeric.get(cid, {}).get("outcome") == "REFUTED"
              or derivation.get(cid, {}).get("outcome") == "REFUTED"
              or bounds.get(cid, {}).get("falsity_not_searchable"))
        assert ok, f"{cid}: declared false and nothing refutes it"
