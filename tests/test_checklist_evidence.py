"""The fidelity checklist's per-item evidence (ROADMAP 5.4).

Thirteen signed attestations, six checklist booleans each, all `true`. Every
mechanical layer this repository has added detects FALSITY or MALFORMEDNESS;
`docs/CONLECHE-EVALUATION.md` settled that no kernel closes the remaining gap,
because con-leche -- which carries a ZFC model-theoretic consistency proof --
accepts `A06_wrong_statement`. So the six booleans are the weakest link in the
pipeline and were the only part of it never touched.

They were also **wholesale**: a reviewer who thought hard and one who ticked
six boxes left byte-identical records. These tests pin what the evidence must
point at, and -- more importantly -- pin the two things it must NOT be allowed
to claim: that `statement_matches_text` has machine backing, and that a
reviewer saw evidence derived after they signed.
"""
import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))

CHECKLIST = [
    "statement_matches_text",
    "no_unintended_convention",
    "quantifier_order_checked",
    "hypotheses_necessary_and_satisfiable",
    "definitions_reviewed",
    "conclusion_not_weakened",
]

EVIDENCE = {
    "reference/checklist-evidence.json": "reference/attestations",
    "reference/checklist-evidence-mathlib.json": "reference/attestations-mathlib",
    "reference/checklist-evidence-fermat.json": "reference/attestations-fermat",
}


def load(p: str) -> dict:
    return json.loads((ROOT / p).read_text(encoding="utf-8"))


def conventions() -> dict:
    return load("reference/fidelity_conventions.json")


def all_claims():
    for ev_path, att_dir in EVIDENCE.items():
        for cid, c in load(ev_path)["claims"].items():
            yield ev_path, att_dir, cid, c


# ---- the record exists and covers the checklist

def test_every_signed_attestation_has_evidence():
    """The requirement that makes this layer real: an attestation with no
    per-item evidence does not verify."""
    for ev_path, att_dir in EVIDENCE.items():
        ev = load(ev_path)
        for att in sorted((ROOT / att_dir).glob("*.json")):
            cid = json.loads(att.read_text(encoding="utf-8"))["claim"]
            assert cid in ev["claims"], f"{cid} is attested but has no evidence in {ev_path}"


def test_each_claim_covers_exactly_the_six_items():
    for ev_path, _, cid, c in all_claims():
        assert set(c["items"]) == set(CHECKLIST), f"{ev_path}:{cid}"


def test_evidence_is_bound_to_the_attested_statement():
    """Evidence derived from a different statement than the one signed off is
    not evidence. `ampas_review.py verify` recomputes the hash from the live
    reference; this checks the committed records agree with each other."""
    for ev_path, att_dir, cid, c in all_claims():
        att = ROOT / att_dir / f"{cid}.json"
        if not att.exists():
            continue
        signed = json.loads(att.read_text(encoding="utf-8"))["statement_sha256"]
        assert c["statement_sha256"] == signed, (
            f"{cid}: the evidence was derived from a statement other than the "
            f"one the attestation pins")


# ---- the one item with nothing behind it

def test_statement_matches_text_is_marked_as_having_no_machine_evidence():
    for ev_path, _, cid, c in all_claims():
        it = c["items"]["statement_matches_text"]
        assert it["machine_derivable"] is False, f"{ev_path}:{cid}"
        assert "A06_wrong_statement" in it["why_not"], (
            "the reason must cite the measurement that settles it, not assert it")


def test_it_is_the_only_item_without_machine_evidence():
    """Five of six having evidence is the honest shape. If a sixth ever
    appears, something was put beside `statement_matches_text` that answers a
    different question than the one asked."""
    for ev_path, _, cid, c in all_claims():
        without = [k for k, v in c["items"].items() if not v.get("machine_derivable")]
        assert without == ["statement_matches_text"], f"{ev_path}:{cid}: {without}"
    for ev_path in EVIDENCE:
        d = load(ev_path)
        assert d["items_with_no_machine_evidence"] == ["statement_matches_text"]
        assert d["totals"]["machine_derivable_items"] == len(CHECKLIST) - 1


def test_the_unverifiable_item_still_puts_both_readings_side_by_side():
    """No machine evidence is not the same as no material: the reviewer's job
    is a comparison, so the record carries both halves of it."""
    for ev_path, _, cid, c in all_claims():
        m = c["items"]["statement_matches_text"]["material_to_read"]
        assert m["claim_text"].strip(), f"{ev_path}:{cid}"
        assert m["conclusion"].strip(), f"{ev_path}:{cid}"


# ---- what the mechanisable ticks point at

def test_binder_identity_is_the_index_not_the_name():
    """An anonymous binder (`∀ a b, b ≤ a → …`) gets a machine-generated name
    and every one of them gets the SAME one, so a tick citing a hypothesis by
    name would be ambiguous exactly where hypotheses matter most. The auditor
    reports null rather than a name that does not distinguish."""
    seen_null = False
    for ev_path, _, cid, c in all_claims():
        seq = c["items"]["quantifier_order_checked"]["binder_sequence"]
        assert [b["index"] for b in seq] == list(range(len(seq))), f"{ev_path}:{cid}"
        named = [b["name"] for b in seq if b["name"] is not None]
        assert len(named) == len(set(named)), f"{ev_path}:{cid}: duplicate binder names"
        for b in seq:
            if b["name"] is None:
                seen_null = True
            else:
                assert "_@" not in b["name"] and "hyg" not in b["name"], (
                    f"{ev_path}:{cid}: a machine-generated name leaked into the record")
    assert seen_null, (
        "no anonymous binder anywhere: either the corpus lost its unnamed "
        "hypotheses or the auditor started inventing names for them")


def test_the_order_hash_changes_under_a_permutation():
    """`quantifier_order_checked` is about the ORDER. A hash over the binder
    types alone would be blind to `∀ a, ∃ b` versus `∃ b, ∀ a`, which is the
    single most common fidelity failure there is."""
    import hashlib

    def order_hash(rows):
        return hashlib.sha256("\n".join(
            f"{i}\t{k}\t{h}" for i, (k, h) in enumerate(rows)).encode()).hexdigest()

    a = [("data", "X"), ("hypothesis", "Y")]
    assert order_hash(a) != order_hash(list(reversed(a)))
    # and the recorded hashes are over the recorded sequences
    for ev_path, _, cid, c in all_claims():
        q = c["items"]["quantifier_order_checked"]
        want = hashlib.sha256("\n".join(
            f"{b['index']}\t{b['kind']}\t{b['type_sha256']}"
            for b in q["binder_sequence"]).encode("utf-8")).hexdigest()
        assert q["order_sha256"] == want, f"{ev_path}:{cid}"


def test_data_and_hypothesis_counts_agree_with_the_sequence():
    for ev_path, _, cid, c in all_claims():
        q = c["items"]["quantifier_order_checked"]
        seq = q["binder_sequence"]
        assert q["data_binders"] == sum(1 for b in seq if b["kind"] == "data")
        assert q["hypothesis_binders"] == sum(1 for b in seq if b["kind"] == "hypothesis")
        assert len(c["items"]["hypotheses_necessary_and_satisfiable"]["hypotheses"]) \
            == q["hypothesis_binders"], f"{ev_path}:{cid}"


def test_the_hypotheses_tick_cannot_cover_fewer_hypotheses_than_the_statement_has():
    """The item with actual teeth: a tick on
    `hypotheses_necessary_and_satisfiable` is a claim about every hypothesis,
    and the guards are what back it. Two hypotheses with one necessity guard
    means the tick covers one of them."""
    for ev_path, _, cid, c in all_claims():
        g = c["items"]["hypotheses_necessary_and_satisfiable"]["guard_coverage"]
        assert g["consistent"] is True, f"{ev_path}:{cid}: {g}"
        if g.get("non_vacuity_status") == "REFUTATION":
            # `¬ P` is `P → False`: the telescope sees a binder, the sanity
            # pass reports zero hypotheses. Two records of one statement
            # disagreeing is how the A01 mislabel survived nine rounds, so the
            # disagreement is RECONCILED IN THE RECORD rather than resolved by
            # silently preferring one of them.
            assert "reconciliation" in g, (
                f"{cid}: a refutation's hypothesis count differs between the "
                f"two passes and nothing in the record explains why")
            assert g["nontriviality"], f"{cid}: refutation cites no nontriviality guard"
        else:
            assert g["hypothesis_binders"] == g["guards_hypotheses"] == g["necessity_guards"]


def test_definitions_reviewed_names_the_projects_own_definitions():
    for ev_path, _, cid, c in all_claims():
        d = c["items"]["definitions_reviewed"]
        assert d["count"] == len(d["project_definitions"]), f"{ev_path}:{cid}"
        for e in d["project_definitions"]:
            assert e["sha256"] and e["name"] and e["module"]
            assert not e["module"].startswith(("Init", "Mathlib", "Std", "Lean")), (
                f"{cid}: {e['name']} is library, not this repository's")
        assert "AmpasRef.Defs" in d["limit"], (
            "the limit must say that AmpasRef.Defs is NOT excluded: the "
            "provenance layer trusts it, and a wrong Ampas.IsEven living "
            "there is the canonical fidelity failure")


def test_the_even_claim_reports_the_definition_it_actually_rests_on():
    """The concrete case the whole item exists for. `Ampas.IsEven` is in
    `AmpasRef.Defs`, which the PROVENANCE layer trusts -- and the first
    implementation reused that trusted-module list here and reported zero
    definitions for every claim, including this one."""
    ev = load("reference/checklist-evidence.json")
    names = [d["name"] for d in
             ev["claims"]["EVEN"]["items"]["definitions_reviewed"]["project_definitions"]]
    assert "Ampas.IsEven" in names, names
    assert ev["claims"]["ADD"]["items"]["definitions_reviewed"]["count"] == 0, (
        "add_comm_nat rests on no definition of this repository's; reporting "
        "one would mean the filter stopped filtering")


def test_conclusion_evidence_is_the_serialized_form_not_the_pretty_one():
    """The pretty form is for the human; the hash must be over the structural
    serialization, which is what cannot be changed by reformatting."""
    import hashlib
    for ev_path, _, cid, c in all_claims():
        k = c["items"]["conclusion_not_weakened"]
        assert k["conclusion"].strip() and k["conclusion_serialized"].strip()
        assert k["conclusion_sha256"] == hashlib.sha256(
            k["conclusion_serialized"].encode("utf-8")).hexdigest(), f"{ev_path}:{cid}"


# ---- the conventions list is a judgement, and says so

def test_the_conventions_list_states_its_own_limit():
    d = conventions()
    assert d["last_reviewed"], "an empty result means nothing without a review date"
    blob = " ".join(d["what_this_is"]) + " " + " ".join(d["not_covered"])
    assert "judgement, not a derivation" in blob
    assert "kernel_advisories" in blob, (
        "the same failure mode has a name in this repository; the list must "
        "point at it rather than restating it")


def test_every_rule_is_unique_and_says_what_to_check():
    d = conventions()
    consts = [e["const"] for e in d["conventions"]]
    assert len(consts) == len(set(consts)), "duplicate rule"
    for e in d["conventions"]:
        assert len(e["note"]) > 25, f"{e['const']}: a note that short checks nothing"


def test_the_rules_use_elaborated_names():
    """Written first against the surface syntax the list matched almost
    nothing: `b ≤ a` elaborates to `@LE.le Nat instLENat b a` and never
    mentions `Nat.le`. Both forms are listed now; these are the ones that
    actually appear in a statement."""
    consts = {e["const"] for e in conventions()["conventions"]}
    for n in ("LE.le", "LT.lt", "instLENat", "instLTNat", "HSub.hSub", "HPow.hPow"):
        assert n in consts, n


def test_the_known_traps_actually_fire_on_the_claims_that_carry_them():
    """A convention list that matches nothing is indistinguishable from a
    clean result. These are the traps each claim is known to carry."""
    want = {
        ("reference/checklist-evidence.json", "SUB"): "HSub.hSub",
        ("reference/checklist-evidence.json", "DIV"): "HDiv.hDiv",
        ("reference/checklist-evidence.json", "DVD"): "Dvd.dvd",
        ("reference/checklist-evidence.json", "GREATER"): "LT.lt",
        ("reference/checklist-evidence-mathlib.json", "PRIMES"): "Nat.Prime",
        # 2 ^ 2 ^ n + 1 is a Fermat number only because `^` associates RIGHT
        ("reference/checklist-evidence-fermat.json", "FERMAT-CLAIM"): "HPow.hPow",
    }
    for (ev_path, cid), const in want.items():
        got = [e["const"] for e in load(ev_path)["claims"][cid]
               ["items"]["no_unintended_convention"]["in_the_statement"]]
        assert const in got, f"{cid}: expected {const} among {got}"


def test_an_empty_convention_result_is_auditable():
    """`unmatched_statement_constants` is why the list is improvable: it showed
    `Nat.Prime` and `HPow.hPow` sitting unmatched under three claims, which is
    how those rules came to exist. Without it an empty
    `in_the_statement` reads as a clean result."""
    for ev_path, _, cid, c in all_claims():
        n = c["items"]["no_unintended_convention"]
        assert "unmatched_statement_constants" in n, f"{ev_path}:{cid}"
        assert "NOT that the statement has no convention trap" in n["limit"]
        assert n["conventions_list"]["last_reviewed"]
        known = {e["const"] for e in conventions()["conventions"]}
        assert not (set(n["unmatched_statement_constants"]) & known), (
            f"{cid}: a constant is reported unmatched that the list has a rule for")


def test_a_convention_reached_through_a_project_definition_is_reported_separately():
    """`Ampas.IsEven` hides its arithmetic one level down, so a convention a
    reviewer cannot see in the statement gets its own channel. Expanding
    through LEAN's definitions too made it useless -- `Nat.div` is implemented
    with truncated subtraction, so every claim mentioning `/` reported
    `HSub.hSub`, `Nat.sub` and `Nat.pred`, and `OfNat.ofNat` appeared under
    nearly every claim there is."""
    ev = load("reference/checklist-evidence.json")
    div = ev["claims"]["DIV"]["items"]["no_unintended_convention"]
    via = [e["const"] for e in div["via_this_repositorys_definitions"]]
    assert "Nat.sub" not in via and "Nat.pred" not in via, (
        f"the channel is expanding through Lean's own implementations again: {via}")
    for _, _, cid, c in all_claims():
        n = c["items"]["no_unintended_convention"]
        inside = {e["const"] for e in n["in_the_statement"]}
        assert not (inside & {e["const"] for e in n["via_this_repositorys_definitions"]}), (
            f"{cid}: a convention is reported in both channels")


# ---- what the evidence must NOT be read as

def test_the_signed_attestations_are_recorded_as_predating_the_evidence():
    """The failure this guards against is the subtlest one here: derived
    evidence sitting beside a signed checklist reads as backing for the
    judgement, and for all thirteen it had no part in it -- ROADMAP 5.4 came
    after them. The dates are beside each other, so the answer is
    recomputable rather than asserted."""
    for ev_path, att_dir in EVIDENCE.items():
        gen = load(ev_path)["generated"]
        for att in sorted((ROOT / att_dir).glob("*.json")):
            rec = json.loads(att.read_text(encoding="utf-8"))
            signed = rec["signature"]["signed_at"]
            assert signed < gen, (
                f"{rec['claim']}: signed at {signed}, evidence generated {gen}. If "
                f"an attestation is ever signed WITH the evidence in front of the "
                f"reviewer, this test must be updated deliberately -- that is a "
                f"stronger claim and the record should be able to say so.")


def test_verify_reports_which_ticks_predate_the_evidence():
    # Matched on fragments short enough to sit inside ONE string literal.
    # Whitespace-joining the file is not enough -- the `" "` seam between two
    # adjacent literals survives it -- and asserting on a long phrase is the
    # bug that broke test_provenance when a blockquote marker split
    # "not really an independent implementation".
    src = " ".join((ROOT / "harness" / "ampas_review.py")
                   .read_text(encoding="utf-8").split())
    assert "attestations_signed_before_the_evidence_existed" in src
    assert "not a record that the reviewer examined" in src
    assert "ticked" in src and "without the per-item evidence" in src


def test_the_evidence_does_not_claim_to_decide_fidelity():
    for ev_path in EVIDENCE:
        blob = " ".join(load(ev_path)["what_this_is"])
        assert "does not decide fidelity" in blob
        assert "A06_wrong_statement" in blob, (
            "the limit must cite the measurement, since a reader who finds "
            "five of six items backed will otherwise assume the sixth is too")


# ---- the auditor that produced it

def test_the_auditor_renders_inside_the_telescope():
    """The first implementation pretty-printed after the telescope closed, so
    data binders came out as `_fvar.1` and `∀ n, ∃ m, n < m` came out as
    `∃ m, m < m` -- a different and FALSE statement, offered as the evidence a
    tick is about."""
    src = (ROOT / "harness" / "Audit.lean").read_text(encoding="utf-8")
    assert "∃ m, m < m" in src, "the bug must stay named in the comment"
    assert "body.abstract xs" in src, (
        "serialization must put the de Bruijn indices back rather than "
        "serializing free variables")


def test_a_stale_compiled_auditor_is_not_preferred_over_its_source(tmp_path):
    """`audit_cmd()` preferred the binary unconditionally, so editing
    Audit.lean and re-running executed the code from before the edit with
    nothing in the output saying so.

    Staleness is decided by CONTENT. mtime was tried first and is not enough:
    a plain `cp` of an old binary resets its mtime, which happened in the same
    session it was written -- and a test that merely asserted the function
    returned *something* passed locally because this repository had a stale
    binary lying in it, while CI's clean checkout had none and the function
    raised. Both failures are the same shape: a label that does not track the
    data beside it.
    """
    import hashlib
    import ampas_review as R
    import ampas_lean as L

    for mod in (R, L):
        assert "stale" in (mod.audit_cmd.__doc__ or "").lower()
        assert "mtime" in (mod.audit_binary_is_stale.__doc__ or "")
    doc = " ".join((L.audit_fingerprint_path.__doc__ or "").split())
    assert "same staleness rule as audit_cmd()" in doc

    # The three answers, exercised on the REAL function by pointing its two
    # module globals at a temp directory. A test that reimplemented the rule
    # could not catch a bug in the rule, which is the point of having it.
    src = tmp_path / "Audit.lean"
    src.write_text("-- the source\n", encoding="utf-8", newline="\n")
    binary = tmp_path / "audit"
    record = tmp_path / "audit.source-sha256"
    want = hashlib.sha256(src.read_bytes()).hexdigest()

    for mod in (R, L):
        old_here, old_bin = mod.HERE, mod.AUDIT_BIN
        # reset: the first module through the loop leaves both files behind
        binary.unlink(missing_ok=True)
        record.unlink(missing_ok=True)
        src.write_text("-- the source\n", encoding="utf-8", newline="\n")
        try:
            mod.HERE, mod.AUDIT_BIN = tmp_path, binary
            assert mod.audit_binary_is_stale() is False, (
                f"{mod.__name__}: no binary is not staleness -- it is the "
                f"normal state, and tier 0 has none")
            binary.write_bytes(b"\x7fELF")
            assert mod.audit_binary_is_stale() is True, (
                f"{mod.__name__}: a binary with no record of its source is of "
                f"unknown provenance and must lose to the source")
            record.write_text(want + "  Audit.lean\n", encoding="utf-8", newline="\n")
            assert mod.audit_binary_is_stale() is False, f"{mod.__name__}"
            src.write_text("-- edited\n", encoding="utf-8", newline="\n")
            assert mod.audit_binary_is_stale() is True, (
                f"{mod.__name__}: an edited source must win")
            # the failure mtime could not see: same content, newer binary
            record.write_text(want + "  Audit.lean\n", encoding="utf-8", newline="\n")
            binary.touch()
            assert mod.audit_binary_is_stale() is True, (
                f"{mod.__name__}: touching the binary must not make stale code "
                f"look current -- that is exactly what mtime got wrong")
        finally:
            mod.HERE, mod.AUDIT_BIN = old_here, old_bin

    # and the live repository answers without raising in every state
    assert L.audit_binary_is_stale() == R.audit_binary_is_stale()


def test_bootstrap_records_which_source_it_compiled():
    """The record is what makes the check content-based rather than a guess,
    so the only thing that writes it must keep writing it."""
    sh = (ROOT / "scripts" / "bootstrap.sh").read_text(encoding="utf-8")
    assert "audit.source-sha256" in sh
    assert "sha256" in sh
    assert "harness/audit.source-sha256" in (
        ROOT / ".gitignore").read_text(encoding="utf-8"), (
        "the record is as platform-specific as the binary it describes")
    # and the limit must stay stated: the record is an assertion by whatever
    # wrote it, so this closes the accident and not a forging party
    import ampas_review as R
    doc = " ".join((R.audit_binary_is_stale.__doc__ or "").split())
    assert "assertion by whatever wrote it" in doc
    assert "closes is the accident" in doc


def test_the_driver_reproduces_its_own_record():
    """`check` re-derives everything and compares. Needs Lean, so it is
    skipped where there is none -- the records above are checked regardless."""
    import shutil
    if not shutil.which("lean"):
        pytest.skip("no Lean on PATH; run at tier 1")
    r = subprocess.run([sys.executable, "harness/checklist_evidence.py", "check"],
                       cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
                       timeout=1800)
    assert r.returncode == 0, r.stdout + r.stderr


def test_the_auditor_request_file_is_unique_per_call():
    """Two concurrent runs used to clobber each other: `_audit` wrote a fixed
    `.review_req.json` in the repository root and unlinked it afterwards, so a
    `checklist_evidence.py check` running beside the test suite made one of
    them read a file the other had already deleted. The symptom was a
    `KeyError` on the mode's own output key, which names nothing about the
    cause. CHANGELOG 0.3.0 records the same class of bug costing a certified
    claim."""
    src = (ROOT / "harness" / "ampas_review.py").read_text(encoding="utf-8")
    assert ".review_req.json\"" not in src, (
        "a fixed request path is a collision between any two concurrent runs")
    assert "tempfile.mkstemp" in src
    assert ".review_req-*.json" in (ROOT / ".gitignore").read_text(encoding="utf-8")
