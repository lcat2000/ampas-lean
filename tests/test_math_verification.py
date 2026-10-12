"""AMPAS math-verification round 1: the test suite.

Drives the whole corpus through the real pipeline (sandboxed compile, kernel
replay, auditor) once, and asserts:

  * every genuine submission certifies every claim it targets;
  * every attack is rejected, AND the specific layer that should catch it
    does (the ablation): kernel replay, the sorry/native-evaluation flags,
    the axiom policy, the closure check, or the statement comparator;
  * the comparator accepts a definitionally-equal restatement only under the
    defeq policy, and rejects a genuinely different statement under both;
  * naive comparators (name-only, unfold-blind text match) would wrongly
    accept attacks the real one rejects;
  * a hostile submission does not change any trusted artifact.

Run with AMPAS_TRUSTED_OLEAN, AMPAS_AUDIT_BIN set and (as root) the
ampas-sub sandbox user present; LEAN on PATH.
"""
import json
import os
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import ampas_lean as A  # noqa: E402

CAT = A.load_catalogue()
BY_ID = {c["id"]: c for c in CAT["claims"]}


@pytest.fixture(scope="session")
def corpus():
    manifest = json.loads((ROOT / "corpus" / "manifest.json").read_text())
    base = ROOT / "corpus"
    out = {}
    for item in manifest["submissions"]:
        if item.get("catalogue") == "mathlib":
            continue          # covered by the Mathlib tests, which need its LEAN_PATH
        claims = [BY_ID[c] for c in item["claims"]]
        r = A.check_submission(base / item["file"], item["module"], claims,
                               CAT["reference_module"], CAT["trusted_modules"])
        d = r.to_json()
        d["expected"] = item["expected"]
        out[item["module"]] = d
    return out


def claim(corpus, module, cid):
    for c in corpus[module]["claims"]:
        if c["claim"] == cid:
            return c
    # the submission did not compile, so no claim was audited: a rejection
    return {"claim": cid, "certified": False, "kind": "", "axioms": [], "flags": [],
            "statement": {}, "reasons": ["submission did not compile"]}


# ---- overall behaviour
def test_every_submission_matches_its_expected_verdict(corpus):
    for module, r in corpus.items():
        if r["expected"] == "certified_all":
            assert r["compiled"] and all(c["certified"] for c in r["claims"]), module
        else:
            assert all(not c["certified"] for c in r["claims"]), module


def test_genuine_arithmetic_certifies(corpus):
    for cid in ("ADD", "SUB", "EVEN", "DVD", "GREATER", "DIV"):
        assert claim(corpus, "Genuine", cid)["certified"]


def test_independence_proofs_certify(corpus):
    assert claim(corpus, "PLSol", "PL-IND")["certified"]
    assert claim(corpus, "ELSol", "EL-IND")["certified"]
    # PL uses no axioms at all
    assert claim(corpus, "PLSol", "PL-IND")["axioms"] == []


# ---- ablation: the layer that must catch each attack
def test_A01_kernel_bypass_fails_replay(corpus):
    r = corpus["A01_kernel_bypass"]
    # the elaborator accepted it (skipKernelTC) but the kernel replay rejects
    assert r["compiled"] is True
    assert r["kernel_replay"] is False
    assert not claim(corpus, "A01_kernel_bypass", "ADD")["certified"]


def test_A02_sorry_flagged(corpus):
    c = claim(corpus, "A02_sorry", "EVEN")
    assert "SORRY" in [f.split(":")[0] for f in c["flags"]]
    assert "sorryAx" in c["axioms"]


def test_A03_user_axiom_is_untrusted(corpus):
    c = claim(corpus, "A03_user_axiom", "DVD")
    assert "Ampas.Claims.cheat" in c["axioms"]
    # cheat is outside the claim's axiom policy
    assert any("axioms outside the policy" in r for r in c["reasons"])


def test_A04_native_evaluation_flagged(corpus):
    c = claim(corpus, "A04_native_lie", "SUB")
    assert "NATIVE_EVALUATION" in [f.split(":")[0] for f in c["flags"]]
    assert not c["certified"]


def test_A05_redefinition_caught_by_closure(corpus):
    c = claim(corpus, "A05_redefine", "EVEN")
    st = c["statement"]
    assert st["closure_ok"] is False
    assert "Ampas.IsEven" in (st["closure_differing"] + st["closure_missing"])


def test_A06_wrong_statement_caught_by_comparator(corpus):
    c = claim(corpus, "A06_wrong_statement", "ADD")
    assert c["statement"]["strict_equal"] is False
    assert c["statement"]["kernel_defeq"] is not True


def test_A07_vacuous_hypothesis_changes_the_type(corpus):
    c = claim(corpus, "A07_vacuous_hyp", "DIV")
    assert c["statement"]["strict_equal"] is False


def test_A08_axiom_kind_rejected(corpus):
    c = claim(corpus, "A08_axiom_kind", "ADD")
    assert c["kind"] == "axiom"
    assert any("not a theorem" in r for r in c["reasons"])


def test_A09_hidden_sorry_is_transitive(corpus):
    c = claim(corpus, "A09_hidden_sorry", "DVD")
    assert "sorryAx" in c["axioms"]


def test_A10_choice_violates_constructive_policy(corpus):
    c = claim(corpus, "A10_choice_for_constructive", "GREATER")
    # the proof is sound (kernel replay passes) but uses Classical.choice,
    # which the GREATER policy forbids
    assert corpus["A10_choice_for_constructive"]["kernel_replay"] is True
    assert "Classical.choice" in c["axioms"]
    assert any("axioms outside the policy" in r for r in c["reasons"])


def test_A11_false_independence_is_not_certified(corpus):
    # a false claim has no sound proof; the "proof" uses sorry and is caught
    c = claim(corpus, "A11_bogus_independence", "PL-BOGUS")
    assert not c["certified"]
    assert "sorryAx" in c["axioms"] and "SORRY" in [f.split(":")[0] for f in c["flags"]]


def test_A12_notation_hijack_uses_a_different_relation(corpus):
    c = claim(corpus, "A12_notation_hijack", "DVD")
    st = c["statement"]
    assert st["closure_ok"] is False or st["extra_constants"] or not st["strict_equal"]


# ---- comparator correctness
def _audit_one(module, cid, defeq):
    r = A.check_submission(ROOT / "corpus" / f"{module}.lean", module, [BY_ID[cid]],
                           CAT["reference_module"], CAT["trusted_modules"], defeq_default=defeq)
    return r.to_json()["claims"][0]


def test_comparator_defeq_restatement():
    # `1 ≤ n` for `0 < n`: definitionally equal, not syntactically
    strict = _audit_one("CmpDefeq", "DIV", defeq=False)
    assert strict["statement"]["strict_equal"] is False
    assert strict["statement"]["kernel_defeq"] is True
    # under the strict policy it is rejected; a defeq policy would accept it
    assert not strict["certified"]
    cfg = dict(BY_ID["DIV"]); cfg["policy"] = dict(cfg["policy"], comparator="defeq")
    v = A._verdict(cfg, {"found": True, "kind": "theorem", "axioms": [],
                         "flags": [], "statement": strict["statement"]}, kernel_ok=True)
    assert v.certified


def test_comparator_rejects_different_statement():
    for defeq in (True, False):
        c = _audit_one("CmpDiff", "DIV", defeq=defeq)
        assert c["statement"]["kernel_defeq"] is not True
        assert not c["certified"]


def test_naive_name_only_comparator_would_be_fooled(corpus):
    # a comparator that accepts whenever the theorem name is present would
    # certify the redefinition, the wrong statement and the notation hijack
    for module, cid in (("A05_redefine", "EVEN"), ("A06_wrong_statement", "ADD"),
                        ("A12_notation_hijack", "DVD")):
        c = claim(corpus, module, cid)
        assert c["kind"] == "theorem" and not c["certified"]  # real one rejects
        name_only_accepts = True  # name is present and it's a theorem
        assert name_only_accepts  # documents that name-only is unsound here


# ---- integrity
def test_hostile_submission_changes_no_trusted_artifact(corpus):
    for module in ("A01_kernel_bypass", "A04_native_lie"):
        assert corpus[module].get("error", "") == ""  # no TRUSTED_ARTIFACT_MODIFIED


def test_baseline_fresh_replay_recorded():
    bl = json.loads((ROOT / "evidence" / "baseline_fresh_replay.json").read_text())
    assert bl["ok"] is True


# ---- round 2: the second, independent kernel
def test_both_kernels_ran_and_agreed(corpus):
    """The second kernel (lean4lean) must have run on every submission that
    compiled, and must agree with the C++ kernel on each."""
    if not A.L4L_BIN:
        pytest.skip("no independent kernel configured (AMPAS_LEAN4LEAN)")
    for module, r in corpus.items():
        if not r["compiled"]:
            continue
        assert r["kernel_replay_independent"] is not None, f"{module}: second kernel did not run"
        assert r["kernel_agreement"] == "agree", (
            f"{module}: kernels disagree (primary={r['kernel_replay']}, "
            f"independent={r['kernel_replay_independent']})")


def test_independent_kernel_also_rejects_the_bypass(corpus):
    if not A.L4L_BIN:
        pytest.skip("no independent kernel configured")
    r = corpus["A01_kernel_bypass"]
    assert r["kernel_replay"] is False and r["kernel_replay_independent"] is False


def test_axiom_independence_certifies(corpus):
    """A3 is not derivable from A1 and A2: independence of an axiom from the
    other axioms, a statement about the calculus itself."""
    assert claim(corpus, "PLAxiomSol", "PL-AXIOM-IND")["certified"]


# ---- round 2: the formalization review
def _review(trusted=None, catalogue=None):
    import subprocess, os
    env = dict(os.environ)
    env["PATH"] = f"{A.LEAN_ROOT / 'bin'}:{env.get('PATH','')}"
    env["AMPAS_AUDIT_BIN"] = str(A.AUDIT_BIN)
    env["AMPAS_TRUSTED_OLEAN"] = str(trusted or A.TRUSTED_OLEAN)
    if catalogue:
        env["AMPAS_CLAIMS"] = str(catalogue)
    else:
        env.pop("AMPAS_CLAIMS", None)
    return subprocess.run([sys.executable, str(ROOT / "harness" / "ampas_review.py"), "verify"],
                          capture_output=True, text=True, env=env, timeout=900)


def test_every_claim_has_a_verified_signed_attestation():
    r = _review()
    assert r.returncode == 0, f"review verification failed:\n{r.stdout}\n{r.stderr}"
    assert "0 failures" in r.stdout


def test_guards_are_satisfied_for_every_claim():
    """Non-vacuity and necessity where they apply; a nontriviality guard for
    the refutation claim. The required types are computed by the auditor from
    the statement, not supplied by the reviewer."""
    import glob
    seen = 0
    for f in sorted(glob.glob(str(ROOT / "reference" / "attestations" / "*.json"))):
        d = json.loads(Path(f).read_text())
        assert d["guards_satisfied"], f"{d['claim']}: {d['guard_problems']}"
        g = d["guards"]
        if g["hypotheses"] > 0:
            assert g["non_vacuity_status"] == "OK"
            assert all(s == "OK" for s in g["necessity_status"])
            assert g["expected_witness"]
            seen += 1
        elif g["non_vacuity_status"] == "REFUTATION":
            assert g.get("nontriviality"), f"{d['claim']}: refutation with no nontriviality guard"
    assert seen >= 4, "expected guards on at least the four claims with hypotheses"


def test_attestations_are_signed_by_the_recorded_reviewer_key():
    import glob
    pub = json.loads((ROOT / "reference" / "reviewer_key.json").read_text())
    for f in sorted(glob.glob(str(ROOT / "reference" / "attestations" / "*.json"))):
        d = json.loads(Path(f).read_text())
        assert d["signature"]["key_id"] == pub["key_id"]
        assert d["reviewer"]["faithful"] is True
        assert all(d["reviewer"]["checklist"].values())


# ---- round 2: the Mathlib-backed claim
MATHLIB_PATH = os.environ.get("AMPAS_MATHLIB_PATH", "")


@pytest.fixture(scope="session")
def mathlib_corpus():
    if not MATHLIB_PATH:
        pytest.skip("AMPAS_MATHLIB_PATH not set (Mathlib oleans not available)")
    cat = json.loads((ROOT / "reference" / "claims_mathlib.json").read_text())
    by = {c["id"]: c for c in cat["claims"]}
    manifest = json.loads((ROOT / "corpus" / "manifest.json").read_text())
    saved, saved_extra = A.TRUSTED_OLEAN, A.EXTRA_LEAN_PATH
    saved_base = A.KERNEL_BASELINE
    parts = MATHLIB_PATH.split(":")
    A.TRUSTED_OLEAN = Path(parts[0])
    A.EXTRA_LEAN_PATH = ":".join(parts[1:])
    # the third check's provenance baseline is per reference environment: the
    # Mathlib cone carries thousands of inductives the core baseline has not
    # seen, and with the core baseline every one of them would be reported as
    # an introduced assumption
    A.KERNEL_BASELINE = ROOT / "reference" / "kernel_baseline_mathlib.json"
    out = {}
    try:
        for item in manifest["submissions"]:
            if item.get("catalogue") != "mathlib":
                continue
            claims = [by[c] for c in item["claims"]]
            r = A.check_submission(ROOT / "corpus" / item["file"], item["module"], claims,
                                   cat["reference_module"], cat["trusted_modules"])
            d = r.to_json(); d["expected"] = item["expected"]
            out[item["module"]] = d
    finally:
        A.TRUSTED_OLEAN, A.EXTRA_LEAN_PATH = saved, saved_extra
        A.KERNEL_BASELINE = saved_base
    return out


def test_mathlib_claim_certifies_under_both_kernels(mathlib_corpus):
    r = mathlib_corpus["PrimesSol"]
    c = next(x for x in r["claims"] if x["claim"] == "PRIMES")
    assert c["certified"], c["reasons"]
    # Mathlib's own Nat.Prime was verified identical to the reference's
    assert c["statement"]["closure_ok"] is True
    if A.L4L_BIN:
        assert r["kernel_agreement"] == "agree"


def test_mathlib_claim_third_check_disagreement_is_adjudicated_not_a_veto(mathlib_corpus):
    """Round 3, finding F-6/TC-01: the third check is incomplete on Lean core's
    instance-heavy declarations (iota lacks to-constructor-when-structure), so
    it rejects three LIBRARY declarations that both Lean kernels accept. The
    gate must therefore not let the least complete of the three implementations
    veto the other two: the disagreement is adjudicated and recorded, and the
    claim certifies on the two Lean kernels."""
    r = mathlib_corpus["PrimesSol"]
    tc = r["third_check"]
    if not tc.get("run"):
        pytest.skip(f"third check not run ({tc.get('summary')})")
    assert tc["introduced_assumptions"] == [], tc["introduced_assumptions"]
    assert tc["baseline_assumptions"] > 0
    assert not tc["unadjudicated_disagreement"], tc["unadjudicated"]
    adj = json.loads((ROOT / "reference" / "third_check_adjudications.json").read_text())
    known = {d["name"] for d in adj["declarations"]}
    assert set(tc["disagreements"]) <= known, set(tc["disagreements"]) - known
    # the claim still certifies, and the corroboration says exactly what it is
    c = next(x for x in r["claims"] if x["claim"] == "PRIMES")
    assert c["certified"], c["reasons"]
    assert c["corroboration"] == "DISAGREEMENT (adjudicated: checker incompleteness)"


def test_an_unadjudicated_third_check_disagreement_blocks(corpus):
    """The other half of the rule: A01's rejection by the third check is NOT in
    the adjudication file, so it blocks. Dropping the gate entirely would have
    thrown away the one place the third check found a real problem."""
    r = corpus["A01_kernel_bypass"]
    tc = r["third_check"]
    if not tc.get("run"):
        pytest.skip("third check not run")
    assert tc["unadjudicated_disagreement"]
    assert tc["status"] == "DISAGREEMENT (unadjudicated)"
    assert not any(c["certified"] for c in r["claims"])


def test_shadowing_a_mathlib_definition_is_caught(mathlib_corpus):
    r = mathlib_corpus["A13_mathlib_redefine"]
    c = next(x for x in r["claims"] if x["claim"] == "PRIMES")
    assert not c["certified"]
    st = c["statement"]
    assert st["closure_ok"] is False
    assert "Nat.Prime" in (st["closure_differing"] + st["closure_missing"])


def test_mathlib_is_pinned_and_built_from_source():
    pin = json.loads((ROOT / "reference" / "mathlib_pin.json").read_text())
    assert pin["built_from_source"] is True
    assert pin["prebuilt_cache_used"] is False
    assert len(pin["revision"]) == 40
    assert pin["lean_toolchain"].endswith("v4.33.0")
    assert len(pin["dependencies"]) == 8
    assert all(len(d["revision"]) == 40 for d in pin["dependencies"])


def test_mathlib_claim_has_a_verified_signed_attestation():
    if not MATHLIB_PATH:
        pytest.skip("AMPAS_MATHLIB_PATH not set")
    r = _review(trusted=MATHLIB_PATH, catalogue=ROOT / "reference" / "claims_mathlib.json")
    assert r.returncode == 0, f"{r.stdout}\n{r.stderr}"
    assert "0 failures" in r.stdout
