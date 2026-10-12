"""The formalization-correctness review: freeze, sign-off and drift.

Lean cannot decide whether the reference statement renders the claim's
natural-language text. These tests check the machinery that makes that human
judgement explicit and tamper-evident: a claim is certifiable only while its
reference statement still hashes to the value a reviewer signed, for the text
and policy they signed.
"""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import review as R                                        # noqa: E402
import ampas_lean as A                                    # noqa: E402


def _build_reference(ref_dir: Path, build: Path):
    build.mkdir(parents=True, exist_ok=True)
    (build / "AmpasRef").mkdir(exist_ok=True)
    env = {"PATH": f"{A.LEAN_BIN}:/usr/bin:/bin", "LEAN_PATH": str(build),
           "HOME": str(build.parent), "LEAN_NUM_THREADS": "2"}
    for mod in ("Defs", "Challenge"):
        r = subprocess.run([str(A.LEAN_BIN / "lean"), "-o",
                            str(build / "AmpasRef" / f"{mod}.olean"),
                            str(ref_dir / "AmpasRef" / f"{mod}.lean")],
                           cwd=build.parent, env=env, capture_output=True, text=True)
        assert r.returncode == 0, r.stdout + r.stderr


@pytest.fixture
def sandbox(tmp_path, monkeypatch):
    """A private copy of the reference, with review.py pointed at it."""
    shutil.copytree(ROOT / "reference", tmp_path / "reference")
    build = tmp_path / "build"
    _build_reference(tmp_path / "reference", build)
    monkeypatch.setattr(R, "CLAIMS_PATH", tmp_path / "reference" / "claims.json")
    monkeypatch.setattr(R, "FREEZE_PATH", tmp_path / "reference" / "freeze.json")
    return tmp_path, build


def _edit_claims(path: Path, fn):
    d = json.loads(path.read_text())
    fn(d)
    path.write_text(json.dumps(d, indent=2, ensure_ascii=False))


def test_the_shipped_freeze_verifies_against_the_shipped_reference():
    """The record in the package must match the reference in the package."""
    res = R.verify(Path(os.environ.get("AMPAS_TRUSTED_OLEAN", ROOT / "build")))
    bad = {k: v for k, v in res.items() if not v["ok"]}
    assert not bad, bad
    assert len(res) >= 9


def test_freeze_then_verify_is_clean(sandbox):
    tmp, build = sandbox
    doc = R.freeze(build)
    (tmp / "reference" / "freeze.json").write_text(json.dumps(doc, indent=2))
    res = R.verify(build)
    assert all(v["status"] == "FROZEN_OK" for v in res.values())


def test_weakening_a_definition_drifts_only_the_claims_that_rest_on_it(sandbox):
    tmp, build = sandbox
    (tmp / "reference" / "freeze.json").write_text(json.dumps(R.freeze(build), indent=2))
    defs = tmp / "reference" / "AmpasRef" / "Defs.lean"
    defs.write_text(defs.read_text().replace(
        "def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k",
        "def IsEven (_n : Nat) : Prop := True"))
    _build_reference(tmp / "reference", build)
    res = R.verify(build)
    assert res["EVEN"]["status"] == "DRIFT"
    # the hash is by meaning, so unrelated claims are untouched
    for cid in ("ADD", "SUB", "DVD", "GREATER", "DIV", "PL-IND", "EL-IND"):
        assert res[cid]["status"] == "FROZEN_OK", (cid, res[cid])


def test_editing_the_text_or_the_policy_after_signoff_is_stale(sandbox):
    tmp, build = sandbox
    claims = tmp / "reference" / "claims.json"
    (tmp / "reference" / "freeze.json").write_text(json.dumps(R.freeze(build), indent=2))

    def drop_hypothesis_from_text(d):
        for c in d["claims"]:
            if c["id"] == "SUB":
                c["text"] = "For all natural numbers a and b, (a - b) + b = a."
    _edit_claims(claims, drop_hypothesis_from_text)
    res = R.verify(build)
    assert res["SUB"]["status"] == "SIGNOFF_STALE"
    assert res["ADD"]["status"] == "FROZEN_OK"

    # widening the axiom policy is equally a change to what was signed
    shutil.copy(ROOT / "reference" / "claims.json", claims)
    def widen_policy(d):
        for c in d["claims"]:
            if c["id"] == "GREATER":
                c["policy"]["axioms"] = ["propext", "Classical.choice", "Quot.sound"]
    _edit_claims(claims, widen_policy)
    assert R.verify(build)["GREATER"]["status"] == "SIGNOFF_STALE"


def test_an_unsigned_claim_is_not_ok(sandbox):
    tmp, build = sandbox
    doc = R.freeze(build)
    doc["claims"].pop("DIV")
    (tmp / "reference" / "freeze.json").write_text(json.dumps(doc, indent=2))
    assert R.verify(build)["DIV"]["status"] == "UNSIGNED"


def test_hmac_binds_the_signoff_to_a_key(sandbox, monkeypatch):
    tmp, build = sandbox
    monkeypatch.setenv("AMPAS_REVIEW_KEY", "reviewer-key-A")
    doc = R.freeze(build)
    (tmp / "reference" / "freeze.json").write_text(json.dumps(doc, indent=2))
    assert all(v["ok"] for v in R.verify(build).values())
    monkeypatch.setenv("AMPAS_REVIEW_KEY", "reviewer-key-B")
    res = R.verify(build)
    assert all(v["status"] == "HMAC_BAD" for v in res.values())
