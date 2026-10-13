"""The third check: the independent Python type checker (harness/kernel3).

Two groups of tests.

A. Offline, on fixed export files (no Lean needed): the adversarial vectors
   from the line-by-line review (harness/kernel3/REVIEW.md). These pin the
   scope of the checker — what a clean result does and does not mean — so a
   later change cannot quietly widen it:
     * a statement-mode export is refused (F-1);
     * the two forged inductive specifications that prove False are NOT
       reported clean once the provenance gate is on (F-2);
     * the control (the same recursor restricted to small elimination) is
       rejected on its type, proving the hole is in the assumed specification
       and not a general collapse.

B. Through the pipeline (needs Lean + the sandbox, like the other suites):
   the third check actually runs, confirms genuine proofs with no introduced
   assumption, and independently rejects the kernel-bypass attack.
"""
import json
import os
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
from kernel3.check import check_env, baseline_fingerprints, decl_fingerprint  # noqa: E402
from kernel3.parse import parse_export  # noqa: E402

FORGE = Path(__file__).resolve().parent / "forgeries"
BASELINE = ROOT / "reference" / "kernel_baseline.json"


def run(path: Path, baseline=None, **kw):
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(60000)
    try:
        return check_env(parse_export(str(path)), baseline=baseline, **kw)
    finally:
        sys.setrecursionlimit(old)


# ---------------------------------------------------------------- A. offline
def test_a_checker_output_clip_keeps_the_verdict_line():
    """A crash can append pages of stack trace, and the verdict is at the
    START of a checker's output -- `(kernel) declaration type mismatch ...`.
    A tail-only clip threw away the only line that said what happened, which
    is how a real lean4lean rejection came to look like a bare stack trace."""
    import ampas_lean as A

    text = "(kernel) declaration type mismatch\n" + ("stack frame\n" * 5000)
    out = A._clip(text)
    assert "(kernel) declaration type mismatch" in out
    assert len(out) < len(text)
    assert "characters omitted" in out


def test_tier_zero_does_not_need_lean():
    """Tier 0 is the tier a reviewer can run before installing anything, and
    it imports the harness. Detecting the toolchain must therefore not be
    fatal at import time: it has to fail later, where Lean is actually used,
    with a message that says what to do. A fresh clone with no Lean on PATH
    caught this."""
    import ampas_lean as A

    assert hasattr(A, "require_lean"), "no lazy Lean requirement"
    assert isinstance(A.LEAN_FOUND, bool)
    if not A.LEAN_FOUND:
        import pytest as _pytest
        with _pytest.raises(SystemExit) as e:
            A.require_lean()
        assert "INSTALL.md" in str(e.value)


def test_baseline_file_is_present_and_nonempty():
    fps = json.loads(BASELINE.read_text())
    assert isinstance(fps, list) and len(fps) > 100
    assert len(set(fps)) == len(fps), "baseline fingerprints must be distinct"


def test_baseline_covers_the_whole_trusted_environment():
    """The baseline must be every assumed declaration of the trusted core, not
    only those reachable from the reference statements. Built the narrow way it
    reported legitimate Init inductives (Subtype, Ordering, ...) as introduced
    for genuine submissions: fail-safe, but wrong, and it would have hidden a
    real introduction in the noise. 2000+ is the environment; ~200 was the
    statement closure."""
    fps = json.loads(BASELINE.read_text())
    assert len(fps) > 1500, (
        f"{len(fps)} fingerprints looks like a statement-closure baseline; "
        f"regenerate with harness/make_baseline.py")


def test_forged_large_elimination_is_not_reported_clean():
    """A Prop with two constructors plus a hand-written recursor eliminating
    into Sort u. Proof irrelevance then makes MyTrue and MyFalse
    interchangeable, and `bad : MyFalse` type-checks. The checker cannot see
    that the recursor is illegitimate, so it must not vouch for it."""
    base = set(json.loads(BASELINE.read_text()))
    out = run(FORGE / "forge_large_elim.export", baseline=base)
    # it type-checks: that is the finding, not a bug in the test
    assert out["errors"] == [], "the forgery does type-check; see REVIEW.md F-2"
    # ... but every piece of the forged specification is reported as not covered
    assert out["introduced_assumptions"], "a forged inductive spec must be reported"
    assert out["baseline_assumptions"] == 0
    for n in ("P", "P.a", "P.b", "P.rec"):
        assert n in out["introduced_assumptions"], n


def test_forged_nonpositive_inductive_is_not_reported_clean():
    """Bad.mk : (Bad -> MyFalse) -> Bad, the classic diagonal. Same verdict:
    it type-checks, and the provenance gate reports it."""
    base = set(json.loads(BASELINE.read_text()))
    out = run(FORGE / "forge_positivity.export", baseline=base)
    assert out["errors"] == []
    assert out["introduced_assumptions"]
    for n in ("Bad", "Bad.mk", "Bad.rec"):
        assert n in out["introduced_assumptions"], n


def test_control_small_elimination_is_rejected_on_its_type():
    """The same recursor restricted to Prop (small elimination, the legitimate
    restriction) is rejected. This isolates the hole: the checker enforces the
    type layer and only assumes the specification layer."""
    out = run(FORGE / "control_small_elim.export")
    assert out["errors"], "the small-elimination control must be rejected"
    assert any("Sort" in msg for _, msg in out["errors"]), out["errors"]


def test_a_forgery_is_only_clean_without_the_gate():
    """Without a baseline there is nothing to compare against, so every
    assumed declaration is reported as introduced. The gate is never silently
    satisfied by omitting it."""
    out = run(FORGE / "forge_large_elim.export", baseline=None)
    assert out["introduced_assumptions"]


def test_statement_mode_export_is_refused():
    """A --statement export carries #THMTYPE declarations: types without
    proofs. The original code counted those as checked and reported 0 errors."""
    src = (FORGE / "forge_large_elim.export").read_text()
    stmt = ROOT / "tests" / "forgeries" / ".tmp_statement_mode.export"
    stmt.write_text(src.replace("#MODE proof", "#MODE statement"))
    try:
        out = run(stmt)
        assert out["checked"] == 0
        assert out["errors"] and "statement" in out["errors"][0][1]
    finally:
        stmt.unlink(missing_ok=True)


def test_unproved_theorem_is_an_error_even_in_proof_mode():
    """Belt and braces: a #THMTYPE smuggled into a proof-mode export is
    reported, not counted as checked."""
    src = (FORGE / "forge_positivity.export").read_text().splitlines()
    out_lines, hit = [], False
    for ln in src:
        if ln.startswith("#DEF 7 ") and not hit:
            hit = True
            out_lines.append("#THMTYPE 7 1 0")   # name 7 (bad2), type 1 (MyFalse)
        else:
            out_lines.append(ln)
    assert hit
    p = ROOT / "tests" / "forgeries" / ".tmp_thmtype.export"
    p.write_text("\n".join(out_lines) + "\n")
    try:
        out = run(p)
        assert "bad2" in out["unproved_theorems"]
        assert any(n == "bad2" for n, _ in out["errors"])
    finally:
        p.unlink(missing_ok=True)


def test_resource_exhaustion_is_inconclusive_not_a_rejection():
    """Found the hard way: two concurrent runs on this 2-core machine made a
    checker hit its CPU limit, and the driver read that non-zero exit as a
    kernel rejection -- so a certified claim flipped to rejected because the
    machine was busy. A resource limit means no verdict was reached; it must
    be reported as INCONCLUSIVE, never as a statement about the proof."""
    import ampas_lean as A

    class R:
        def __init__(self, rc, out="", err=""):
            self.returncode, self.stdout, self.stderr = rc, out, err

    assert not A._exhausted(R(0))
    assert not A._exhausted(R(1)), "a real rejection must stay a rejection"
    for rc in (124, -24, -9, 137):
        assert A._exhausted(R(rc)), rc
    assert A._exhausted(R(1, "", "\nTIMEOUT"))
    # Lean's C++ kernel runs out of memory by throwing, not by being signalled.
    # This signature was missed by the first version of the classifier and was
    # found while packaging, on the largest submission in the corpus.
    bad_alloc = "terminate called after throwing an instance of 'St9bad_alloc'"
    assert A._exhausted(R(1, "", bad_alloc))
    assert "out of memory" in A._why(R(1, "", bad_alloc))
    # Thread exhaustion was the third signature in this family, found after
    # SIGXCPU and after std::bad_alloc, each having first been misreported as
    # a kernel rejection.
    threads = ("terminate called after throwing an instance of 'lean::exception'\n"
               "  what():  failed to create thread")
    assert A._exhausted(R(1, "", threads))
    assert "thread" in A._why(R(1, "", threads))

    # The compile step was the one place this check was never applied, and it
    # is where GitHub CI hit it: the largest submission failed with
    # `failed to create thread` while COMPILING, which the driver reported as
    # a plain rejection ("expected certified_all, got rejected") rather than
    # as a run that reached no verdict. The signature also arrives with a
    # different prefix on a different libc++.
    ci = ("libc++abi: terminating due to uncaught exception of type "
          "lean::exception: failed to create thread")
    assert A._exhausted(R(1, "", ci))

    # and a genuine kernel rejection must NOT be mistaken for exhaustion
    assert not A._exhausted(R(1, "", "error: unknown identifier 'foo'"))
    assert not A._exhausted(
        R(1, "", "(kernel) declaration type mismatch, 'f' has type True "
                 "but it is expected to have type False"))

    claim = {"id": "X", "theorem": "T", "policy": {}}
    v = A._verdict(claim, {"found": True, "kind": "theorem"}, True, "CONFIRMED",
                   ["lean4lean (SIGXCPU (CPU limit))"])
    assert v.inconclusive and not v.certified
    assert "INCONCLUSIVE" in v.reasons[0]
    assert not any("kernel replay did not succeed" in r for r in v.reasons), \
        "must not be reported as a kernel rejection"


def test_no_attestation_names_a_person_for_work_they_did_not_do():
    """Until round 3 every attestation carried a single `attested_by` field
    filled with the repository owner's name, asserting he had personally
    confirmed six checklist items per claim, for records the assistant had
    prepared. He had not.

    The three roles must stay separate fields, and a confirmation must say how
    it was given, so a delegated approval can never read as a personal review.
    """
    import glob
    recs = sorted(glob.glob(str(ROOT / "reference" / "attestations*" / "*.json")))
    assert recs, "no attestations found"
    for f in recs:
        d = json.loads(Path(f).read_text())
        name = Path(f).stem
        assert "attested_by" not in d.get("reviewer", {}), (
            f"{name}: the collapsed attested_by field is back")
        assert d.get("prepared_by"), f"{name}: no prepared_by"
        assert d["reviewer"].get("reviewed_by"), f"{name}: no reviewed_by"
        conf = d.get("confirmation", {})
        if conf.get("confirmed_by"):
            assert conf.get("mode") in ("personally_reviewed", "delegated"), (
                f"{name}: confirmation without a mode")
            assert conf.get("basis"), f"{name}: confirmation without a basis"
            if conf["mode"] == "delegated":
                assert "NOT personally read" in conf["basis"] or \
                       "not personally" in conf["basis"].lower(), (
                    f"{name}: a delegated confirmation must say so plainly")


def test_the_signing_key_does_not_claim_to_be_a_persons():
    """The key was generated inside the container that built the repository and
    is held by nobody, so its record must say that rather than carry an id that
    reads like a custody claim."""
    k = json.loads((ROOT / "reference" / "reviewer_key.json").read_text())
    assert "kai" not in k["key_id"].lower(), (
        "the key id names a person, implying custody that does not exist")
    assert k.get("custody", "").startswith("NONE") or \
           k.get("custody", "").startswith("UNDECLARED")
    assert "attributes NOTHING to a person" in k.get("note", "")


ADJ = ROOT / "reference" / "third_check_adjudications.json"


def test_every_adjudication_is_attributed_and_reasoned():
    """A disagreement is discounted only on a reviewer's record, never by
    default: each entry must name a reviewer, a date, a verdict, a reason and
    the finding it belongs to, and every finding must state its direction."""
    d = json.loads(ADJ.read_text())
    s = d["sign_off"]
    assert s["status"] in ("SIGNED", "PENDING_REVIEWER_CONFIRMATION"), s
    if s["status"] == "SIGNED":
        assert s["confirmed_by"] and s["confirmed_on"], s
    else:
        # the file must not imply a sign-off that was never given
        assert s["confirmed_by"] is None and s["confirmed_on"] is None, s
        assert s["prepared_by"] and s["note"], s
    assert d["declarations"], "an empty file would discount nothing, which is fine"
    findings = {f["id"]: f for f in d["findings"]}
    for row in d["declarations"]:
        assert row["verdict"] == "checker_incompleteness", row
        assert row["reason"] and row["origin"], row
        assert row["finding"] in findings, row
    for f in findings.values():
        assert "INCOMPLETE, NOT UNSOUND" in f["direction"], f["id"]
        assert f["mechanism"] and f["worked_example"] and f["evidence"], f["id"]


def test_the_adjudicated_declarations_are_library_code_not_submissions():
    """The whole adjudication rests on these being Lean core declarations that
    both Lean kernels accept, reproducible with no submission involved."""
    d = json.loads(ADJ.read_text())
    for row in d["declarations"]:
        assert row["origin"].startswith("Lean core"), row
    for f in d["findings"]:
        assert "no submission involved" in f["evidence"], f["id"]


def test_fingerprint_separates_the_recursor_rules():
    """The provenance gate is only as good as the fingerprint. A recursor
    whose rule right-hand side differs must get a different fingerprint,
    otherwise a forged rule could pass as a baseline one."""
    a = parse_export(str(FORGE / "forge_large_elim.export"))
    b = parse_export(str(FORGE / "control_small_elim.export"))
    ra = next(d for d in a.decls.values() if d.kind == "rec")
    rb = next(d for d in b.decls.values() if d.kind == "rec")
    assert decl_fingerprint(ra) != decl_fingerprint(rb)


def test_baseline_fingerprints_round_trip():
    env = parse_export(str(FORGE / "forge_positivity.export"))
    fps = baseline_fingerprints(env)
    out = run(FORGE / "forge_positivity.export", baseline=fps)
    assert out["introduced_assumptions"] == []
    assert out["baseline_assumptions"] == len(fps)


# ------------------------------------------------------- B. in the pipeline
pipeline = pytest.mark.skipif(
    not os.environ.get("AMPAS_AUDIT_BIN"),
    reason="needs Lean, the auditor and the sandbox (AMPAS_AUDIT_BIN)")

if os.environ.get("AMPAS_AUDIT_BIN"):
    import ampas_lean as A

    CAT = A.load_catalogue()
    BY_ID = {c["id"]: c for c in CAT["claims"]}

    @pytest.fixture(scope="module")
    def genuine():
        A.THIRD_CHECK = True
        claims = [BY_ID[c] for c in ("ADD", "EVEN")]
        return A.check_submission(
            ROOT / "corpus" / "Genuine.lean", "Genuine", claims,
            CAT["reference_module"], CAT["trusted_modules"]).to_json()

    @pytest.fixture(scope="module")
    def bypass():
        A.THIRD_CHECK = True
        claims = [BY_ID["ADD"]]
        return A.check_submission(
            ROOT / "corpus" / "attacks" / "A01_kernel_bypass.lean",
            "A01_kernel_bypass", claims,
            CAT["reference_module"], CAT["trusted_modules"]).to_json()


@pipeline
def test_third_check_runs_on_a_genuine_submission(genuine):
    tc = genuine["third_check"]
    assert tc["run"], tc
    assert tc["checked"] > 0 and tc["errors"] == []


@pipeline
def test_genuine_submission_introduces_no_assumption(genuine):
    """Everything the genuine proof relies on is an inductive the trusted
    reference already carries, so the clean result covers what it claims to."""
    tc = genuine["third_check"]
    assert tc["introduced_assumptions"] == [], tc["introduced_assumptions"]
    assert tc["baseline_assumptions"] > 0


@pipeline
def test_third_check_states_its_scope(genuine):
    assert "inductive specifications only where they match" in genuine["third_check"]["covers"]


@pipeline
def test_genuine_submission_is_corroborated(genuine):
    assert genuine["third_check"]["status"] == "CONFIRMED"
    for c in genuine["claims"]:
        assert c["corroboration"] == "CONFIRMED"


@pipeline
def test_third_check_independently_rejects_the_kernel_bypass(bypass):
    """A01 disables the kernel type-checker in Lean. The third check shares no
    code with Lean and rejects it on its own."""
    tc = bypass["third_check"]
    assert tc["run"] and tc["errors"], tc
    assert not any(c["certified"] for c in bypass["claims"])
