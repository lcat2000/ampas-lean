"""Strict positivity (harness/kernel3/positivity.py) and its differential test.

ROADMAP 2. The third check assumes every inductive declaration is a
legitimate specification, and `tests/forgeries/forge_positivity.export` proves
`False` through that hole. This pass closes the positivity part of it.

The pass WIDENS what could be accepted, so these tests are written against
the failure direction that matters:

  A. the forgery is rejected on its SPECIFICATION, and the two vectors
     positivity has nothing to say about are not rejected by it -- a pass that
     rejected everything would also "catch" the forgery and would be useless;
  B. UNCLASSIFIED is never a pass. Several tests here exist only to fail if a
     later change folds it into `ok`, including a source-level one, because
     the quiet version of that mistake is a caller writing
     `if not r["violations"]`;
  C. the committed differential record (`evidence/positivity_differential.json`)
     is internally consistent and reports no violation over the declaration
     sets Lean itself accepted. A violation there is a bug in the pass.

What these tests do NOT claim: that a specification coming back OK is a
checked specification. Positivity is one of three properties kernel3 assumes
(recursor shape and iota rules are the other two), so `test_positivity_does_
not_relax_the_provenance_gate` pins that the forgery is still not clean.
"""
import json
import re
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
from kernel3.parse import parse_export                       # noqa: E402
from kernel3.positivity import (check_env, check_constructor,  # noqa: E402
                                occurs, _telescope)
from kernel3.check import check_env as third_check            # noqa: E402
from kernel3.check import baseline_fingerprints              # noqa: E402

FORGE = ROOT / "tests" / "forgeries"
DIFF = ROOT / "evidence" / "positivity_differential.json"


def classify(name: str) -> dict:
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(60000)
    try:
        return check_env(parse_export(str(FORGE / name)))
    finally:
        sys.setrecursionlimit(old)


def nm(env, name: str):
    """The export's keys are `Name` objects, and `occurs` compares names by
    equality -- so a test must pass the real `Name`, not a string. A string
    set would silently match nothing, which is the same failure direction the
    pass itself guards against."""
    for n in env.order:
        if str(n) == name:
            return n
    raise AssertionError(f"{name} not in export")


def decl(env, name: str):
    return env.get(nm(env, name))


def verdict_of(r: dict, decl: str) -> str:
    if decl in r["ok"]:
        return "OK"
    for n, _ in r["violations"]:
        if n == decl:
            return "VIOLATION"
    for n, _ in r["unclassified"]:
        if n == decl:
            return "UNCLASSIFIED"
    return "ABSENT"


# ------------------------------------------------- A. the adversarial vectors
def test_forged_positivity_is_rejected_on_its_specification():
    """The ROADMAP 'done when': the forgery is caught by the rule it breaks,
    not merely contained by the provenance gate. `Bad.mk : (Bad -> MyFalse)
    -> Bad` puts the recursive occurrence left of an arrow, which is what
    lets a diagonal argument derive False."""
    r = classify("forge_positivity.export")
    assert verdict_of(r, "Bad") == "VIOLATION"
    why = next(w for n, w in r["violations"] if n == "Bad")
    assert "LEFT" in why and "binder 0" in why


def test_the_benign_inductive_in_the_same_export_still_passes():
    """A pass that rejected every inductive would also 'catch' the forgery.
    `MyFalse` sits in the same export and is a legitimate specification."""
    r = classify("forge_positivity.export")
    assert verdict_of(r, "MyFalse") == "OK"
    assert len(r["violations"]) == 1, r["violations"]


@pytest.mark.parametrize("vector", ["forge_large_elim.export",
                                    "control_small_elim.export"])
def test_recursor_forgeries_are_outside_this_pass(vector):
    """`forge_large_elim` forges a RECURSOR, not an inductive specification.
    Positivity has nothing to say about it, so it must come back clean here
    and must still be caught by the provenance gate. Recording that honestly
    is the point: a pass that claimed this one too would be claiming to check
    the recursor's shape, which nothing in this repository does."""
    r = classify(vector)
    assert r["violations"] == []
    assert r["checked"] >= 3


def test_positivity_does_not_relax_the_provenance_gate():
    """The forgery passing or failing THIS pass changes nothing about the
    third check's verdict: its specification is still not in the baseline, so
    it is still an introduced assumption. If this test ever fails, a positivity
    OK has been wired into the gate, which is the unsoundness this module's
    docstring forbids."""
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(60000)
    try:
        env = parse_export(str(FORGE / "forge_positivity.export"))
        base = baseline_fingerprints(parse_export(str(FORGE / "control_small_elim.export")))
        out = third_check(env, baseline=base)
    finally:
        sys.setrecursionlimit(old)
    assert out["introduced_assumptions"], (
        "the forged specification is no longer reported as introduced")


# ------------------------------------------- B. UNCLASSIFIED is not a pass
def test_unclassified_and_ok_are_disjoint():
    for vector in ("forge_positivity.export", "forge_large_elim.export",
                   "control_small_elim.export"):
        r = classify(vector)
        names = {n for n, _ in r["unclassified"]} | {n for n, _ in r["violations"]}
        assert not (names & set(r["ok"])), vector
        assert r["checked"] == len(r["ok"]) + len(r["violations"]) + len(r["unclassified"])


def test_nested_inductive_shape_is_unclassified_not_ok():
    """`Lean.Syntax.node` holds `Array Syntax`: a recursive occurrence under
    another inductive's parameter. Lean accepts it; this pass cannot decide it
    without computing Array's own positivity, so it must decline. Reporting it
    OK would be the pass asserting something it did not check."""
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    unclassified = {n: w for s in d["sets"] for n, w in s["unclassified"]}
    assert "Lean.Syntax" in unclassified
    assert "nested" in unclassified["Lean.Syntax"]
    oks = {s["environment"]: s["ok"] for s in d["sets"]}
    assert all(v > 0 for v in oks.values())


def test_verdict_comes_from_an_occurrence_not_from_the_shape():
    """`Bad.mk` has a function argument, and plenty of legitimate constructors
    do. What makes it a violation is that the FAMILY occurs in that argument's
    domain. Read against a family it does not mention, the same type is not a
    positivity question and must come back OK -- otherwise the pass is
    rejecting arrows, not non-strict positivity."""
    env = parse_export(str(FORGE / "forge_positivity.export"))
    bad = decl(env, "Bad.mk")
    assert bad is not None
    fam = nm(env, "Bad")
    verdict, _ = check_constructor(bad.type, 0, {fam}, fam)
    assert verdict == "VIOLATION"
    # the same type, read against a family it does not mention, is not a
    # positivity question at all: there is nothing to check, so OK. This pins
    # that the verdict comes from an occurrence and not from the shape alone.
    absent = nm(env, "out")   # in the export, but absent from Bad.mk's type
    verdict2, why2 = check_constructor(bad.type, 0, {absent}, fam)
    assert verdict2 == "OK", why2


def test_no_caller_treats_unclassified_as_a_pass():
    """Source-level, because the quiet version of this mistake is a caller
    writing `if not r["violations"]` and calling the rest accepted. Every
    reader of check_env() must look at `unclassified` too."""
    offenders = []
    for path in sorted((ROOT / "harness").rglob("*.py")):
        if path.name == "positivity.py":
            continue
        text = path.read_text(encoding="utf-8")
        if "check_env" not in text or "positivity" not in text:
            continue
        if "violations" in text and "unclassified" not in text:
            offenders.append(str(path.relative_to(ROOT)))
    assert not offenders, (
        f"these read positivity violations without reading unclassified: {offenders}")


def test_module_docstring_states_what_it_does_not_check():
    """The two unchecked properties must stay named in the module itself. A
    reader who finds this pass and not that paragraph will take OK for a
    checked specification."""
    import kernel3.positivity as P
    doc = P.__doc__ or ""
    assert "recursor" in doc and "iota" in doc
    assert "UNCLASSIFIED" in doc


# ------------------------------------------------ C. the differential record
def test_differential_record_is_consistent():
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    assert d["schema"] == "ampas-positivity-differential/1"
    t = d["totals"]
    assert t["checked"] == sum(s["checked"] for s in d["sets"])
    assert t["ok"] == sum(s["ok"] for s in d["sets"])
    assert t["unclassified"] == sum(len(s["unclassified"]) for s in d["sets"])
    for s in d["sets"]:
        assert s["checked"] == (
            s["ok"] + len(s["violations"]) + len(s["unclassified"])), s["environment"]
        assert sum(s["unclassified_by_cause"].values()) == len(s["unclassified"])


def test_differential_record_reports_no_violation():
    """Over declaration sets Lean's own kernel accepted, a violation would be
    a bug in the pass -- Lean accepted the declaration. harness/spec_diff.py
    exits non-zero on one; this pins the committed result."""
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    assert d["totals"]["violations"] == 0
    for s in d["sets"]:
        assert s["violations"] == [], s["environment"]


def test_differential_record_covers_both_environments():
    """One environment is not a differential test. The core reference set and
    the Mathlib set have different inductive shapes -- Mathlib is where the
    nested ones live."""
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    envs = {s["environment"] for s in d["sets"]}
    assert "AmpasRef.Guards" in envs
    assert any("Mathlib" in e for e in envs), envs
    assert d["totals"]["checked"] > 1000


def test_differential_record_does_not_claim_the_specification_is_checked():
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    means = " ".join(d["means"])
    assert "recursor" in means and "iota" in means
    assert "provenance gate" in means
    assert not re.search(r"specification[s]? (are|is) checked", means)


def test_unclassified_count_is_recorded_not_hidden():
    """Growth in UNCLASSIFIED is how this pass silently stops covering things.
    It has to be in the record, with reasons, not just a count."""
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    assert d["totals"]["unclassified"] > 0, (
        "zero unclassified over Mathlib would mean the nested cases are being "
        "decided, which this pass does not do")
    for s in d["sets"]:
        for name, why in s["unclassified"]:
            assert name and why.strip()


# ----------------------------------------------------------- the primitives
def test_occurs_walks_every_subterm():
    env = parse_export(str(FORGE / "forge_positivity.export"))
    bad = decl(env, "Bad.mk")
    assert occurs(bad.type, {nm(env, "Bad")})
    assert occurs(bad.type, {nm(env, "MyFalse")})
    assert not occurs(bad.type, {nm(env, "out")})


def test_telescope_splits_arrows():
    env = parse_export(str(FORGE / "forge_positivity.export"))
    bad = decl(env, "Bad.mk")
    doms, concl = _telescope(bad.type)
    assert len(doms) == 1
    assert occurs(concl, {nm(env, "Bad")})
    # and the recursive occurrence is in the domain, which is the violation
    assert occurs(doms[0], {nm(env, "Bad")})


def test_node_kinds_are_imported_not_restated():
    """If PI/APP/CONST were copied as literals here and terms.py reordered,
    this pass would inspect nothing and report every specification clean --
    the one failure direction that matters."""
    src = (ROOT / "harness" / "kernel3" / "positivity.py").read_text(encoding="utf-8")
    assert "from .terms import PI, APP, CONST" in src
    assert not re.search(r"^\s*(PI|APP|CONST)\s*=\s*\d", src, re.M)
