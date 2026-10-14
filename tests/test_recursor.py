"""Recursor shape (harness/kernel3/recursor.py) and its differential test.

ROADMAP 2b, the second of the third check's three assumed properties.
`tests/forgeries/forge_large_elim.export` is the live vector: a `Prop` with two
constructors given a hand-written recursor eliminating into `Sort u`, which
proves `False` through proof irrelevance. Its control is the same recursor
restricted to `Prop`, and the two exports differ in one token.

The tests are written against the failure direction that matters, as for
positivity:

  A. the forgery is rejected on its RECURSOR, the control is not, and
     `forge_positivity` — whose recursor is legitimate — passes. A pass that
     rejected all three would also "catch" the forgery and would be useless.
     Each forgery passing the other's pass is the point: they forge different
     properties.
  B. UNCLASSIFIED is never a pass, and the reasons are tagged at the source
     rather than matched as substrings by callers.
  C. the committed differential record (`evidence/recursor_differential.json`)
     is internally consistent and reports no violation over the declaration
     sets Lean itself generated these recursors for. A violation there is a bug
     in the pass — and one was: the first version of the rules check assumed a
     mutual family's recursor carries iota rules for the whole family, and 19
     Mathlib recursors said otherwise.

What these tests do NOT claim: that the iota rules are right. The pass counts
them and checks which constructor each belongs to, not what it computes.
"""
import json
import re
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
from kernel3.parse import parse_export                          # noqa: E402
from kernel3.recursor import (check_env, check_recursor,         # noqa: E402
                              subsingleton, is_prop_valued,
                              FIELD_TYPE_NOT_IN_EXPORT)
from kernel3.check import check_env as third_check               # noqa: E402
from kernel3.check import baseline_fingerprints                  # noqa: E402

FORGE = ROOT / "tests" / "forgeries"
DIFF = ROOT / "evidence" / "recursor_differential.json"


def load(name: str):
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(60000)
    try:
        return parse_export(str(FORGE / name))
    finally:
        sys.setrecursionlimit(old)


def classify(name: str) -> dict:
    return check_env(load(name))


def nm(env, name: str):
    for n in env.order:
        if str(n) == name:
            return n
    raise AssertionError(f"{name} not in export")


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
def test_large_elimination_forgery_is_rejected_on_its_recursor():
    """The ROADMAP 2b 'done when': caught by the rule it breaks, not merely
    contained by the provenance gate. `P` is a Prop with two constructors, so
    a recursor into `Sort u` would read which constructor was used — and proof
    irrelevance makes the two indistinguishable."""
    r = classify("forge_large_elim.export")
    assert verdict_of(r, "P.rec") == "VIOLATION"
    why = next(w for n, w in r["violations"] if n == "P.rec")
    assert "2 constructors" in why
    assert "proof irrelevance" in why


def test_the_control_is_not_rejected():
    """The control is the same recursor restricted to `Prop`. If this fails,
    the pass is rejecting the shape rather than the elimination universe, and
    the forgery's rejection proves nothing."""
    r = classify("control_small_elim.export")
    assert verdict_of(r, "P.rec") == "OK"
    assert r["violations"] == []


def test_the_positivity_forgerys_recursor_is_legitimate():
    """`forge_positivity` forges the INDUCTIVE. Its recursor is the one Lean
    would generate, so this pass must pass it — and positivity must catch it.
    Each forgery being caught by exactly one pass is what shows the two
    properties are separate."""
    r = classify("forge_positivity.export")
    assert r["violations"] == []
    assert verdict_of(r, "Bad.rec") == "OK"


def test_the_two_passes_catch_different_forgeries():
    """Together: neither pass subsumes the other, and neither is a blunt
    rejector. This is the test that fails if someone 'simplifies' one pass
    into rejecting whatever the other rejects."""
    from kernel3.positivity import check_env as pos_check
    pos_large = pos_check(load("forge_large_elim.export"))
    rec_pos = check_env(load("forge_positivity.export"))
    pos_pos = pos_check(load("forge_positivity.export"))
    rec_large = check_env(load("forge_large_elim.export"))

    assert pos_pos["violations"], "positivity must catch the positivity forgery"
    assert rec_large["violations"], "the recursor pass must catch the recursor forgery"
    assert pos_large["violations"] == [], "positivity must NOT claim the recursor forgery"
    assert rec_pos["violations"] == [], "the recursor pass must NOT claim the positivity forgery"


def test_recursor_pass_does_not_relax_the_provenance_gate():
    """The forgery passing or failing this pass changes nothing about the
    third check's verdict: its recursor is not in the baseline, so it is still
    an introduced assumption. If this fails, a shape OK has been wired into
    the gate."""
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(60000)
    try:
        env = load("forge_large_elim.export")
        base = baseline_fingerprints(load("forge_positivity.export"))
        out = third_check(env, baseline=base)
    finally:
        sys.setrecursionlimit(old)
    assert out["introduced_assumptions"], (
        "the forged recursor is no longer reported as introduced")


# ------------------------------------------- B. UNCLASSIFIED is not a pass
def test_unclassified_and_ok_are_disjoint():
    for vector in ("forge_positivity.export", "forge_large_elim.export",
                   "control_small_elim.export"):
        r = classify(vector)
        named = {n for n, _ in r["unclassified"]} | {n for n, _ in r["violations"]}
        assert not (named & set(r["ok"])), vector
        assert r["checked"] == len(r["ok"]) + len(r["violations"]) + len(r["unclassified"])


def test_undecidable_field_type_declines_rather_than_approves():
    """A field whose type needs a definition the export does not carry must
    come back UNCLASSIFIED, not OK. The `--specs` export is assumed
    declarations only, so this is the common case over a real library."""
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    causes = {}
    for s in d["sets"]:
        for cause, n in s["unclassified_by_cause"].items():
            causes[cause] = causes.get(cause, 0) + n
    assert causes.get("field type not in export", 0) > 0
    assert FIELD_TYPE_NOT_IN_EXPORT, "the cause must be a tagged constant"


def test_subsingleton_returns_three_outcomes_not_two():
    """`subsingleton()` must be able to say UNKNOWN. A two-valued version
    would have to guess, and the guess that matters is the one that says a
    large eliminator is fine."""
    import inspect
    src = inspect.getsource(subsingleton)
    assert '"UNKNOWN"' in src
    assert '"NO"' in src and '"YES"' in src


def test_no_caller_treats_unclassified_as_a_pass():
    """Source-level, as for positivity: the quiet version of this mistake is a
    caller writing `if not r["violations"]`."""
    offenders = []
    for path in sorted((ROOT / "harness").rglob("*.py")):
        if path.name == "recursor.py":
            continue
        text = path.read_text(encoding="utf-8")
        if "check_env" not in text or "recursor" not in text:
            continue
        if "violations" in text and "unclassified" not in text:
            offenders.append(str(path.relative_to(ROOT)))
    assert not offenders, (
        f"these read recursor violations without reading unclassified: {offenders}")


def test_module_docstring_states_what_it_does_not_check():
    import kernel3.recursor as R
    doc = R.__doc__ or ""
    assert "iota" in doc
    assert "UNCLASSIFIED" in doc
    assert "provenance gate" in doc


def test_node_kinds_are_imported_not_restated():
    src = (ROOT / "harness" / "kernel3" / "recursor.py").read_text(encoding="utf-8")
    assert "from .terms import BVAR, SORT, CONST, APP, PI" in src
    assert not re.search(r"^\s*(BVAR|SORT|CONST|APP|PI)\s*=\s*\d", src, re.M)


# ------------------------------------------------ C. the differential record
def test_differential_record_is_consistent():
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    assert d["schema"] == "ampas-recursor-differential/1"
    assert d["pass"] == "recursor"
    t = d["totals"]
    assert t["checked"] == sum(s["checked"] for s in d["sets"])
    assert t["ok"] == sum(s["ok"] for s in d["sets"])
    assert t["unclassified"] == sum(len(s["unclassified"]) for s in d["sets"])
    for s in d["sets"]:
        assert s["checked"] == (
            s["ok"] + len(s["violations"]) + len(s["unclassified"])), s["environment"]
        assert sum(s["unclassified_by_cause"].values()) == len(s["unclassified"])


def test_differential_record_reports_no_violation():
    """Lean generated every one of these recursors itself. A violation here
    would be a bug in the pass, and harness/spec_diff.py exits non-zero on one.

    This is not hypothetical: the first version of the rules check assumed a
    mutual family's recursor carries iota rules for every constructor in the
    family. Nineteen Mathlib recursors reported VIOLATION, all of them
    legitimate, and the rule was wrong — a mutual recursor carries rules for
    the member it eliminates. Without the differential test the pass would have
    shipped rejecting valid code, and a rule that is wrong in one direction can
    be wrong in the other."""
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    assert d["totals"]["violations"] == 0
    for s in d["sets"]:
        assert s["violations"] == [], s["environment"]


def test_differential_record_covers_both_environments():
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    envs = {s["environment"] for s in d["sets"]}
    assert "AmpasRef.Guards" in envs
    assert any("Mathlib" in e for e in envs), envs
    assert d["totals"]["checked"] > 1000


def test_differential_record_does_not_claim_the_rules_are_checked():
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    means = " ".join(d["means"])
    assert "iota" in means
    assert "provenance gate" in means
    assert not re.search(r"(iota rules|specification[s]?) (are|is) checked", means)


def test_unclassified_causes_are_named_not_lumped():
    """`other` swallowing the unclassified set is how a new cause becomes
    invisible. Every declined declaration must fall under a named cause."""
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    for s in d["sets"]:
        assert s["unclassified_by_cause"].get("other", 0) == 0, (
            f"{s['environment']} has unclassified declarations under no named cause")


# ----------------------------------------------------------- the primitives
def test_is_prop_valued_distinguishes_prop_from_sort_u():
    env = load("forge_large_elim.export")
    p = env.get(nm(env, "P"))
    assert is_prop_valued(p.type)
    env2 = load("forge_positivity.export")
    my_false = env2.get(nm(env2, "MyFalse"))
    assert is_prop_valued(my_false.type)


def test_k_flag_is_checked_against_the_constructor():
    """K-like reduction says any two proofs are the same term. Setting it on an
    inductive whose constructor has fields would make the kernel identify
    terms that differ."""
    env = load("forge_large_elim.export")
    rec = env.get(nm(env, "P.rec"))
    assert rec.k is False, "the vector does not exercise k; this guards the premise"
    import dataclasses
    forged = dataclasses.replace(rec, k=True)
    verdict, why = check_recursor(forged, env)
    assert verdict == "VIOLATION"
    assert "K-like" in why


def test_a_missing_iota_rule_is_a_violation():
    env = load("control_small_elim.export")
    rec = env.get(nm(env, "P.rec"))
    import dataclasses
    stripped = dataclasses.replace(rec, rules=rec.rules[:1])
    verdict, why = check_recursor(stripped, env)
    assert verdict == "VIOLATION"
    assert "iota rules" in why


def test_a_foreign_iota_rule_is_a_violation():
    env = load("control_small_elim.export")
    rec = env.get(nm(env, "P.rec"))
    import dataclasses
    c, nf, rhs = rec.rules[0]
    swapped = dataclasses.replace(rec, rules=[(c, nf, rhs), (c, nf, rhs)])
    verdict, why = check_recursor(swapped, env)
    assert verdict == "VIOLATION"
    assert "two iota rules" in why


def test_a_wrong_field_count_in_a_rule_is_a_violation():
    env = load("control_small_elim.export")
    rec = env.get(nm(env, "P.rec"))
    import dataclasses
    rules = [(c, nf + 1, rhs) for c, nf, rhs in rec.rules]
    verdict, why = check_recursor(dataclasses.replace(rec, rules=rules), env)
    assert verdict == "VIOLATION"
    assert "fields but the" in why


@pytest.mark.parametrize("field", ["num_params", "num_indices", "num_minors",
                                   "num_motives"])
def test_an_arity_lie_is_never_approved(field):
    """A recursor claiming a different arity from the inductive it eliminates
    must never come back OK. Which of the two non-OK verdicts it gets depends
    on which check trips first -- raising `num_indices` makes the motive
    unreadable, so the pass declines instead of judging, and declining is the
    safe direction. What matters is that nothing here is approved."""
    env = load("control_small_elim.export")
    rec = env.get(nm(env, "P.rec"))
    import dataclasses
    broken = dataclasses.replace(rec, **{field: getattr(rec, field) + 1})
    verdict, why = check_recursor(broken, env)
    assert verdict in ("VIOLATION", "UNCLASSIFIED"), why


# ---------------------------------------------------------------------------
# What the Lean Kernel Arena found (ROADMAP 6c, 2026-10-14)
#
# Three rules of this pass were wrong, and none of the four hand-written
# forgeries nor the 3410-recursor differential over Init and Mathlib could
# have found any of them. Each test below names the arena vector.
def test_a_level_parameter_may_be_instantiated_to_prop():
    """`bad/bugs/large-elim-param`: `MyBool : Sort u` with two constructors and
    a recursor into `Sort v`. At `u := 0` that is a two-constructor Prop with a
    large eliminator. The first version asked whether the sort was LITERALLY
    zero and let `Sort u` through -- wrong in the ACCEPTING direction, which is
    the direction ROADMAP 2 warned about."""
    from kernel3.terms import sort, param, succ, ZERO, lmax, limax, Name
    u = param(Name.mk(("u",)))
    v = param(Name.mk(("v",)))
    assert is_prop_valued(sort(ZERO))          # Prop
    assert is_prop_valued(sort(u))             # Sort u -- u := 0 is legal
    assert is_prop_valued(sort(lmax(u, v)))    # max u v -- both may be 0
    assert is_prop_valued(sort(limax(u, v)))   # imax u v -- zero when v is
    assert not is_prop_valued(sort(succ(u)))   # Sort (u+1): never Prop
    assert not is_prop_valued(sort(succ(ZERO)))


def test_a_recursor_with_no_family_is_a_violation_not_a_decline():
    """`bad/bugs/orphan-rec`: a recursor with `all: []`, typed `False`. The
    first version resolved the family to the recursor's own name, found that is
    not an inductive, and DECLINED -- which let `rogue : False` through."""
    env = load("control_small_elim.export")
    rec = env.get(nm(env, "P.rec"))
    import dataclasses
    orphan = dataclasses.replace(rec, all_names=[], induct=None)
    verdict, why = check_recursor(orphan, env)
    assert verdict == "VIOLATION"
    assert "declares no inductive family" in why


def test_fewer_motives_than_family_members_is_a_violation():
    """`bad/other/extra-rec` and `bad/tutorial/073_BogusRecursor`: a recursor
    with ZERO motives. The first version tested `!=` and called both directions
    "a nested inductive's auxiliary recursor", so too FEW motives was declined.
    A nested auxiliary has MORE (Lean.Syntax.rec has 3 for a family of 1).
    Measured over Init and Mathlib: 0 recursors have fewer, 183 have more."""
    env = load("control_small_elim.export")
    rec = env.get(nm(env, "P.rec"))
    import dataclasses
    verdict, why = check_recursor(dataclasses.replace(rec, num_motives=0), env)
    assert verdict == "VIOLATION"
    assert "one motive per member" in why
    verdict2, why2 = check_recursor(dataclasses.replace(rec, num_motives=3), env)
    assert verdict2 == "UNCLASSIFIED"
    assert "auxiliary recursor" in why2


def test_a_misnamed_recursor_is_a_violation():
    """`bad/tutorial/136_misnamed_rec_user` and `137_dup_rec_def2`: a recursor
    named something other than `<member>.rec`, so the name `I.rec` is free for
    a user definition to occupy. Measured over the same 3410 recursors: every
    one is `<member>.rec` or `<member>.rec_N`, with no exceptions to carve."""
    env = load("control_small_elim.export")
    rec = env.get(nm(env, "P.rec"))
    import dataclasses
    from kernel3.terms import Name
    bad = dataclasses.replace(rec, name=Name.mk(("P", "not_rec")))
    verdict, why = check_recursor(bad, env)
    assert verdict == "VIOLATION"
    assert "not `<member>.rec`" in why
    # the nested auxiliary naming must still be accepted
    aux = dataclasses.replace(rec, name=Name.mk(("P", "rec_1")), num_motives=2)
    verdict2, _ = check_recursor(aux, env)
    assert verdict2 == "UNCLASSIFIED"
