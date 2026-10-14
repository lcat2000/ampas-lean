"""The fifth specification pass: declaration well-formedness (ROADMAP 3/6c).

Two of the nine bad arena tests `kernel3` still accepted are not about terms,
inductives or flags, but about whether the declaration is a declaration at
all. `bad/tutorial/014_selfProof` is the serious one:

    theorem selfProof : (p : Prop) → p := selfProof

The value is a reference to itself, so it type-checks against its own declared
type, and what it proves is everything. Lean rejects it structurally — a
declaration enters the environment only AFTER being checked, so the
self-reference is an unknown constant — and `kernel3`'s reader adds first and
checks after, which makes the constant resolve.

`docs/ARENA-RESULT.md` had both under "outside what `kernel3` checks rather
than bugs in it", and for `014` that was an overstatement of the scope
boundary. These tests pin the correction as much as the fix.
"""
import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))

from kernel3 import declaration                                    # noqa: E402
from kernel3.declaration import (VALUED_KINDS, check_env, mutual_block_referential,
                                 self_referential,
                                 theorem_type_is_a_universe)       # noqa: E402
from kernel3.parse import Decl, Env                                # noqa: E402
from kernel3.terms import Name, ZERO, app, const, pi, sort, succ   # noqa: E402

N = lambda *p: Name.mk(p)                                          # noqa: E731
ANON = Name.anonymous()
# A stand-in PROPOSITION. `sort(ZERO)` is `Prop` itself, which is a universe
# and therefore trips theorem_type_is_a_universe -- it caught three fixtures
# in this file before it caught anything in the arena.
PROP = const(N("False"), [])


def forall(dom, body):
    return pi(ANON, dom, body)


def decl(kind, name, ty, val=None, **kw):
    return Decl(kind, name, ty, [], value=val, **kw)


# ---- 014_selfProof: the one that proves False

def test_a_theorem_whose_value_is_itself_is_a_violation():
    """The arena test, reduced to its shape: `theorem t : Prop := t`."""
    t = N("t")
    env = Env()
    env.add(decl("thm", t, sort(ZERO), const(t, [])))
    r = check_env(env)
    assert [n for n, _ in r["violations"]] == ["t"]
    why = r["violations"][0][1]
    assert "refers to `t` itself" in why
    assert "only after checking it" in why, (
        "the reason must name WHY no Lean export contains this, or a reader "
        "cannot tell a rule from a preference")


def test_the_self_reference_is_found_at_any_depth():
    """`occurs` walks the whole term, so wrapping the self-reference in
    applications and binders must not hide it -- a rule that only looked at
    the head would be defeated by `t 0` or `fun _ => t`."""
    t = N("t")
    for val in (app(const(t, []), PROP),
                forall(PROP, const(t, [])),
                app(app(const(N("f"), []), PROP), const(t, []))):
        env = Env()
        env.add(decl("thm", t, PROP, val))
        assert [n for n, _ in check_env(env)["violations"]] == ["t"], val


def test_every_valued_kind_is_covered_not_just_theorems():
    """A `def` or an `opaque` that names itself is the same defect: the value
    type-checks against its own declared type and the declared type can say
    anything."""
    assert set(VALUED_KINDS) == {"def", "thm", "opaque"}
    for kind in VALUED_KINDS:
        t = N("t")
        env = Env()
        env.add(decl(kind, t, PROP, const(t, [])))
        assert [n for n, _ in check_env(env)["violations"]] == ["t"], kind


def test_mentioning_a_different_constant_is_fine():
    t, u = N("t"), N("u")
    env = Env()
    env.add(decl("thm", u, PROP, const(N("p"), [])))
    env.add(decl("thm", t, PROP, const(u, [])))
    r = check_env(env)
    assert r["violations"] == []
    assert len(r["ok"]) == 2


def test_a_declaration_without_a_value_is_not_self_referential():
    """An axiom, an inductive or a recursor has no value to read. Treating
    the absence as suspect would reject every assumed declaration there is."""
    for kind in ("ax", "ind", "ctor", "rec", "quot"):
        t = N("t")
        assert self_referential(decl(kind, t, sort(ZERO))) is False, kind
    assert self_referential(decl("def", N("t"), sort(ZERO), None)) is False


# ---- 012_nonPropThm: the label error

def test_a_theorem_whose_statement_is_a_universe_is_a_violation():
    """The arena test: `theorem nonPropThm : Prop := ...`. A theorem's type
    must be a proposition, and `Prop : Type`."""
    env = Env()
    env.add(decl("thm", N("t"), sort(ZERO), forall(sort(ZERO), const(N("x"), []))))
    r = check_env(env)
    assert len(r["violations"]) == 1
    assert "universe, not a" in r["violations"][0][1]


def test_it_holds_under_a_binder_prefix():
    """`∀ x, Sort u` has type `Sort (imax … (u+1))`, never Prop, so stripping
    the ∀ prefix before looking is required rather than cosmetic."""
    assert theorem_type_is_a_universe(
        decl("thm", N("t"), forall(PROP, sort(succ(ZERO))), sort(ZERO)))
    assert theorem_type_is_a_universe(
        decl("thm", N("t"), forall(PROP, forall(PROP, sort(ZERO))), sort(ZERO)))
    # and a ∀ ending in a proposition is fine
    assert theorem_type_is_a_universe(
        decl("thm", N("t"), forall(PROP, PROP), sort(ZERO))) is False


def test_a_definition_may_be_typed_by_a_universe():
    """`def Foo : Type := Nat` is perfectly ordinary. The rule is about the
    `thm` label, not about universes."""
    for kind in ("def", "opaque", "ax"):
        assert theorem_type_is_a_universe(
            decl(kind, N("t"), sort(succ(ZERO)), sort(ZERO))) is False, kind


def test_an_ordinary_proposition_passes():
    env = Env()
    env.add(decl("thm", N("t"), app(const(N("P"), []), sort(ZERO)), sort(ZERO)))
    assert check_env(env)["violations"] == []


# ---- the shape of the pass

def test_neither_rule_ever_declines():
    """Both are decided by reading the declaration, as in safety.py and
    unlike the three inductive passes, which all have shapes they cannot
    judge. UNCLASSIFIED must never be the outcome and must never count as a
    pass."""
    env = Env()
    env.add(decl("thm", N("a"), PROP, const(N("a"), [])))
    env.add(decl("def", N("b"), sort(ZERO), sort(ZERO)))
    r = check_env(env)
    assert r["unclassified"] == []
    assert r["checked"] == len(r["ok"]) + len(r["violations"]) == 2


def test_both_rules_can_fire_on_one_declaration():
    """They are independent defects and the record must show both rather than
    stopping at the first."""
    t = N("t")
    env = Env()
    env.add(decl("thm", t, sort(ZERO), const(t, [])))
    why = check_env(env)["violations"][0][1]
    assert "refers to `t` itself" in why and "universe, not a" in why


def test_mutual_block_references_are_recorded_and_are_not_violations():
    """A value mentioning another member of its own mutual block should also
    be impossible, but nothing in the arena pins it, and `should` is the word
    that put three bugs in the iota pass. It is recorded so a rule can later
    be added on evidence."""
    a, b = N("a"), N("b")
    env = Env()
    env.add(decl("def", a, sort(ZERO), const(b, []), all_names=[a, b]))
    r = check_env(env)
    assert r["violations"] == []
    assert r["mutual_block_references"] == [["a", ["b"]]]
    # and a self-reference is not double-counted as a block reference
    env2 = Env()
    env2.add(decl("def", a, sort(ZERO), const(a, []), all_names=[a, b]))
    assert check_env(env2)["mutual_block_references"] == []


def test_the_module_states_what_it_does_not_cover():
    doc = " ".join((theorem_type_is_a_universe.__doc__ or "").split())
    assert "theorem foo : Nat := 5" in doc, (
        "the residue must be named: a thm typed by some other non-Prop needs "
        "infer(), which would make this pass depend on the term checker")
    assert "depend on the term checker" in doc
    mod = " ".join((declaration.__doc__ or "").split())
    assert "overstatement of this checker's scope boundary" in mod
    assert "compile step" in mod, (
        "the containment claim must name the mechanism that actually applies; "
        "the provenance gate does not, since both are DEFINED declarations")


# ---- the differential, and the record

def test_the_differential_record_is_clean_over_the_libraries():
    """If a real Lean declaration referenced itself, this rule would be wrong
    and the pass would reject legitimate work. 3849 valued declarations over
    Init and Mathlib say it does not."""
    p = ROOT / "evidence" / "declaration_differential.json"
    if not p.exists():
        pytest.skip("run scripts/verify.sh at tier 3 to produce it")
    d = json.loads(p.read_text(encoding="utf-8"))
    assert d["totals"]["violations"] == 0
    assert d["totals"]["unclassified"] == 0
    assert d["totals"]["checked"] > 4000
    blob = " ".join(d.get("means", []))
    assert "FULL export" in blob, (
        "a --specs export has no values, so this pass checks nothing over one "
        "and the record must say which kind of export it needs")
    assert "mutual_block_references" in blob


def test_the_arena_record_shows_the_two_tests_caught_by_this_pass():
    p = ROOT / "evidence" / "arena_run_round9.json"
    if not p.exists():
        pytest.skip("run harness/arena_run.py to produce it")
    d = json.loads(p.read_text(encoding="utf-8"))
    by = {r["test"]: r for r in d["results"]}
    for t in ("bad/tutorial/012_nonPropThm.ndjson", "bad/tutorial/014_selfProof.ndjson"):
        r = by[t]
        assert r["expected"] == "REJECTED"
        assert r["term_only"] == "ACCEPTED", (
            f"{t}: the term layer accepting it is the finding; if this changes, "
            f"the term checker moved and the attribution below is wrong")
        assert r["with_spec_passes"] == "REJECTED", t


def test_the_arena_result_doc_corrects_its_own_scope_claim():
    txt = " ".join((ROOT / "docs" / "ARENA-RESULT.md")
                   .read_text(encoding="utf-8").split())
    assert "014_selfProof" in txt
    # the correction must be present, not a silent edit
    assert "overstatement" in txt or "was wrong" in txt, (
        "the document said these were outside kernel3's scope; a reader must "
        "be able to see that claim retracted rather than find it gone")
    assert "introduced_assumptions" in txt, (
        "the containment claim must be corrected too: both are defined "
        "declarations, so the provenance gate reports nothing for them")


def test_the_arena_improvement_is_attributed_to_the_right_cause():
    """Round 9's `wrongly_rejected` also moved, and not because of this pass:
    a `good/perf` test was killed by the OOM killer under a timeout it did not
    reach. Round 7 learned this the hard way -- five fixes moved the count by
    fourteen, and six of those were caught by an adjacent rule. An unexplained
    improvement is as suspicious as an unexplained regression."""
    p = ROOT / "evidence" / "arena_run_round9.json"
    if not p.exists():
        pytest.skip("run harness/arena_run.py to produce it")
    new = json.loads(p.read_text(encoding="utf-8"))
    old = json.loads((ROOT / "evidence" / "arena_run_after_fixes.json")
                     .read_text(encoding="utf-8"))
    ob = {r["test"]: r for r in old["results"]}
    moved = {r["test"]: (ob[r["test"]]["with_spec_passes"], r["with_spec_passes"])
             for r in new["results"]
             if r["test"] in ob
             and ob[r["test"]]["with_spec_passes"] != r["with_spec_passes"]}
    gained = {t for t, (a, b) in moved.items() if a == "ACCEPTED" and b == "REJECTED"}
    assert gained == {"bad/tutorial/012_nonPropThm.ndjson",
                      "bad/tutorial/014_selfProof.ndjson"}, (
        f"this pass targeted two tests; the count moved on {sorted(gained)}. "
        f"Any extra is being caught by an adjacent rule, which is round 7's "
        f"six incidental catches repeating.")
    assert (new["totals"]["with_spec_passes"]["wrongly_accepted"]
            == old["totals"]["with_spec_passes"]["wrongly_accepted"] - 2)
    # and every OTHER movement must be a resource kill, never a verdict
    for t, (a, b) in moved.items():
        if t in gained:
            continue
        r = next(x for x in new["results"] if x["test"] == t)
        assert b == "DECLINED" and "exit -9" in (r.get("detail") or ""), (
            f"{t}: {a} -> {b} is unexplained. It is not this pass's doing and "
            f"it is not a resource kill either, so something else moved.")
    txt = " ".join((ROOT / "docs" / "ARENA-RESULT.md")
                   .read_text(encoding="utf-8").split())
    assert "is NOT an improvement and is not claimed" in txt
    assert "OOM killer" in txt
