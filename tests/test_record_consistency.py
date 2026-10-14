"""Cross-check facts this repository records in more than one place.

The A01 mislabel survived nine rounds by a specific mechanism: one fact was
recorded twice -- `ablation.json` listed "primary kernel, third check" for the
kernel-bypass attack while `third_check.status` called the same event an
unadjudicated DISAGREEMENT -- and nothing ever compared the two. Either record
alone looked coherent.

So these tests do not assert that a derived field equals a constant. That is
how the old A01 test came to pin the mistake. They RECOMPUTE each derived
field from the data sitting next to it and assert the two agree. A label that
cannot be recomputed from its own evidence is a label nobody is checking.

The second instance, found while writing this: `harness/ablation.py` derives
its signal list by STRING-MATCHING the claim-level reason text. Reword a
reason and the signal silently disappears from the "which layer caught each
attack" table -- which is the evidence the README leans on to show that no
single layer is doing all the work. `test_every_blocking_reason_maps_to_a_signal`
is the guard for that.
"""
import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))

RESULTS = [ROOT / "build" / "corpus_core.json",
           ROOT / "evidence" / "corpus_results_threechecks.json",
           ROOT / "evidence" / "corpus_results.json"]

POSITIVE = "kernel-checked; statement matches the reference; axioms within policy"


def _load() -> tuple[list[dict], dict]:
    """The results, and any corrections recorded against that file.

    `evidence/` holds the reference run, made with the pre-2026-10-14
    labeller, so it carries a status this repository now knows to be wrong.
    Regenerating it here would replace a tier-3 record with a tier-1 one and
    lose signals -- falsifying a historical record instead of annotating it.
    So the file carries a `record_corrections` entry and these tests honour
    it: a field named there is checked against the CORRECTED value, and a
    correction that stops being needed makes the test fail rather than pass
    quietly."""
    for p in RESULTS:
        if p.exists():
            d = json.loads(p.read_text(encoding="utf-8"))
            subs = d if isinstance(d, list) else d.get("submissions", d.get("results", []))
            if subs:
                corr = {}
                if isinstance(d, dict):
                    for c in d.get("record_corrections", []):
                        for mod in c["affects"]:
                            corr[(mod, c["field"])] = c
                return subs, corr
    pytest.skip("no corpus results on disk; run ./scripts/verify.sh 1")


@pytest.fixture(scope="module")
def loaded() -> tuple[list[dict], dict]:
    return _load()


@pytest.fixture(scope="module")
def subs(loaded) -> list[dict]:
    return loaded[0]


@pytest.fixture(scope="module")
def corrections(loaded) -> dict:
    return loaded[1]


def test_certified_agrees_with_the_reasons_beside_it(subs):
    """`certified` is a verdict; `reasons` is its evidence. A certified claim
    carrying a blocking reason, or a rejected one carrying only the positive
    reason, would mean the two were written independently."""
    for s in subs:
        for c in s.get("claims", []):
            where = f"{s.get('module')}/{c['claim']}"
            if c["certified"]:
                assert c["reasons"] == [POSITIVE], (
                    f"{where}: certified, but the reasons say {c['reasons']}")
            elif not c.get("inconclusive"):
                assert c["reasons"] and c["reasons"] != [POSITIVE], (
                    f"{where}: not certified, but the only reason is the "
                    f"positive one")


def test_inconclusive_agrees_with_recorded_resource_exhaustion(subs):
    """A5: a resource limit is not a rejection. `inconclusive` must be set
    exactly when the run recorded exhaustion, or the distinction the whole
    section rests on is being asserted twice and reconciled never."""
    for s in subs:
        exhausted = bool(s.get("resource_exhausted"))
        for c in s.get("claims", []):
            if c.get("inconclusive"):
                assert exhausted, (
                    f"{s.get('module')}/{c['claim']}: marked INCONCLUSIVE with "
                    f"no resource exhaustion recorded for the submission")


def test_third_check_status_is_recomputable_from_its_own_errors(subs, corrections):
    """The status label must follow from the error list and the kernels'
    result. This is the exact pair that disagreed for nine rounds."""
    for s in subs:
        tc = s.get("third_check", {})
        if not tc.get("run"):
            continue
        where = s.get("module", "?")
        errors = tc.get("errors") or []
        fix = corrections.get((where, "results[].third_check.status"))
        if fix is not None:
            # A known-wrong field in a historical record. The correction has to
            # BE the corrected value, so an annotation cannot excuse an
            # arbitrary one, and it has to still be needed.
            assert tc.get("status") == fix["recorded_value"], (
                f"{where}: a correction is recorded for a value this file no "
                f"longer contains; remove the correction")
            tc = dict(tc, status=fix["correct_value"],
                      unadjudicated_disagreement=False)
        replay_ok = s.get("kernel_replay") and (
            s.get("kernel_replay_independent") is not False)
        status = tc.get("status", "")
        if not errors:
            assert status == "CONFIRMED", f"{where}: no errors but status {status!r}"
            assert not tc.get("unadjudicated_disagreement")
        elif not replay_ok:
            assert status.startswith("CORROBORATION"), (
                f"{where}: the third check objected and the Lean kernels "
                f"rejected too, so this is corroboration, not {status!r}")
            assert tc.get("unadjudicated_disagreement") is False
        else:
            assert status.startswith("DISAGREEMENT"), (
                f"{where}: the kernels accepted and the third check objected, "
                f"which is a disagreement, not {status!r}")


def test_third_check_counts_are_internally_consistent(subs):
    for s in subs:
        tc = s.get("third_check", {})
        if not tc.get("run") or "checked" not in tc:
            continue
        assert tc["checked"] <= tc["total"], s.get("module")
        # every disagreement names a declaration, and the unadjudicated ones
        # are a subset of them
        assert set(tc.get("unadjudicated", [])) <= set(tc.get("disagreements", [])), (
            f"{s.get('module')}: an unadjudicated disagreement that is not in "
            f"the disagreement list")


def test_the_ablation_table_is_recomputable_from_the_results(subs):
    """`ablation.json` is the evidence that no single layer does all the work.
    If it is stale relative to the corpus results, that evidence is about a
    run that no longer exists -- and it was the HALF-RIGHT record in the A01
    case, so its agreement with the results matters."""
    # Both files must come from the SAME run. build/ is a tier-1 core run and
    # evidence/ is the recorded tier-3 one; crossing them would compare an
    # `independent kernel` signal that needs lean4lean against a run without
    # it, and report a difference that is a tier difference.
    pairs = [(ROOT / "build" / "ablation.json", ROOT / "build" / "corpus_core.json"),
             (ROOT / "evidence" / "ablation.json",
              ROOT / "evidence" / "corpus_results_threechecks.json")]
    abl_path = results_path = None
    for a, r in pairs:
        if a.exists() and r.exists():
            abl_path, results_path = a, r
            break
    if abl_path is None:
        pytest.skip("no matched ablation/results pair on disk")
    import ablation
    rows = {r["attack"]: r for r in json.loads(abl_path.read_text(encoding="utf-8"))}
    rd = json.loads(results_path.read_text(encoding="utf-8"))
    rsubs = rd if isinstance(rd, list) else rd.get("submissions", rd.get("results", []))
    by_mod = {s.get("module"): s for s in rsubs}
    for attack, row in rows.items():
        s = by_mod.get(attack)
        if s is None:
            continue
        assert ablation.signals(s) == row["signals"], (
            f"{attack}: the recorded signals {row['signals']} are not what the "
            f"results now produce ({ablation.signals(s)}); regenerate "
            f"build/ablation.json")


def test_every_blocking_reason_maps_to_a_signal(subs):
    """`ablation.py` classifies reasons by matching their TEXT. A reworded
    reason matches nothing and its layer vanishes from the table silently --
    the table still looks complete, with one fewer signal.

    So every blocking reason must either produce a signal or be on the list
    below, which names the reasons that deliberately do not (the layer is
    recorded through a flag or the kernel fields instead)."""
    import ablation
    NOT_A_SIGNAL = (
        "kernel replay did not succeed",
        "the third check also rejected",
        "the third check rejects a declaration",
        "INCONCLUSIVE:",
        "forbidden:",
    )
    unmatched = []
    for s in subs:
        for c in s.get("claims", []):
            for reason in c["reasons"]:
                if reason == POSITIVE or reason.startswith(NOT_A_SIGNAL):
                    continue
                # a single-claim record carrying only this reason
                probe = {"compiled": True, "kernel_replay": True,
                         "kernel_replay_independent": None, "third_check": {},
                         "claims": [{"reasons": [reason], "flags": []}]}
                if not ablation.signals(probe):
                    unmatched.append(f"{s.get('module')}/{c['claim']}: {reason[:70]}")
    assert not unmatched, (
        "these blocking reasons produce no ablation signal, so the layer that "
        "caught them is missing from the table:\n  " + "\n  ".join(unmatched))


def test_attestation_guard_fields_agree(subs):
    """`guards_satisfied` beside `guard_problems`: satisfied exactly when the
    problem list is empty."""
    for sub in ("attestations", "attestations-mathlib", "attestations-fermat"):
        d = ROOT / "reference" / sub
        if not d.is_dir():
            continue
        for f in sorted(d.glob("*.json")):
            rec = json.loads(f.read_text(encoding="utf-8"))
            assert rec["guards_satisfied"] == (not rec["guard_problems"]), (
                f"{sub}/{f.name}: guards_satisfied={rec['guards_satisfied']} "
                f"with problems {rec['guard_problems']}")


def test_counterexample_counts_add_up():
    """box_size = checked + vacuous + unresolved. The three are reported
    separately so a reader can see how much of the box meant anything; if they
    do not sum, one of them is measuring something else."""
    for name in ("counterexample_search.json", "counterexample_search_mathlib.json",
                 "counterexample_search_fermat.json"):
        p = ROOT / "reference" / name
        if not p.exists():
            continue
        for r in json.loads(p.read_text(encoding="utf-8"))["searches"]:
            if "box_size" not in r:
                continue
            total = (r.get("checked_points", 0) + r.get("vacuous_points", 0)
                     + r.get("unresolved_points", 0))
            assert total == r["box_size"], (
                f"{r['claim']}: {r['box_size']} points in the box but "
                f"{total} accounted for")


def test_derivation_outcomes_follow_from_their_kernel_records():
    """`outcome: REFUTED` must follow from the kernel fields beside it, not sit
    next to them. harness/derivation_search.verdict() is the one definition."""
    p = ROOT / "reference" / "derivation_search.json"
    if not p.exists():
        pytest.skip("no derivation search on record")
    import derivation_search
    for r in json.loads(p.read_text(encoding="utf-8"))["searches"]:
        if "kernel" not in r:
            continue
        assert r["outcome"] == derivation_search.verdict(r["kernel"]), (
            f"{r['claim']}: recorded {r['outcome']} but its kernel record "
            f"yields {derivation_search.verdict(r['kernel'])}")


# ---------------------------------------------------------------------------
# A status that names an adjudication must carry it (2026-10-14)
#
# The third check's status read "DISAGREEMENT (adjudicated: checker
# incompleteness)" beside an `adjudication` field of null, so a reader had to
# leave the record to find out which finding was meant -- and would then
# discover that the adjudications file is PENDING_REVIEWER_CONFIRMATION, which
# is weaker than the word "adjudicated" suggests. Third time this session that
# a derived label's support was not beside it (after the A01 mislabel and
# ablation.py's filename prefix), so it gets a test.
def _third_check_records():
    out = []
    for path in sorted((ROOT / "evidence").glob("*.json")) + \
                sorted((ROOT / "build").glob("*validation*.json")) + \
                sorted((ROOT / "build").glob("corpus*.json")):
        try:
            d = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        for r in (d.get("results") or []) if isinstance(d, dict) else []:
            tc = r.get("third_check") or {}
            if tc.get("run"):
                out.append((path.name, r.get("module"), tc))
    return out


def test_an_adjudicated_status_names_the_adjudication():
    checked = 0
    for name, module, tc in _third_check_records():
        status = str(tc.get("status", ""))
        if "adjudicated:" not in status:
            continue
        if "adjudicated" not in tc:
            continue        # written before 2026-10-14; the field did not exist
        checked += 1
        assert tc["adjudicated"], (name, module,
                                   "status says adjudicated and the list is empty")
        for a in tc["adjudicated"]:
            assert a.get("name"), (name, module)
            assert a.get("finding"), (name, module, a.get("name"))
    # not asserted non-zero: a record set may legitimately contain no
    # adjudicated disagreement, and inventing one to satisfy a test would be
    # the opposite of the point


def test_an_adjudicated_status_says_whether_a_reviewer_confirmed_it():
    for name, module, tc in _third_check_records():
        if "adjudicated:" not in str(tc.get("status", "")):
            continue
        so = tc.get("adjudication_sign_off")
        if so is None and "adjudicated" not in tc:
            continue        # pre-2026-10-14 record
        assert so, (name, module, "no sign-off state beside an adjudicated status")
        assert "status" in so and "confirmed_by" in so, (name, module)
        assert "unconfirmed adjudication exists" in (so.get("means") or ""), (
            name, module,
            "the record must not let 'adjudicated' read as 'a reviewer agreed'")


def test_every_adjudicated_name_is_in_the_adjudications_file():
    adj_path = ROOT / "reference" / "third_check_adjudications.json"
    adj = {d["name"] for d in
           json.loads(adj_path.read_text(encoding="utf-8"))["declarations"]}
    for name, module, tc in _third_check_records():
        for a in tc.get("adjudicated") or []:
            assert a["name"] in adj, (name, module, a["name"])


def test_an_adjudicated_disagreement_is_not_credited_as_catching_an_attack():
    """The ablation table answers "which layer actually caught this attack".
    An ADJUDICATED third-check disagreement is about library code the checker
    cannot decide -- four history attacks trip TC-02 merely by using `decide`
    over a bounded quantifier, and a genuine submission doing the same would
    trip it too. Crediting the third check there named a layer that caught
    nothing, in the one table the README cites as evidence that each attack is
    stopped by the right layer."""
    import ablation
    base = {"compiled": True, "kernel_replay": True,
            "kernel_replay_independent": True, "claims": []}
    adjudicated_only = dict(base, third_check={
        "run": True, "errors": [["Nat.decidableBallLT.match_5", "imax"]],
        "unadjudicated": [],
        "adjudicated": [{"name": "Nat.decidableBallLT.match_5",
                         "finding": "TC-02"}]})
    assert "third check" not in ablation.signals(adjudicated_only)

    unadjudicated = dict(base, third_check={
        "run": True, "errors": [["Ampas.Claims.false_thm", "mismatch"]],
        "unadjudicated": ["Ampas.Claims.false_thm"]})
    assert "third check" in ablation.signals(unadjudicated)

    # a record from before `unadjudicated` existed keeps the old reading
    legacy = dict(base, third_check={"run": True, "errors": [["x", "y"]]})
    assert "third check" in ablation.signals(legacy)


def test_an_adjudicated_disagreement_is_still_recorded_somewhere():
    """Dropped from `signals` is not the same as dropped from the record: the
    row must still say the third check objected and why it does not count."""
    path = ROOT / "evidence" / "ablation_external.json"
    if not path.exists():
        pytest.skip("run tier 3 to produce it")
    rows = json.loads(path.read_text(encoding="utf-8"))
    noted = [r for r in rows if r.get("third_check_note")]
    assert noted, "no row carries an adjudicated third-check note"
    for r in noted:
        n = r["third_check_note"]
        assert n["adjudicated"]
        assert "caught nothing about this submission" in n["means"]
        assert "third check" not in r["signals"], r["attack"]


def test_the_core_ablation_record_is_reproducible_from_the_committed_results():
    """evidence/ablation.json has 13 rows: the 12 core attacks and
    A13_mathlib_redefine, which only runs at tier 3. Rebuilding it from the
    core results alone gives 12, so for a while the committed record could not
    be reproduced by scripts/verify.sh and a reader diffing their run found a
    missing row with no explanation."""
    import ablation
    rows = []
    for name in ("corpus_results_threechecks.json", "corpus_results_mathlib3.json"):
        d = json.loads((ROOT / "evidence" / name).read_text(encoding="utf-8"))
        for r in d["results"]:
            if ablation.is_attack(r):
                rows.append(r["module"])
    committed = [r["attack"] for r in
                 json.loads((ROOT / "evidence" / "ablation.json").read_text(encoding="utf-8"))]
    assert sorted(rows) == sorted(committed), (sorted(rows), sorted(committed))
