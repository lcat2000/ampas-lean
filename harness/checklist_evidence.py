#!/usr/bin/env python3
"""Per-item evidence for the fidelity checklist (ROADMAP 5.4).

`reference/attestations/*.json` carries a reviewer's six booleans:

    statement_matches_text, no_unintended_convention,
    quantifier_order_checked, hypotheses_necessary_and_satisfiable,
    definitions_reviewed, conclusion_not_weakened

All thirteen signed attestations answer all six `true`. Signed, hash-pinned,
drift-detected -- and **wholesale**: nothing in the record says which
quantifier order was checked, which definitions were read, or which
conventions were in play. A reviewer who thought hard and a reviewer who
ticked six boxes in four seconds leave byte-identical records, so the
checklist cannot distinguish them and neither can anyone reading it later.

This module derives, from the frozen statement itself, what each mechanisable
item is a claim ABOUT, and binds it to that statement's hash:

  statement_matches_text                 NO machine evidence. Marked so.
  no_unintended_convention               the convention-bearing constants the
                                         statement uses, and those one of this
                                         repository's definitions brings in
  quantifier_order_checked               the binder sequence, in order, split
                                         into data and hypotheses
  hypotheses_necessary_and_satisfiable   the hypothesis binders, cross-checked
                                         against the guards that are supposed
                                         to cover them
  definitions_reviewed                   the project's own definitions in the
                                         closure, each with its own hash
  conclusion_not_weakened                the conclusion, pretty and serialized

**This does not make a judgement correct.** Fidelity is a human reading, and
`statement_matches_text` has no machine evidence at all -- the whole gap
`docs/CONLECHE-EVALUATION.md` measured, where a kernel with a ZFC consistency
proof accepts `A06_wrong_statement` because the statement is well formed and
false to the text. What this makes is **carelessness visible**: a tick now
points at a named object, and `--check` re-derives the object and fails if
the statement it was derived from has changed.

Usage:
    python3 harness/checklist_evidence.py write    # derive and record
    python3 harness/checklist_evidence.py check    # re-derive and compare
    AMPAS_CLAIMS=reference/claims_mathlib.json ... # another catalogue
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))

import ampas_review as R                                      # noqa: E402

CONVENTIONS = Path(os.environ.get(
    "AMPAS_FIDELITY_CONVENTIONS", ROOT / "reference" / "fidelity_conventions.json"))

SCHEMA = "ampas-checklist-evidence/1"

# The one item nothing can derive. Kept as a named constant because the
# temptation is to find *something* mechanical to put beside it, and anything
# put there would be evidence for a different question than the one asked.
NO_MACHINE_EVIDENCE = "statement_matches_text"

WHY_NOT = (
    "Whether the Lean statement says what the natural-language text says is a "
    "comparison between a formal object and a sentence in English. No "
    "property of the formal object settles it: con-leche accepts "
    "A06_wrong_statement, and con-leche is a checker with a model-theoretic "
    "consistency proof. The material below is what the reviewer must read "
    "side by side; the verdict is theirs and is recorded nowhere else."
)


def sha256_str(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def conventions_file() -> dict:
    return json.loads(CONVENTIONS.read_text(encoding="utf-8"))


def evidence_path(cat: dict) -> Path:
    """Beside the attestations it is evidence for. Defined in ampas_review so
    the writer and the verifier cannot disagree about where it is."""
    return R.checklist_evidence_path(cat)


def derive_fidelity(cat: dict, conv: dict) -> dict:
    """Run the auditor's `fidelity` mode over every claim in the catalogue."""
    names = [c["theorem"] for c in cat["claims"]]
    out = R._audit({"mode": "fidelity",
                    "reference_module": cat["reference_module"],
                    "trusted_modules": cat["trusted_modules"],
                    "theorems": names,
                    "conventions": [e["const"] for e in conv["conventions"]]})
    return {t["name"]: t for t in out["fidelity"]}


def _notes_for(consts: list[str], conv: dict) -> list[dict]:
    by = {e["const"]: e["note"] for e in conv["conventions"]}
    return [{"const": c, "note": by[c]} for c in consts if c in by]


def _binder_rows(fid: dict) -> list[dict]:
    """The binder sequence as the evidence records it.

    `index` is the identity, not `name`: an anonymous binder
    (`∀ a b, b ≤ a → …`) has a machine-generated name and every one of them
    has the SAME machine-generated name, so citing a hypothesis by name would
    be ambiguous exactly where hypotheses matter. The auditor reports `null`
    for those rather than a name that does not distinguish them.
    """
    return [{"index": b["index"], "name": b["name"], "kind": b["kind"],
             "type": b["type"], "type_sha256": sha256_str(b["type_serialized"])}
            for b in fid["binders"]]


def item_evidence(c: dict, fid: dict, guards: dict, conv: dict) -> dict:
    """The six items, each pointing at the thing it is a claim about."""
    binders = _binder_rows(fid)
    hyps = [b for b in binders if b["kind"] == "hypothesis"]
    data = [b for b in binders if b["kind"] == "data"]

    present = _notes_for(fid["conventions_present"], conv)
    via = _notes_for(fid["conventions_via_definitions"], conv)
    known = {e["const"] for e in conv["conventions"]}
    unmatched = [k for k in fid["statement_constants"] if k not in known]

    # the guards the sanity pass computed, and whether they cover the
    # hypotheses this statement actually has
    nec = guards.get("necessity_status") or []
    refutation = guards.get("non_vacuity_status") == "REFUTATION"
    coverage = {
        "hypothesis_binders": len(hyps),
        "guards_hypotheses": guards.get("hypotheses", 0),
        "necessity_guards": len(nec),
        "necessity_status": nec,
        "non_vacuity_status": guards.get("non_vacuity_status"),
    }
    if refutation:
        # The two records disagree ON PURPOSE and the disagreement is recorded
        # rather than resolved by picking one. `¬ P` is `P → False`, so the
        # telescope sees one binder while the sanity pass reports zero
        # hypotheses: for a refutation the antecedent is the statement being
        # REFUTED, not a hypothesis whose necessity has to be shown. Both
        # numbers are above; without this note a reader comparing them finds
        # an unexplained mismatch, which is how the A01 mislabel survived nine
        # rounds.
        coverage["reconciliation"] = (
            "refutation: the single antecedent is the refuted statement, not a "
            "hypothesis, so the guards report 0 where the binder telescope "
            "reports 1. A nontriviality lemma stands in for the witness and "
            "necessity guards.")
        coverage["nontriviality"] = guards.get("nontriviality")
        coverage["consistent"] = len(hyps) <= 1 and len(nec) == 0
    else:
        coverage["consistent"] = (
            len(hyps) == guards.get("hypotheses", 0) == len(nec))
    if not coverage["consistent"]:
        coverage["inconsistency"] = (
            "a tick on this item covers fewer hypotheses than the statement "
            "has: see hypothesis_binders against necessity_guards")

    return {
        NO_MACHINE_EVIDENCE: {
            "machine_derivable": False,
            "why_not": WHY_NOT,
            "material_to_read": {
                "claim_text": c["text"],
                "conclusion": fid["conclusion"],
                "binders": binders,
            },
        },
        "no_unintended_convention": {
            "machine_derivable": True,
            "in_the_statement": present,
            "via_this_repositorys_definitions": via,
            "unmatched_statement_constants": unmatched,
            "conventions_list": {
                "path": str(CONVENTIONS.relative_to(ROOT)).replace(os.sep, "/"),
                "last_reviewed": conv["last_reviewed"],
                "rules": len(conv["conventions"]),
            },
            "limit": (
                "An empty `in_the_statement` means no constant on that list "
                "appears, NOT that the statement has no convention trap. "
                "`unmatched_statement_constants` is what the list has no rule "
                "for; the list's own not_covered section names the known gaps."
            ),
        },
        "quantifier_order_checked": {
            "machine_derivable": True,
            "binder_sequence": binders,
            "data_binders": len(data),
            "hypothesis_binders": len(hyps),
            # the order itself, hashed: a permutation of the binders changes
            # this even when every individual type is unchanged
            "order_sha256": sha256_str(
                "\n".join(f"{b['index']}\t{b['kind']}\t{b['type_sha256']}" for b in binders)),
        },
        "hypotheses_necessary_and_satisfiable": {
            "machine_derivable": True,
            "hypotheses": hyps,
            "guard_coverage": coverage,
        },
        "definitions_reviewed": {
            "machine_derivable": True,
            "project_definitions": [
                {"name": d["name"], "kind": d["kind"], "module": d["module"],
                 "type": d["type"],
                 "sha256": sha256_str(f"{d['kind']}\t{d['type']}\t{d['value'] or ''}")}
                for d in fid["project_definitions"]],
            "count": len(fid["project_definitions"]),
            "limit": (
                "Lean's own definitions are excluded: a reviewer is not "
                "expected to have read Init. A statement with none of its own "
                "definitions rests entirely on Lean's, which is informative "
                "rather than missing -- and note that `AmpasRef.Defs` is NOT "
                "excluded even though the provenance layer trusts it, because "
                "a wrong `Ampas.IsEven` is the canonical fidelity failure and "
                "it lives there."
            ),
        },
        "conclusion_not_weakened": {
            "machine_derivable": True,
            "conclusion": fid["conclusion"],
            "conclusion_serialized": fid["conclusion_serialized"],
            "conclusion_sha256": sha256_str(fid["conclusion_serialized"]),
        },
    }


def build(cat: dict) -> dict:
    conv = conventions_file()
    fid = derive_fidelity(cat, conv)
    derived = R.derive(cat)
    claims = {}
    for c in cat["claims"]:
        f = fid.get(c["theorem"])
        if f is None or "error" in f:
            raise SystemExit(f"{c['id']}: fidelity mode found no {c['theorem']}")
        d = derived[c["id"]]
        claims[c["id"]] = {
            "claim": c["id"],
            "theorem": c["theorem"],
            # The evidence is ABOUT one exact statement. If the statement
            # changes, this hash changes and `check` fails: evidence for a
            # statement that no longer exists is not evidence.
            "statement_sha256": d["statement_sha256"],
            "items": item_evidence(c, f, d["guards"], conv),
        }
    incons = sorted(k for k, v in claims.items()
                    if not v["items"]["hypotheses_necessary_and_satisfiable"]
                    ["guard_coverage"]["consistent"])
    return {
        "schema": SCHEMA,
        "generated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "catalogue": str(R.CATALOGUE.relative_to(ROOT)).replace(os.sep, "/"),
        "reference_module": cat["reference_module"],
        "what_this_is": [
            "Per-item evidence for the fidelity checklist in the attestations",
            "beside this file (ROADMAP 5.4). Each of the six checklist items",
            "points at the object it is a claim about, derived from the frozen",
            "statement and bound to its hash.",
            "",
            "It does not decide fidelity. `statement_matches_text` has no",
            "machine evidence and says so: a kernel cannot compare a formal",
            "object to an English sentence, which is what",
            "docs/CONLECHE-EVALUATION.md measured when a checker carrying a",
            "ZFC consistency proof accepted A06_wrong_statement.",
            "",
            "What it does is make a careless tick distinguishable from a",
            "careful one, and make the distinction survive into the record.",
        ],
        "items_with_no_machine_evidence": [NO_MACHINE_EVIDENCE],
        "conventions_list_last_reviewed": conv["last_reviewed"],
        "claims": claims,
        "totals": {
            "claims": len(claims),
            "items_per_claim": len(R.CHECKLIST),
            "machine_derivable_items": len(R.CHECKLIST) - 1,
            "guard_coverage_inconsistent": incons,
        },
    }


def _comparable(rec: dict) -> dict:
    """Everything but the timestamp: `generated` changes on every run and is
    not what `check` is about."""
    return {k: v for k, v in rec.items() if k != "generated"}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("action", choices=["write", "check", "show"])
    a = ap.parse_args(argv)
    cat = R.catalogue()
    path = evidence_path(cat)

    if a.action == "write":
        rec = build(cat)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(rec, indent=2, ensure_ascii=False) + "\n",
                        encoding="utf-8", newline="\n")
        print(f"wrote {path.relative_to(ROOT)}: {rec['totals']['claims']} claims, "
              f"{rec['totals']['machine_derivable_items']} of "
              f"{rec['totals']['items_per_claim']} items with machine evidence")
        if rec["totals"]["guard_coverage_inconsistent"]:
            print("GUARD COVERAGE INCONSISTENT: "
                  + ", ".join(rec["totals"]["guard_coverage_inconsistent"]))
            return 1
        return 0

    if not path.exists():
        print(f"no evidence recorded at {path.relative_to(ROOT)}; run `write`")
        return 1
    stored = json.loads(path.read_text(encoding="utf-8"))

    if a.action == "show":
        for cid, c in stored["claims"].items():
            it = c["items"]
            print(f"{cid:14s} {len(it['quantifier_order_checked']['binder_sequence'])} binders, "
                  f"{len(it['hypotheses_necessary_and_satisfiable']['hypotheses'])} hyp, "
                  f"{len(it['no_unintended_convention']['in_the_statement'])} conventions, "
                  f"{it['definitions_reviewed']['count']} defs")
        return 0

    fresh = build(cat)
    if _comparable(fresh) == _comparable(stored):
        print(f"{path.relative_to(ROOT)}: reproduces ({fresh['totals']['claims']} claims)")
        return 0
    bad = 0
    for cid, f in fresh["claims"].items():
        s = stored["claims"].get(cid)
        if s is None:
            print(f"{cid}: not in the record"); bad += 1; continue
        if f["statement_sha256"] != s["statement_sha256"]:
            print(f"{cid}: STATEMENT CHANGED since the evidence was derived "
                  f"({s['statement_sha256'][:12]} -> {f['statement_sha256'][:12]})")
            bad += 1
        for k in R.CHECKLIST:
            if f["items"][k] != s["items"][k]:
                print(f"{cid}: evidence for `{k}` differs"); bad += 1
    for cid in stored["claims"]:
        if cid not in fresh["claims"]:
            print(f"{cid}: in the record but not in the catalogue"); bad += 1
    if not bad:
        print("claims agree; the record differs in a field outside them")
        bad = 1
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
