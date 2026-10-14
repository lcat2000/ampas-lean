#!/usr/bin/env python3
"""Which layer actually caught each attack.

A suite that rejects every attack proves less than it looks like: the
rejections could all come from one layer while the others do nothing. This
reads the driver's results and reports, per attack, the signals that fired —
so a rejection can be attributed, and a layer that never fires is visible.

    python3 harness/ablation.py evidence/corpus_results_threechecks.json \\
        [more results.json ...] --out evidence/ablation.json

Which submissions count as attacks is read from each record's own `expected`
field -- the manifest's declared outcome -- and NOT from the module's name.
The first version keyed on an `A` prefix, which is how the core corpus happens
to name its attacks; the history corpus (ROADMAP 6) names its submissions
after the mathematicians, so every one of its eight attacks fell out of the
table and the table said "0 attacks, all rejected: True". A derived label has
to be recomputable from the data beside it, which is the same lesson as the
`signals` rewrite below.
"""
import argparse
import json
import sys
from pathlib import Path


def signals(r: dict) -> list[str]:
    out = []
    if not r["compiled"]:
        out.append("compile")
    if r["compiled"] and not r["kernel_replay"]:
        out.append("primary kernel")
    if r["kernel_replay_independent"] is False:
        out.append("independent kernel")
    tc = r.get("third_check", {})
    if tc.get("run") and tc.get("errors"):
        out.append("third check")
    for c in r["claims"]:
        # Structured tags when the record has them. The substring matching
        # below is the fallback for records written before 2026-10-14, and it
        # is why this function needed replacing: rewording a reason without
        # changing its meaning dropped its layer from the table silently, so
        # an attack caught by the statement comparator appeared to be caught
        # by nothing. tests/test_record_consistency.py fails on that now.
        if c.get("signals"):
            out.extend(c["signals"])
            for f in c["flags"]:
                out.append(f.split(":", 1)[0])
            continue
        for reason in c["reasons"]:
            low = reason.lower()
            if "axioms outside the policy" in low:
                out.append("axiom-policy")
            elif "redefined or missing" in low or "outside the reference" in low:
                out.append("closure")          # the closure check over the statement
            elif "does not match the reference" in low:
                out.append("statement")        # the statement comparator
            elif "forbidden:" in low:
                pass                           # recorded via the flag itself
            elif "not a theorem" in low or "kind" in low:
                out.append("kind!=theorem")
            elif "guard" in low:
                out.append("guard")
            elif "review" in low or "attestation" in low:
                out.append("review")
            elif "does not declare" in low:
                out.append("theorem missing")
        for f in c["flags"]:
            out.append(f.split(":", 1)[0])     # the flag, not the constant it named
    seen, uniq = set(), []
    for s in out:
        if s not in seen:
            seen.add(s)
            uniq.append(s)
    return uniq


def is_attack(r: dict) -> bool:
    """A submission the manifest expects to be rejected.

    `expected` has been in every result record since round 1, so this needs no
    fallback to the naming convention -- and must not have one: a record
    without it is not evidence about any layer and is better left out of the
    table than guessed at from its name.
    """
    return r.get("expected") == "rejected"


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("results", nargs="+")
    ap.add_argument("--out")
    a = ap.parse_args(argv)
    rows = []
    for path in a.results:
        for r in json.loads(Path(path).read_text(encoding="utf-8"))["results"]:
            if not is_attack(r):
                continue
            certs = [c["certified"] for c in r["claims"]]
            rows.append({"attack": r["module"], "signals": signals(r),
                         "verdict": "REJECTED" if not (certs and all(certs))
                                    else "CERTIFIED (unexpected)"})
    rows.sort(key=lambda d: d["attack"])
    text = json.dumps(rows, indent=1, ensure_ascii=False) + "\n"
    if a.out:
        Path(a.out).write_text(text, encoding="utf-8", newline="\n")
    fired = sorted({s for r in rows for s in r["signals"]})
    print(text)
    print(f"{len(rows)} attacks, all rejected: "
          f"{all(r['verdict'] == 'REJECTED' for r in rows)}")
    print("layers that fired:", ", ".join(fired))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
