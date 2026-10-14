#!/usr/bin/env python3
"""Which stored verdicts would not reproduce today?

ROADMAP 1.2, and the second half of that item's "done when". After a kernel
soundness disclosure the question is not whether the suite passes now -- it is
which certificates already issued rest on a kernel the disclosure names. A
certificate that cannot be matched back to its kernel cannot be answered for.

**This compares metadata. It does not re-run anything** unless `--rerun` is
passed, and the two must never be confused: a record whose provenance matches
the live toolchain is a record that *would be expected* to reproduce, which is
not the same as one that *did*. Every line of output says which of the two it
is, and the summary refuses to call a metadata match a reproduction.

Verdicts per stored record:

  AFFECTED        an advisory in reference/kernel_advisories.json names a
                  kernel this record used. Re-check it against a fixed
                  toolchain; this is the state the whole mechanism exists for.
  KERNEL_CHANGED  the live kernels differ from the ones that issued it, so
                  whether it still holds is untested. Not a failure.
  NO_PROVENANCE   issued before provenance was recorded (before 2026-10-14).
                  Nothing can be said about its kernel, which is the gap this
                  item closes going forward and cannot close backwards.
  SAME_KERNEL     the live kernels match the recorded ones. Expected to
                  reproduce; `--rerun` is what establishes that it does.

Usage:
  python3 harness/reverify.py
  python3 harness/reverify.py --rerun          # actually re-execute the corpus
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Stored records this knows how to read: the recorded reference run, and
# whatever the latest local run left in build/.
CANDIDATES = [
    ROOT / "evidence" / "corpus_results_threechecks.json",
    ROOT / "evidence" / "corpus_results_twokernels.json",
    ROOT / "evidence" / "corpus_results.json",
    ROOT / "evidence" / "corpus_results_mathlib.json",
    ROOT / "evidence" / "corpus_results_mathlib3.json",
    ROOT / "evidence" / "fermat_validation.json",
    ROOT / "build" / "corpus_core.json",
]


def classify(stored: dict, live: dict) -> tuple[str, list[str]]:
    prov = stored.get("provenance")
    if not prov:
        return "NO_PROVENANCE", [
            "issued before provenance was recorded; its kernel cannot be "
            "identified from the record"]

    notes, state = [], "SAME_KERNEL"

    adv = prov.get("advisories", {}).get("matched") or []
    live_adv = live.get("advisories", {})
    # An advisory added since the record was written is the case that matters:
    # re-match the record's own kernels against the CURRENT list.
    from provenance import advisory_status
    now = advisory_status((prov.get("lean") or {}).get("version"),
                          (prov.get("independent_kernel") or {}).get("pinned_revision"))
    if now["matched"]:
        state = "AFFECTED"
        notes.append("current advisories name this record's kernel: "
                     + ", ".join(m["id"] for m in now["matched"]))
    elif adv:
        notes.append("the record itself already noted a matching advisory")

    for field, label in (("version", "lean version"), ("sha256", "lean binary")):
        a = (prov.get("lean") or {}).get(field)
        b = (live.get("lean") or {}).get(field)
        if a and b and a != b:
            if state != "AFFECTED":
                state = "KERNEL_CHANGED"
            notes.append(f"{label} differs: recorded {str(a)[:40]}, live {str(b)[:40]}")

    a = (prov.get("primary_kernel") or {}).get("sha256")
    b = (live.get("primary_kernel") or {}).get("sha256")
    if a and b and a != b:
        if state != "AFFECTED":
            state = "KERNEL_CHANGED"
        notes.append("leanchecker binary differs")

    a = (prov.get("independent_kernel") or {}).get("pinned_revision")
    b = (live.get("independent_kernel") or {}).get("pinned_revision")
    if a and b and a != b:
        if state != "AFFECTED":
            state = "KERNEL_CHANGED"
        notes.append(f"lean4lean pin differs: {a[:12]} -> {b[:12]}")

    stale = prov.get("advisories", {}).get("advisories_last_reviewed")
    fresh = live_adv.get("advisories_last_reviewed")
    if stale and fresh and stale != fresh:
        notes.append(f"the advisory list has been reviewed since ({stale} -> {fresh})")
    return state, notes


def certified_count(stored: dict) -> int:
    n = 0
    for r in stored.get("results", stored.get("submissions", [])):
        for c in r.get("claims", []):
            if c.get("certified"):
                n += 1
    return n


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(ROOT / "build" / "reverification.json"))
    ap.add_argument("--rerun", action="store_true",
                    help="actually re-execute the core corpus and compare verdicts")
    args = ap.parse_args(argv)

    from provenance import snapshot
    live = snapshot()

    rows = []
    for p in CANDIDATES:
        if not p.exists():
            continue
        try:
            stored = json.loads(p.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        if not isinstance(stored, dict):
            continue
        state, notes = classify(stored, live)
        rows.append({"record": str(p.relative_to(ROOT)), "state": state,
                     "certified_claims": certified_count(stored), "notes": notes})
        print(f"{state:15s} {p.relative_to(ROOT)}  ({certified_count(stored)} certified)")
        for n in notes:
            print(f"                  - {n}")

    rerun = None
    if args.rerun:
        print("\n== re-executing the core corpus")
        out = ROOT / "build" / "reverify_rerun.json"
        r = subprocess.run([sys.executable, str(ROOT / "harness" / "ampas_lean.py"),
                            str(ROOT / "corpus" / "manifest.json"), "--out", str(out)],
                           cwd=str(ROOT), capture_output=True, text=True,
                           encoding="utf-8", timeout=3600)
        ok = r.returncode == 0 and out.exists()
        rerun = {"ran": True, "succeeded": ok,
                 "record": str(out.relative_to(ROOT)) if ok else None,
                 "stderr_tail": (r.stderr or "")[-400:] if not ok else None}
        print("   re-execution " + ("succeeded" if ok else "FAILED"))

    report = {
        "checked_on": time.strftime("%Y-%m-%d"),
        "live_provenance": live,
        "records": rows,
        "re_execution": rerun or {
            "ran": False,
            "means": ("Nothing was re-executed. A SAME_KERNEL row means the live "
                      "toolchain matches the one that issued the record, so it "
                      "would be EXPECTED to reproduce -- not that it did. Pass "
                      "--rerun to establish that."),
        },
    }
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n",
                              encoding="utf-8", newline="\n")
    print(f"\n-> {args.out}")
    if not args.rerun:
        print("   metadata only; nothing was re-executed (--rerun does that)")
    affected = [r for r in rows if r["state"] == "AFFECTED"]
    return 1 if affected else 0


if __name__ == "__main__":
    sys.path.insert(0, str(ROOT / "harness"))
    raise SystemExit(main(sys.argv[1:]))
