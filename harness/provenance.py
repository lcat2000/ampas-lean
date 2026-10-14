#!/usr/bin/env python3
"""What checked this, and what was known about it at the time.

ROADMAP 1.1. A certificate that does not name the kernel that issued it cannot
be found again after a soundness disclosure, and the repository's strongest
claim -- that two independently written kernels agreed -- is precisely the one
external evidence has weakened (Tao, 2026-10-09: an independent kernel also
accepted an illicit proof, through a bug of its own). So the interesting
question about a stored verdict is not only "did it pass" but "which binaries
said so, and what was known about them that day".

Three things are recorded, and the third is the one to read carefully:

  * **Identity.** Version strings and SHA-256 of the actual binaries, plus the
    pinned revisions for lean4lean and Mathlib. These are facts.
  * **The toolchain pin**, so a record made with an unpinned toolchain is
    visibly that.
  * **Advisory status**, from `reference/kernel_advisories.json`. This is NOT
    a bug-free certificate and the field names avoid implying one. What a
    record can honestly say is "no advisory in this list, as of the date the
    list was last reviewed, names this kernel" -- and that is worth exactly
    as much as the list's maintenance, which is why `advisories_last_reviewed`
    travels with every record that cites it.

`evidence/environment.json` has recorded much of the identity half by hand
since round 1, for the run as a whole. This produces it per run, mechanically,
so it cannot drift from what actually ran -- and `harness/reverify.py`
compares a stored record against the live toolchain.
"""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ADVISORIES = ROOT / "reference" / "kernel_advisories.json"


def _sha256(p: Path) -> str | None:
    try:
        return hashlib.sha256(p.read_bytes()).hexdigest()
    except OSError:
        return None


def _version(binary: Path) -> str | None:
    try:
        r = subprocess.run([str(binary), "--version"], capture_output=True,
                           text=True, encoding="utf-8", timeout=60)
        return r.stdout.strip() or r.stderr.strip() or None
    except (OSError, subprocess.SubprocessError):
        return None


def advisory_status(lean_version: str | None,
                    lean4lean_revision: str | None) -> dict:
    """What the committed advisory list says about these kernels.

    The shape of this answer matters more than its content. "no advisory
    matched" is not "no known bugs": it is a statement about one list, on one
    date, and the date travels with it. A reader who wants the stronger claim
    has to go to the upstream advisories, and the record says so.
    """
    if not ADVISORIES.exists():
        return {"list": "missing", "matched": [],
                "means": "no advisory list is committed, so nothing was checked"}
    adv = json.loads(ADVISORIES.read_text(encoding="utf-8"))
    matched = []
    for a in adv.get("advisories", []):
        hits = []
        aff = a.get("affected", {})
        vers = aff.get("lean_versions")
        if vers and lean_version:
            if any(v in lean_version for v in vers):
                hits.append(f"lean version matches {vers}")
        revs = aff.get("lean4lean_revisions")
        if revs and lean4lean_revision and lean4lean_revision in revs:
            hits.append("lean4lean revision matches")
        if hits:
            matched.append({"id": a["id"], "why": hits})
    return {
        "list": str(ADVISORIES.relative_to(ROOT)),
        "list_sha256": _sha256(ADVISORIES),
        "advisories_last_reviewed": adv.get("last_reviewed"),
        "advisory_count": len(adv.get("advisories", [])),
        "matched": matched,
        "means": (
            "No advisory in this list names these kernels, as of "
            f"{adv.get('last_reviewed')}. That is a statement about this list "
            "on that date, NOT that the kernels have no known soundness bugs. "
            "The list's own caveats are in the file."
            if not matched else
            "An advisory in this list names a kernel used here; see `matched`."),
    }


def snapshot(extra: dict | None = None) -> dict:
    """The provenance block to attach to a verdict record."""
    from ampas_lean import lean_exe, usable_binary, TRUSTED_OLEAN, AUDIT_BIN

    out: dict = {"recorded_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}

    try:
        lean = lean_exe("lean")
        out["lean"] = {"path_name": lean.name, "version": _version(lean),
                       "sha256": _sha256(lean)}
    except SystemExit:
        out["lean"] = {"error": "no lean binary found"}
    try:
        lc = lean_exe("leanchecker")
        out["primary_kernel"] = {"tool": "leanchecker (ships with Lean)",
                                 "sha256": _sha256(lc)}
    except SystemExit:
        out["primary_kernel"] = {"error": "no leanchecker binary found"}

    # the independent kernel is optional: tier 2 and up
    l4l = os.environ.get("AMPAS_LEAN4LEAN", "")
    pin = ROOT / "reference" / "lean4lean_pin.json"
    ind: dict = {"present": bool(l4l)}
    if l4l:
        ind["sha256"] = _sha256(Path(l4l))
    if pin.exists():
        p = json.loads(pin.read_text(encoding="utf-8"))
        ind["pinned_revision"] = p.get("revision")
        ind["declared_toolchain"] = p.get("declared_toolchain")
        # `built_with` is the toolchain discrepancy (the repo declares an rc,
        # this suite pins the release); `note` is about the kernel's deliberate
        # divergences from the C++ kernel. Two different facts, and an earlier
        # draft here put the second under the first's name.
        ind["built_with"] = p.get("built_with")
        ind["divergences_note"] = p.get("note")
        ind["binary_sha256_reference_run"] = p.get("binary_sha256_reference_run")
    out["independent_kernel"] = ind

    tc = ROOT / "lean-toolchain"
    out["toolchain_pin"] = tc.read_text(encoding="utf-8").strip() if tc.exists() else None
    out["trusted_olean_dir"] = str(TRUSTED_OLEAN)
    out["auditor"] = ("compiled binary" if usable_binary(AUDIT_BIN)
                      else "interpreted from harness/Audit.lean")

    mpin = ROOT / "reference" / "mathlib_pin.json"
    if mpin.exists():
        m = json.loads(mpin.read_text(encoding="utf-8"))
        out["mathlib"] = {"revision": m.get("revision"),
                          "built_from_source": m.get("built_from_source")}

    out["advisories"] = advisory_status(
        (out.get("lean") or {}).get("version"), ind.get("pinned_revision"))
    if extra:
        out.update(extra)
    return out


if __name__ == "__main__":
    import sys
    sys.path.insert(0, str(ROOT / "harness"))
    print(json.dumps(snapshot(), indent=2, ensure_ascii=False))
