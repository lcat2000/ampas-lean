#!/usr/bin/env python3
"""AMPAS math-verification: the formalization-correctness review process.

"Did the Lean statement faithfully render the natural-language claim?" is not
a question the kernel can answer. This tool makes the answer an auditable
artifact instead of an opinion in a comment:

  freeze   For each claim, record what was reviewed, by content:
             * statement_sha256 - SHA-256 of a structural serialization of
               the ELABORATED reference statement (not its source text), so
               reformatting is invisible and any change of meaning is not;
             * closure_sha256 - SHA-256 of the serialization of every
               constant the statement rests on, transitively, INCLUDING
               definition bodies, so redefining `IsEven` changes the freeze
               even though the statement text is untouched;
             * the machine-checked guards (non-vacuity of the hypotheses,
               necessity of each one) and their verification status, as the
               auditor computed the required types and checked them;
             * the reviewer's identity, date and checklist answers.
  sign     Detached Ed25519 signature over the canonical record, so the
           attestation is attributable to a key, not merely to a name typed
           in a file.
  verify   Re-derive everything from the current reference and compare:
           signature, statement hash, closure hash (naming which constant
           drifted), and guard status. Any difference fails. This is the
           drift detector: a reference statement cannot change, and nothing
           it depends on can change, without invalidating the sign-off.

A frozen, signed, guard-backed statement is still only a statement a human
judged faithful. The point is that the judgement is pinned to an exact
mathematical object and cannot drift silently afterwards.
"""
from __future__ import annotations

import argparse
import json
import hashlib
import os
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
def _lean_root() -> Path:
    """Where the Lean toolchain lives.

    LEAN_ROOT wins; otherwise ask Lean itself (`lean --print-prefix`), which
    works for an elan-managed toolchain as well as an unpacked one; otherwise
    fall back to the parent of whatever `lean` is on PATH. No path in this
    file is specific to the machine the suite was developed on.
    """
    env = os.environ.get("LEAN_ROOT")
    if env:
        return Path(env)
    try:
        out = subprocess.run(["lean", "--print-prefix"], capture_output=True,
                             text=True, encoding="utf-8", timeout=60)
        if out.returncode == 0 and out.stdout.strip():
            return Path(out.stdout.strip())
    except (OSError, subprocess.SubprocessError):
        pass
    found = shutil.which("lean")
    if found:
        return Path(found).resolve().parent.parent
    # Deliberately NOT fatal here. Tier 0 of the verification runs with no
    # Lean at all, and it imports this module; raising at import time would
    # make the no-Lean tier impossible. Anything that actually needs Lean
    # calls require_lean() first.
    return None


LEAN_ROOT = _lean_root() or Path("/nonexistent-lean-toolchain")
LEAN_FOUND = _lean_root() is not None


def require_lean() -> None:
    """Fail with something actionable, at the point Lean is actually needed."""
    if not LEAN_FOUND:
        raise SystemExit(
            "Lean not found: put `lean` on PATH or set LEAN_ROOT. "
            "See INSTALL.md; ./scripts/bootstrap.sh installs the pinned "
            "toolchain. (Tier 0 of the verification needs no Lean: "
            "python3 -m pytest tests/test_third_check.py -q -k 'not pipeline')")
AUDIT_BIN = Path(os.environ.get("AMPAS_AUDIT_BIN", HERE / "audit"))



def lean_exe(name: str) -> Path:
    """The toolchain's `name` binary, with the platform's extension.

    On Windows these are `lean.exe` and `leanchecker.exe`. Building the path
    without the suffix is not merely untidy: it produced

        OSError: [WinError 193] %1 is not a valid Win32 application

    from inside subprocess, which tells a reader nothing about what was
    wrong. So the probe is explicit, and when it fails it names what it
    looked for.
    """
    require_lean()
    base = _lean_root() / "bin" / name
    candidates = [base.with_name(base.name + ".exe"), base] if os.name == "nt" else [base]
    for c in candidates:
        if c.is_file():
            return c
    raise SystemExit(
        f"no Lean `{name}` binary under {base.parent}. Looked for: "
        + ", ".join(c.name for c in candidates)
        + ". Set LEAN_ROOT to the toolchain prefix (`lean --print-prefix`).")


def _usable_binary(p: Path) -> bool:
    """`os.access(X_OK)` is true for ANY existing file on Windows, so it
    cannot tell a native executable from the Linux ELF that a previous build
    on another machine may have left behind. Require the extension there."""
    if not p.is_file():
        return False
    if os.name == "nt":
        return p.suffix.lower() in (".exe", ".bat", ".cmd")
    return os.access(p, os.X_OK)


def audit_cmd() -> list[str]:
    """The compiled auditor if present AND NOT STALE, otherwise `lean --run`
    on its source (slower, but needs no C toolchain). See
    harness/ampas_lean.py, whose copy of this rule must agree."""
    if _usable_binary(AUDIT_BIN) and not audit_binary_is_stale():
        return [str(AUDIT_BIN)]
    require_lean()
    return [str(lean_exe("lean")), "--run", str(HERE / "Audit.lean")]


def audit_binary_is_stale() -> bool:
    """Is the compiled auditor older than its source?

    This used to go unasked, and the binary simply won. Edit Audit.lean,
    re-run, and the code that executes is the code from before the edit --
    with nothing in the output saying so. Found while adding the `fidelity`
    mode: the new mode fell through to `audit` and failed with
    "solution_module: String expected", which is the HARMLESS version. The
    harmful version is a mode that exists in both builds and changed
    behaviour, where a stale binary returns a plausible wrong answer. (It
    nearly happened: the first `fidelity` implementation rendered
    `∀ n, ∃ m, n < m` as `∃ m, m < m`, and a stale binary would have kept
    emitting that after the fix.)

    Erring toward the source is the safe direction: interpreting is slower and
    always current, and `audit_fingerprint_path()` hashes whichever one runs,
    so the provenance record follows this decision rather than contradicting
    it.
    """
    src = HERE / "Audit.lean"
    if not src.is_file():
        return False
    return AUDIT_BIN.stat().st_mtime < src.stat().st_mtime

TRUSTED_OLEAN = Path(os.environ.get("AMPAS_TRUSTED_OLEAN", ROOT / "build"))
ATTEST_DIR = ROOT / "reference" / "attestations"
# the module that imports both the frozen statements and the guards
REVIEW_MODULE = "AmpasRef.Guards"
# which catalogue to freeze (a second one covers the Mathlib-backed claims)
CATALOGUE = Path(os.environ.get("AMPAS_CLAIMS", ROOT / "reference" / "claims.json"))

CHECKLIST = [
    "statement_matches_text",          # the Lean statement says what the text says
    "no_unintended_convention",        # Nat truncation, x/0, coercions checked
    "quantifier_order_checked",
    "hypotheses_necessary_and_satisfiable",   # backed by the guards below
    "definitions_reviewed",            # every definition in the closure read
    "conclusion_not_weakened",
]


def sha256_str(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def _audit(request: dict) -> dict:
    req = ROOT / ".review_req.json"
    req.write_text(json.dumps(request), encoding="utf-8", newline="\n")
    env = dict(os.environ)
    env["PATH"] = f"{LEAN_ROOT / 'bin'}:{env.get('PATH','')}"
    # AMPAS_EXTRA_LEAN_PATH after the trusted directory, never before it: at
    # tier 3 the trusted directory is the merged one holding every AmpasRef
    # module, and the extra entries carry Mathlib. Without them the auditor
    # cannot even load a Mathlib-backed reference, which is why the freeze and
    # the sign-off verification used to be reachable only for the core
    # catalogue.
    extra = os.environ.get("AMPAS_EXTRA_LEAN_PATH", "")
    env["LEAN_PATH"] = os.pathsep.join(
        [str(TRUSTED_OLEAN)] + ([extra] if extra else []))
    try:
        r = subprocess.run(audit_cmd() + [str(req)], capture_output=True, text=True, encoding="utf-8",
                           env=env, timeout=600)
        if r.returncode != 0:
            raise SystemExit(f"auditor failed: {r.stdout}\n{r.stderr}")
        return json.loads(r.stdout.strip().splitlines()[-1])
    finally:
        req.unlink(missing_ok=True)


def catalogue() -> dict:
    return json.loads(CATALOGUE.read_text(encoding="utf-8"))


def review_module(cat: dict) -> str:
    """The module the sanity pass loads: it must contain the frozen
    statements and, when the catalogue has guards, the guard theorems."""
    return cat.get("guards_module", cat["reference_module"])


def attest_dir(cat: dict) -> Path:
    sub = cat.get("attestation_dir")
    return (ROOT / sub) if sub else ATTEST_DIR


def checklist_evidence_path(cat: dict) -> Path:
    """Where the per-item checklist evidence lives: beside the attestations it
    is evidence for, so a catalogue with its own attestation directory gets
    its own evidence file. harness/checklist_evidence.py writes it and this
    module reads it; the path is defined here so the writer and the verifier
    cannot disagree about where it is (and so importing one does not require
    importing the other)."""
    ad = attest_dir(cat)
    return ad.parent / (ad.name.replace("attestations", "checklist-evidence") + ".json")


def checklist_evidence_for(cat: dict, cid: str) -> dict | None:
    p = checklist_evidence_path(cat)
    if not p.is_file():
        return None
    return json.loads(p.read_text(encoding="utf-8"))["claims"].get(cid)


def evidence_informed_the_tick(cat: dict, cid: str, rec: dict) -> bool | None:
    """Could the reviewer have SEEN the per-item evidence when they ticked?

    The evidence is derived, so it can be produced for an attestation signed
    long before it existed -- and then it reads as backing for a judgement it
    had no part in. All thirteen signed attestations are in exactly that
    position: ROADMAP 5.4 was written after them. The answer is recomputable
    from the two dates sitting beside each other, which is the rule this
    repository holds for every derived label, so it is reported rather than
    asserted either way.
    """
    p = checklist_evidence_path(cat)
    if not p.is_file():
        return None
    gen = json.loads(p.read_text(encoding="utf-8")).get("generated")
    signed = (rec.get("signature") or {}).get("signed_at")
    if not gen or not signed:
        return None
    return gen <= signed


def guard_spec(cat: dict) -> dict:
    """Which guard theorems a claim offers, from claims.json."""
    return {c["id"]: c.get("guards", {}) for c in cat["claims"]}


def derive(cat: dict) -> dict:
    """Recompute, from the current reference, everything an attestation pins."""
    claims = cat["claims"]
    names = [c["theorem"] for c in claims]
    fz = _audit({"mode": "freeze", "reference_module": cat["reference_module"],
                 "trusted_modules": cat["trusted_modules"], "theorems": names})
    sanity_items = []
    for c in claims:
        g = c.get("guards", {})
        item = {"name": c["theorem"]}
        if g.get("witness"):
            item["witness"] = g["witness"]
        if g.get("necessity"):
            item["necessity"] = g["necessity"]
        elif g.get("nontriviality"):
            # a refutation claim: cite the nontriviality lemma (recorded, and
            # kernel-checked as part of the reference, but its relevance is a
            # reviewer judgement rather than a computed type)
            item["necessity"] = [g["nontriviality"]]
        sanity_items.append(item)
    sn = _audit({"mode": "sanity", "reference_module": review_module(cat),
                 "trusted_modules": cat["trusted_modules"], "theorems": sanity_items})
    fz_by = {t["name"]: t for t in fz["freeze"]}
    sn_by = {t["name"]: t for t in sn["sanity"]}
    out = {}
    for c in claims:
        t = fz_by.get(c["theorem"], {})
        s = sn_by.get(c["theorem"], {})
        if "error" in t:
            raise SystemExit(f"{c['id']}: reference theorem missing: {c['theorem']}")
        closure_canon = "\n".join(
            f"{e['name']}\t{e.get('module','')}\t{e['decl']}" for e in t["closure"])
        out[c["id"]] = {
            "claim": c["id"],
            "theorem": c["theorem"],
            "text": c["text"],
            "control": c.get("control"),
            "kind": t["kind"],
            "level_params": t["level_params"],
            "statement_sha256": sha256_str(t["statement"]),
            "closure_sha256": sha256_str(closure_canon),
            "closure_size": len(t["closure"]),
            # per-constant hashes, so drift names the constant that changed
            "closure_entries": {e["name"]: sha256_str(e["decl"]) for e in t["closure"]},
            "policy": c["policy"],
            "guards": {
                "hypotheses": s.get("hypotheses", 0),
                "witness": c.get("guards", {}).get("witness"),
                "necessity": c.get("guards", {}).get("necessity", []),
                "nontriviality": c.get("guards", {}).get("nontriviality"),
                "non_vacuity_status": s.get("non_vacuity"),
                "necessity_status": s.get("necessity", []),
                "expected_witness": s.get("expected_witness", ""),
                "expected_necessity": s.get("expected_necessity", []),
            },
        }
    return out


def guards_ok(d: dict) -> tuple[bool, list[str]]:
    g = d["guards"]
    problems = []
    if g.get("non_vacuity_status") == "REFUTATION":
        # the conclusion is False: the witness and necessity guards do not
        # apply. A nontriviality lemma must be cited instead.
        if not g.get("nontriviality"):
            problems.append("refutation claim cites no nontriviality guard")
        return (not problems), problems
    if g["hypotheses"] > 0:
        if g["non_vacuity_status"] != "OK":
            problems.append(f"non-vacuity guard {g['non_vacuity_status']}")
        for i, st in enumerate(g["necessity_status"]):
            if st not in ("OK", "DEPENDENT"):
                problems.append(f"necessity guard {i} {st}")
    else:
        if g["non_vacuity_status"] not in ("NO_HYPOTHESES", None):
            problems.append(f"unexpected non-vacuity status {g['non_vacuity_status']}")
    return (not problems), problems


def canonical(record: dict) -> bytes:
    """What the signature covers: the record without its signature block."""
    body = {k: v for k, v in record.items() if k != "signature"}
    return json.dumps(body, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False).encode("utf-8")


# ---- signing
def load_private(path: Path):
    from cryptography.hazmat.primitives import serialization
    return serialization.load_pem_private_key(path.read_bytes(), password=None)


def load_public(pem: str):
    from cryptography.hazmat.primitives import serialization
    return serialization.load_pem_public_key(pem.encode())


def keygen(priv_path: Path, pub_path: Path, key_id: str, custody: str | None = None):
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
    from cryptography.hazmat.primitives import serialization
    k = Ed25519PrivateKey.generate()
    priv_path.write_bytes(k.private_bytes(
        serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8,
        serialization.NoEncryption()))
    os.chmod(priv_path, 0o600)
    pub_pem = k.public_key().public_bytes(
        serialization.Encoding.PEM, serialization.PublicFormat.SubjectPublicKeyInfo).decode()
    # Who holds the private key is the whole value of a signature, and it is
    # not derivable from the key material -- so it is recorded here, in the
    # public record, at the moment the key is made. A key generated in a
    # build container and held by nobody authenticates a record's integrity
    # and attributes NOTHING to a person; one held by a named reviewer binds
    # the sign-off to them. The difference must not be left for a reader to
    # guess from the key id.
    rec = {"key_id": key_id, "algorithm": "Ed25519", "public_key_pem": pub_pem}
    rec["custody"] = custody or (
        "UNDECLARED — no custody was stated when this key was generated. Treat "
        "the signature as attesting record integrity only, and as attributing "
        "nothing to any person, until this field says who holds the private key.")
    pub_path.write_text(json.dumps(rec, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
    print(f"private key -> {priv_path} (keep out of the package; never commit it)")
    print(f"public key  -> {pub_path}")
    print(f"custody     -> {rec['custody'][:72]}...")


def cex_path(cat: dict) -> Path:
    """Where this catalogue's committed counterexample-search record lives."""
    sub = cat.get("counterexample_search")
    if sub:
        return ROOT / sub
    stem = CATALOGUE.stem.replace("claims", "counterexample_search")
    return ROOT / "reference" / f"{stem}.json"


def cex_records(cat: dict) -> dict:
    p = cex_path(cat)
    if not p.exists():
        return {}
    return {r["claim"]: r for r in json.loads(p.read_text(encoding="utf-8")).get("searches", [])}


def derivation_records() -> dict:
    """The bounded derivation search's results, keyed by claim.

    Separate from the numeric search because it is a different kind of
    evidence: a REFUTED here means the Lean kernel accepted a proof that the
    frozen statement is false, checked against that statement rather than an
    adjacent one. A NO_DERIVATION means only that no derivation was found
    within a stated universe.
    """
    p = ROOT / "reference" / "derivation_search.json"
    if not p.exists():
        return {}
    return {r["claim"]: r for r in json.loads(p.read_text(encoding="utf-8")).get("searches", [])}


def cex_gate(cid: str, claim: dict, derived: dict, rec: dict | None) -> dict:
    """Decide whether a statement may be frozen, given its search record.

    The search cannot establish that a statement is true, and it says nothing
    about fidelity. What it can do is refuse to let a statement that is
    demonstrably FALSE be frozen as though it were a claim -- and catch the
    reverse, a statement annotated as a false control that nothing mechanical
    disagrees with. Both are findings about the catalogue, not about the
    search, so both block.
    """
    declared_false = (claim.get("control") or {}).get("target_claim_is_true") is False
    if rec is None:
        raise SystemExit(
            f"{cid}: no counterexample search on record. Run\n"
            f"    python3 harness/counterexample.py --out {cex_path(catalogue())}\n"
            f"before freezing. A statement that has never been attacked is not "
            f"ready to be signed (ROADMAP 5.1).")
    if rec.get("statement_sha256") != derived["statement_sha256"]:
        raise SystemExit(
            f"{cid}: the counterexample search was run against a DIFFERENT "
            f"statement (searched {str(rec.get('statement_sha256'))[:12]}, "
            f"current {derived['statement_sha256'][:12]}). The statement changed "
            f"after it was searched; re-run harness/counterexample.py.")
    if rec["outcome"] == "REFUTED" and not declared_false:
        raise SystemExit(
            f"{cid}: the frozen statement is FALSE -- counterexample "
            f"{rec.get('witness')}. It is not annotated as a false-claim "
            f"control, so this is not a control that was meant to be false: "
            f"either the statement is wrong or the claim text is.")
    if declared_false and rec["outcome"] != "REFUTED":
        # The numeric search could not refute it. A kernel-checked DERIVATION
        # refutation counts instead, and is better evidence than the numeric
        # search would have been: a proof the kernel accepted, rather than a
        # point in a box.
        drv = derivation_records().get(cid) or {}
        kernel_refuted = drv.get("outcome") == "REFUTED"
        if kernel_refuted:
            sc = (drv.get("kernel") or {}).get("statement_check") or {}
            if not sc.get("negates_frozen_statement_structurally"):
                raise SystemExit(
                    f"{cid}: a derivation refutation is on record but it does not "
                    f"negate this frozen statement; re-run "
                    f"harness/derivation_search.py")
            rec["refuted_by"] = "bounded derivation search, checked by the Lean kernel"
            rec["refutation_decl"] = (drv.get("kernel") or {}).get("refutation_decl")
        elif not rec.get("falsity_not_searchable"):
            raise SystemExit(
                f"{cid}: annotated as a false-claim control, but nothing refutes "
                f"it (numeric search: {rec['outcome']}; derivation search: "
                f"{drv.get('outcome', 'none on record')}). Either a bound is too "
                f"small, the annotation is wrong, or the falsity is out of both "
                f"searches' reach -- in which case say so in "
                f"reference/counterexample_bounds.json under "
                f"\"falsity_not_searchable\".")
    # `seconds` is wall-clock, so it differs on every run; a content-addressed
    # record that nobody can reproduce byte-for-byte is worse than one without
    # the timing. It stays in the search record file, not in the signature.
    return {k: v for k, v in rec.items()
            if k not in ("claim", "decl", "seconds")}


def cmd_freeze(args):
    cat = catalogue()
    derived = derive(cat)
    AD = attest_dir(cat)
    AD.mkdir(parents=True, exist_ok=True)
    now = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    cex = cex_records(cat)
    for cid, d in derived.items():
        ok, problems = guards_ok(d)
        if not ok and not args.allow_guard_failure:
            raise SystemExit(f"{cid}: guards not satisfied: {problems}; "
                             f"fix the guards before freezing (or pass "
                             f"--allow-guard-failure to record the failure)")
        claim = next(c for c in cat["claims"] if c["id"] == cid)
        review = claim.get("review", {})
        # Inside the record, so the signature covers it: what was attacked,
        # over what box, and with what result.
        cex_block = cex_gate(cid, claim, d, cex.get(cid))
        rec = {
            "schema": "ampas-formalization-attestation/1",
            "claim": cid,
            "theorem": d["theorem"],
            "text": d["text"],
            # The target claim and the verdict on it are separate propositions.
            # `text` is the claim the statement formalizes; `control` records
            # that the claim is FALSE and must never be certified. Collapsing
            # them would make `faithful` ambiguous: a reader could take it to
            # mean the Lean statement formalizes "P is false", which it does
            # not -- it formalizes P, and the outer negation is nowhere in it.
            "control": d.get("control"),
            "frozen_at": now,
            "lean_version": cat["lean_version"],
            "reference_module": cat["reference_module"],
            "statement_sha256": d["statement_sha256"],
            "closure_sha256": d["closure_sha256"],
            "closure_size": d["closure_size"],
            "closure_entries": d["closure_entries"],
            "policy": d["policy"],
            "guards": d["guards"],
            "guards_satisfied": ok,
            "guard_problems": problems,
            "counterexample_search": cex_block,
            # Three separate things, because conflating them is how a record
            # comes to assert a judgement nobody made. `prepared_by` is the
            # machine-reproducible part (hashes, guard types, closure list);
            # `reviewed_by` is whoever actually formed the fidelity judgement;
            # `confirmed_by` is the accountable owner, and it stays null until
            # they say so. Earlier rounds had one `attested_by` field, which
            # the freeze filled with the owner's name for records the
            # assistant had prepared.
            "prepared_by": review.get("prepared_by", "UNATTRIBUTED"),
            "reviewer": {
                "reviewed_by": review.get("reviewed_by", "UNREVIEWED"),
                "faithful": review.get("faithful", False),
                "note": review.get("note", ""),
                "reviewed_on": review.get("reviewed_on"),
                "checklist": {k: review.get("checklist", {}).get(k, False) for k in CHECKLIST},
            },
            "confirmation": {
                "confirmed_by": review.get("confirmed_by"),
                "confirmed_on": review.get("confirmed_on"),
                "mode": review.get("confirmation_mode"),
                "basis": review.get("confirmation_basis"),
            },
        }
        (AD / f"{cid}.json").write_text(
            json.dumps(rec, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
    print(f"froze {len(derived)} attestations into {AD}")
    return 0


def cmd_sign(args):
    key = load_private(Path(args.key))
    n = 0
    for p in sorted(attest_dir(catalogue()).glob("*.json")):
        rec = json.loads(p.read_text(encoding="utf-8"))
        sig = key.sign(canonical(rec)).hex()
        rec["signature"] = {"algorithm": "Ed25519", "key_id": args.key_id,
                            "signed_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                            "value": sig}
        p.write_text(json.dumps(rec, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
        n += 1
    print(f"signed {n} attestations with key {args.key_id}")
    return 0


def cmd_verify(args):
    cat = catalogue()
    derived = derive(cat)
    pub = json.loads((ROOT / "reference" / "reviewer_key.json").read_text(encoding="utf-8"))
    pubkey = load_public(pub["public_key_pem"])
    failures = []
    checked = 0
    for c in cat["claims"]:
        cid = c["id"]
        p = attest_dir(cat) / f"{cid}.json"
        if not p.exists():
            failures.append(f"{cid}: no attestation (statement is not signed off)")
            continue
        rec = json.loads(p.read_text(encoding="utf-8"))
        d = derived[cid]
        checked += 1
        # 1. signature
        sig = rec.get("signature")
        if not sig:
            failures.append(f"{cid}: attestation is unsigned")
        else:
            if sig.get("key_id") != pub["key_id"]:
                failures.append(f"{cid}: signed by unknown key {sig.get('key_id')}")
            try:
                pubkey.verify(bytes.fromhex(sig["value"]), canonical(rec))
            except Exception:
                failures.append(f"{cid}: SIGNATURE INVALID (the record was altered)")
        # 2. the statement itself
        if rec["statement_sha256"] != d["statement_sha256"]:
            failures.append(f"{cid}: STATEMENT DRIFT - the reference statement changed "
                            f"since sign-off")
        # 2b. the counterexample search inside the signed record must be
        # about the statement that is there NOW. The signature proves the
        # record was not altered; it cannot notice that the statement moved
        # out from under a clean search result.
        cexb = rec.get("counterexample_search")
        if cexb is None:
            failures.append(f"{cid}: the attestation records no counterexample search")
        else:
            if cexb.get("statement_sha256") != d["statement_sha256"]:
                failures.append(
                    f"{cid}: SEARCH DRIFT - the counterexample search in this "
                    f"attestation was run against a different statement")
            if cexb.get("outcome") == "REFUTED" and \
                    (d.get("control") or {}).get("target_claim_is_true") is not False:
                failures.append(
                    f"{cid}: the statement is refuted by counterexample "
                    f"{cexb.get('witness')} and is not a declared false-claim control")
        # 3. everything the statement rests on
        if rec["closure_sha256"] != d["closure_sha256"]:
            old, new = rec.get("closure_entries", {}), d["closure_entries"]
            changed = sorted(k for k in set(old) & set(new) if old[k] != new[k])
            gone = sorted(set(old) - set(new))
            added = sorted(set(new) - set(old))
            detail = []
            if changed:
                detail.append("changed: " + ", ".join(changed[:6]))
            if gone:
                detail.append("removed: " + ", ".join(gone[:6]))
            if added:
                detail.append("added: " + ", ".join(added[:6]))
            failures.append(f"{cid}: CLOSURE DRIFT - a definition the statement rests on "
                            f"changed ({'; '.join(detail)})")
        # 4. the guards still hold
        ok, problems = guards_ok(d)
        if not ok:
            failures.append(f"{cid}: guards no longer satisfied: {problems}")
        # 5. the human part is actually present, and attributed to whoever
        #    really did it. A record must not be able to pass by naming the
        #    owner for work they did not do, so the three roles are checked
        #    separately and a missing confirmation is reported as missing
        #    rather than inferred from the review.
        rv = rec.get("reviewer", {})
        if not rec.get("prepared_by") or rec["prepared_by"] == "UNATTRIBUTED":
            failures.append(f"{cid}: no prepared_by")
        if not rv.get("reviewed_by") or rv["reviewed_by"] == "UNREVIEWED":
            failures.append(f"{cid}: no reviewed_by (nobody is named as having reviewed it)")
        if not rv.get("faithful"):
            failures.append(f"{cid}: reviewer did not attest faithfulness")
        missing = [k for k, v in rv.get("checklist", {}).items() if not v]
        if missing:
            failures.append(f"{cid}: checklist incomplete: {', '.join(missing)}")
        # 5b. the checklist ticks must point at something (ROADMAP 5.4).
        #
        # Six booleans, all true, for every claim: a reviewer who thought hard
        # and one who ticked six boxes left byte-identical records, so the
        # checklist could not distinguish them. harness/checklist_evidence.py
        # derives, per item, the object the tick is a claim about -- the binder
        # order, the conventions in play, the definitions, the conclusion --
        # and binds it to the statement's hash.
        #
        # This is checked for every claim, signed or not, because the evidence
        # is DERIVED rather than attested: it is recomputable from the
        # reference beside it. What cannot be back-dated is whether the
        # reviewer saw it, so that is reported separately below instead of
        # being implied by its presence.
        ev = checklist_evidence_for(cat, cid)
        if ev is None:
            failures.append(
                f"{cid}: no per-item checklist evidence; run "
                f"`python3 harness/checklist_evidence.py write` (ROADMAP 5.4)")
        else:
            if ev["statement_sha256"] != d["statement_sha256"]:
                failures.append(
                    f"{cid}: EVIDENCE DRIFT - the per-item checklist evidence was "
                    f"derived from a different statement than the one in the "
                    f"reference now")
            got = set(ev.get("items", {}))
            if got != set(CHECKLIST):
                failures.append(
                    f"{cid}: checklist evidence covers {sorted(got)}, not the "
                    f"six items of the checklist")
            bad = ev["items"]["hypotheses_necessary_and_satisfiable"]["guard_coverage"]
            if not bad.get("consistent"):
                failures.append(
                    f"{cid}: the hypotheses tick covers "
                    f"{bad.get('necessity_guards')} guarded hypotheses but the "
                    f"statement has {bad.get('hypothesis_binders')}")
        conf = rec.get("confirmation", {})
        if conf.get("confirmed_by") and not conf.get("mode"):
            failures.append(f"{cid}: confirmed_by set without saying how "
                            f"(mode: personally_reviewed | delegated)")
        if conf.get("mode") and not conf.get("basis"):
            failures.append(f"{cid}: confirmation mode without a recorded basis")
    # Which ticks were made with the per-item evidence available, and which
    # were made before it existed. Not a failure: the evidence is derived and
    # the drift check above is what it is FOR. Recorded because a reader who
    # finds per-item evidence beside a signed checklist will otherwise assume
    # the reviewer worked from it, and for all thirteen signed attestations
    # that is false -- ROADMAP 5.4 came after them.
    predating = []
    for c in cat["claims"]:
        p = attest_dir(cat) / f"{c['id']}.json"
        if not p.exists():
            continue
        if evidence_informed_the_tick(
                cat, c["id"], json.loads(p.read_text(encoding="utf-8"))) is False:
            predating.append(c["id"])
    report = {"checked": checked, "failures": failures,
              "checklist_evidence": {
                  "path": str(checklist_evidence_path(cat).relative_to(ROOT)
                              ).replace(os.sep, "/"),
                  "attestations_signed_before_the_evidence_existed": predating,
                  "means": (
                      "For these claims the six checklist booleans were ticked "
                      "without the per-item evidence in front of the reviewer: "
                      "it is derived from the same statement afterwards, so it "
                      "shows WHAT the ticks were about and detects the statement "
                      "moving, but it is not a record that the reviewer examined "
                      "any of it. A tick made with the evidence available is a "
                      "different and stronger thing, and no attestation here is "
                      "one yet."),
              },
              "verified_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}
    if args.out:
        Path(args.out).write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8", newline="\n")
    for f in failures:
        print("FAIL:", f)
    print(f"{checked} attestations checked, {len(failures)} failures")
    return 1 if failures else 0


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)
    f = sub.add_parser("freeze"); f.add_argument("--allow-guard-failure", action="store_true")
    f.set_defaults(fn=cmd_freeze)
    s = sub.add_parser("sign"); s.add_argument("--key", required=True)
    s.add_argument("--key-id", required=True); s.set_defaults(fn=cmd_sign)
    v = sub.add_parser("verify"); v.add_argument("--out"); v.set_defaults(fn=cmd_verify)
    k = sub.add_parser("keygen"); k.add_argument("--private", required=True)
    k.add_argument("--custody", help="who holds the private key, in one line; "
                                     "recorded in the public key file")
    k.add_argument("--public", required=True); k.add_argument("--key-id", required=True)
    k.set_defaults(fn=lambda a: keygen(Path(a.private), Path(a.public), a.key_id,
                                       getattr(a, "custody", None)) or 0)
    args = ap.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
