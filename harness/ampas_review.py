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
                             text=True, timeout=60)
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


def audit_cmd() -> list[str]:
    """The compiled auditor if present, otherwise `lean --run` on its source
    (slower, but needs no C toolchain). See harness/ampas_lean.py."""
    if AUDIT_BIN.exists() and os.access(AUDIT_BIN, os.X_OK):
        return [str(AUDIT_BIN)]
    require_lean()
    return [str(LEAN_ROOT / "bin" / "lean"), "--run", str(HERE / "Audit.lean")]

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
    req.write_text(json.dumps(request))
    env = dict(os.environ)
    env["PATH"] = f"{LEAN_ROOT / 'bin'}:{env.get('PATH','')}"
    env["LEAN_PATH"] = str(TRUSTED_OLEAN)
    try:
        r = subprocess.run(audit_cmd() + [str(req)], capture_output=True, text=True,
                           env=env, timeout=600)
        if r.returncode != 0:
            raise SystemExit(f"auditor failed: {r.stdout}\n{r.stderr}")
        return json.loads(r.stdout.strip().splitlines()[-1])
    finally:
        req.unlink(missing_ok=True)


def catalogue() -> dict:
    return json.loads(CATALOGUE.read_text())


def review_module(cat: dict) -> str:
    """The module the sanity pass loads: it must contain the frozen
    statements and, when the catalogue has guards, the guard theorems."""
    return cat.get("guards_module", cat["reference_module"])


def attest_dir(cat: dict) -> Path:
    sub = cat.get("attestation_dir")
    return (ROOT / sub) if sub else ATTEST_DIR


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
    pub_path.write_text(json.dumps(rec, indent=2, ensure_ascii=False) + "\n")
    print(f"private key -> {priv_path} (keep out of the package; never commit it)")
    print(f"public key  -> {pub_path}")
    print(f"custody     -> {rec['custody'][:72]}...")


def cmd_freeze(args):
    cat = catalogue()
    derived = derive(cat)
    AD = attest_dir(cat)
    AD.mkdir(parents=True, exist_ok=True)
    now = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    for cid, d in derived.items():
        ok, problems = guards_ok(d)
        if not ok and not args.allow_guard_failure:
            raise SystemExit(f"{cid}: guards not satisfied: {problems}; "
                             f"fix the guards before freezing (or pass "
                             f"--allow-guard-failure to record the failure)")
        claim = next(c for c in cat["claims"] if c["id"] == cid)
        review = claim.get("review", {})
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
            json.dumps(rec, indent=2, ensure_ascii=False) + "\n")
    print(f"froze {len(derived)} attestations into {AD}")
    return 0


def cmd_sign(args):
    key = load_private(Path(args.key))
    n = 0
    for p in sorted(attest_dir(catalogue()).glob("*.json")):
        rec = json.loads(p.read_text())
        sig = key.sign(canonical(rec)).hex()
        rec["signature"] = {"algorithm": "Ed25519", "key_id": args.key_id,
                            "signed_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                            "value": sig}
        p.write_text(json.dumps(rec, indent=2, ensure_ascii=False) + "\n")
        n += 1
    print(f"signed {n} attestations with key {args.key_id}")
    return 0


def cmd_verify(args):
    cat = catalogue()
    derived = derive(cat)
    pub = json.loads((ROOT / "reference" / "reviewer_key.json").read_text())
    pubkey = load_public(pub["public_key_pem"])
    failures = []
    checked = 0
    for c in cat["claims"]:
        cid = c["id"]
        p = attest_dir(cat) / f"{cid}.json"
        if not p.exists():
            failures.append(f"{cid}: no attestation (statement is not signed off)")
            continue
        rec = json.loads(p.read_text())
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
        conf = rec.get("confirmation", {})
        if conf.get("confirmed_by") and not conf.get("mode"):
            failures.append(f"{cid}: confirmed_by set without saying how "
                            f"(mode: personally_reviewed | delegated)")
        if conf.get("mode") and not conf.get("basis"):
            failures.append(f"{cid}: confirmation mode without a recorded basis")
    report = {"checked": checked, "failures": failures,
              "verified_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}
    if args.out:
        Path(args.out).write_text(json.dumps(report, indent=2, ensure_ascii=False))
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
