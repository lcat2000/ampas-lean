#!/usr/bin/env python3
"""AMPAS: the formalization-correctness review process.

Lean can establish that a submission proves the reference statement. It
cannot establish that the reference statement says what the claim's
natural-language text says. That judgement is a human one, so it is recorded
here as an explicit, signed, version-frozen artifact, and the pipeline
refuses to certify a claim whose record does not verify.

What this tool pins down:

  statement freeze
    Each claim's reference statement is hashed by MEANING, not by source
    text: the hash covers the elaborated type of the reference theorem plus
    the transitive closure of the definitions that type rests on (exported in
    "statement" mode, where proofs are excluded). Renaming a binder or
    reformatting the file does not change it; redefining `IsEven`, or
    weakening a hypothesis, does.

  sign-off
    The reviewer attests that a specific statement hash renders a specific
    natural-language text, and the attestation covers the claim's policy too
    (axioms and comparator). The sign-off digest binds all of it together, so
    editing the text, the policy or the statement after sign-off invalidates
    it and the claim stops being certifiable until a reviewer signs again.

  drift detection
    `verify` recomputes every statement hash from the current reference
    environment and compares it with the frozen value, so a silent change to
    the reference -- the most dangerous change there is, because every
    submission is checked against it -- is caught.

Honest limits: with no key infrastructure in this environment, a sign-off is
an integrity-and-intent record, not proof of identity: the digest shows that
the reviewer's recorded attestation matches exactly this statement, text and
policy, and that nothing has changed since. Set AMPAS_REVIEW_KEY to a secret
to additionally require an HMAC over the same content, which does bind the
sign-off to the holder of that key. Who may hold a key, and how reviewers are
authenticated, is a deployment question and is out of scope here.
"""
from __future__ import annotations

import hashlib
import hmac
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
LEAN_BIN = Path(os.environ.get("LEAN_ROOT", "/home/claude/tools/lean4")) / "bin"
EXPORT_LEAN = HERE / "Export.lean"
CLAIMS_PATH = ROOT / "reference" / "claims.json"
FREEZE_PATH = ROOT / "reference" / "freeze.json"

SIGNED_FIELDS = ("claim", "theorem", "text", "policy", "statement_sha256",
                 "reviewer", "attested_at")


def _sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def load_claims() -> dict:
    return json.loads(CLAIMS_PATH.read_text())


def statement_hash(module: str, theorem: str, trusted_olean: Path) -> str:
    """SHA-256 of the statement-mode export of this theorem's closure."""
    with tempfile.TemporaryDirectory(prefix="ampas-freeze-") as td:
        out = Path(td) / "s.export"
        env = {"PATH": f"{LEAN_BIN}:/usr/bin:/bin", "LEAN_PATH": str(trusted_olean),
               "HOME": td, "LEAN_NUM_THREADS": "2"}
        r = subprocess.run([str(LEAN_BIN / "lean"), "--run", str(EXPORT_LEAN),
                            "--statement", module, str(out), theorem],
                           cwd=td, env=env, capture_output=True, text=True, timeout=300)
        if r.returncode != 0 or not out.exists():
            raise RuntimeError(f"statement export failed for {theorem}: "
                               f"{(r.stdout + r.stderr)[-500:]}")
        return _sha256_bytes(out.read_bytes())


def signed_content(claim: dict, statement_sha256: str) -> dict:
    review = claim.get("review", {})
    return {
        "claim": claim["id"],
        "theorem": claim["theorem"],
        "text": claim["text"],
        "policy": claim.get("policy", {}),
        "statement_sha256": statement_sha256,
        "reviewer": review.get("reviewer") or review.get("attested_by"),
        "attested_at": review.get("attested_at"),
    }


def signoff_digest(claim: dict, statement_sha256: str) -> str:
    body = json.dumps(signed_content(claim, statement_sha256),
                      sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    return _sha256_bytes(body.encode("utf-8"))


def signoff_hmac(claim: dict, statement_sha256: str, key: bytes) -> str:
    body = json.dumps(signed_content(claim, statement_sha256),
                      sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    return hmac.new(key, body.encode("utf-8"), hashlib.sha256).hexdigest()


def _key() -> bytes | None:
    k = os.environ.get("AMPAS_REVIEW_KEY")
    return k.encode("utf-8") if k else None


def freeze(trusted_olean: Path) -> dict:
    cat = load_claims()
    out = {"lean_version": cat.get("lean_version"),
           "reference_module": cat["reference_module"], "claims": {}}
    key = _key()
    for c in cat["claims"]:
        sh = statement_hash(cat["reference_module"], c["theorem"], trusted_olean)
        rec = {"theorem": c["theorem"], "statement_sha256": sh,
               "signoff_sha256": signoff_digest(c, sh)}
        if key:
            rec["signoff_hmac"] = signoff_hmac(c, sh, key)
        out["claims"][c["id"]] = rec
    return out


def verify(trusted_olean: Path, freeze_doc: dict | None = None) -> dict:
    """Per claim: FROZEN_OK, DRIFT (the reference statement changed),
    UNSIGNED (no frozen record), SIGNOFF_STALE (text, policy or reviewer
    changed since sign-off), HMAC_BAD."""
    cat = load_claims()
    fz = freeze_doc if freeze_doc is not None else (
        json.loads(FREEZE_PATH.read_text()) if FREEZE_PATH.exists() else {"claims": {}})
    key = _key()
    results = {}
    for c in cat["claims"]:
        cid = c["id"]
        rec = fz.get("claims", {}).get(cid)
        if rec is None:
            results[cid] = {"status": "UNSIGNED", "ok": False,
                            "detail": "no frozen, signed record for this claim"}
            continue
        try:
            sh = statement_hash(cat["reference_module"], c["theorem"], trusted_olean)
        except RuntimeError as e:
            results[cid] = {"status": "ERROR", "ok": False, "detail": str(e)[:300]}
            continue
        if sh != rec["statement_sha256"]:
            results[cid] = {"status": "DRIFT", "ok": False,
                            "detail": "the reference statement changed since sign-off",
                            "frozen": rec["statement_sha256"], "current": sh}
            continue
        if signoff_digest(c, sh) != rec["signoff_sha256"]:
            results[cid] = {"status": "SIGNOFF_STALE", "ok": False,
                            "detail": "the text, policy or reviewer changed after sign-off"}
            continue
        if key is not None:
            want = rec.get("signoff_hmac")
            if not want or not hmac.compare_digest(signoff_hmac(c, sh, key), want):
                results[cid] = {"status": "HMAC_BAD", "ok": False,
                                "detail": "the sign-off HMAC does not verify with this key"}
                continue
        results[cid] = {"status": "FROZEN_OK", "ok": True,
                        "statement_sha256": sh,
                        "reviewer": signed_content(c, sh)["reviewer"],
                        "attested_at": signed_content(c, sh)["attested_at"]}
    return results


def main(argv: list) -> int:
    import argparse
    ap = argparse.ArgumentParser(prog="review")
    ap.add_argument("command", choices=["freeze", "verify"])
    ap.add_argument("--trusted-olean",
                    default=os.environ.get("AMPAS_TRUSTED_OLEAN", str(ROOT / "build")))
    ap.add_argument("--out")
    args = ap.parse_args(argv)
    olean = Path(args.trusted_olean)
    if args.command == "freeze":
        doc = freeze(olean)
        text = json.dumps(doc, indent=2, ensure_ascii=False) + "\n"
        (Path(args.out) if args.out else FREEZE_PATH).write_text(text)
        print(text)
        return 0
    res = verify(olean)
    print(json.dumps(res, indent=2, ensure_ascii=False))
    bad = {k: v for k, v in res.items() if not v["ok"]}
    if bad:
        print(f"\n{len(bad)} claim(s) did not verify: {sorted(bad)}", file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
