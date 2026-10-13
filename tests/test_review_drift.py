"""The drift detector: a signed-off statement must not be able to change
meaning silently.

Each test copies the whole suite to a scratch directory, perturbs it, and
checks that `ampas_review.py verify` fails with the right finding. These are
the tests that make the formalization sign-off worth anything: without them
the attestation is just a file with a hash in it.
"""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import ampas_lean as A  # noqa: E402
LEAN_ROOT = A.LEAN_ROOT   # detected once in the harness, not hardcoded
# The platform's actual binary name: lean.exe on Windows. Built by the one
# helper that probes for it, so these tests fail the same way the harness
# would rather than with WinError 193.
from ampas_lean import lean_exe as _lean_exe


def LEAN_EXE_FN():
    return _lean_exe("lean")


class _LeanExe:
    def __str__(self):
        return str(LEAN_EXE_FN())


LEAN_EXE = _LeanExe()
REF = ["Defs", "Challenge", "Guards"]
# where `lake build AmpasRef` puts the trusted oleans; AMPAS_TRUSTED_OLEAN may
# point elsewhere, so honour it and fall back to the Lake layout
TRUSTED_REL = Path(os.environ.get("AMPAS_TRUSTED_OLEAN_REL", ".lake/build/lib/lean"))


def _copy(tmp_path) -> Path:
    dst = tmp_path / "suite"
    # The copy needs the built oleans under .lake, so the ignore list must be
    # anchored to the top level: a plain ignore_patterns("build") would also
    # match .lake/build and silently copy a suite with no trusted oleans.
    top = {"unreviewed", "mathlib-tier", ".git", "build",
           "build-mathlib", "build-fermat"}
    anywhere = {"__pycache__", ".pytest_cache"}

    def ignore(dirpath, names):
        drop = {n for n in names if n in anywhere}
        if Path(dirpath).resolve() == ROOT:
            drop |= {n for n in names if n in top}
        return drop

    shutil.copytree(ROOT, dst, ignore=ignore)
    assert (dst / TRUSTED_REL / "AmpasRef" / "Guards.olean").exists(), (
        f"the copied suite has no trusted oleans at {TRUSTED_REL}; "
        f"run ./scripts/bootstrap.sh first")
    return dst


def _rebuild(suite: Path):
    env = dict(os.environ)
    env["PATH"] = f"{LEAN_ROOT / 'bin'}:{env.get('PATH','')}"
    env["LEAN_PATH"] = str(suite / TRUSTED_REL)
    for m in REF:
        subprocess.run([str(LEAN_EXE), "-o",
                        str(suite / TRUSTED_REL / "AmpasRef" / f"{m}.olean"),
                        str(suite / "reference" / "AmpasRef" / f"{m}.lean")],
                       capture_output=True, text=True, encoding="utf-8", env=env, cwd=suite, timeout=600)


def _verify(suite: Path):
    env = dict(os.environ)
    env["PATH"] = f"{LEAN_ROOT / 'bin'}:{env.get('PATH','')}"
    env["AMPAS_TRUSTED_OLEAN"] = str(suite / TRUSTED_REL)
    env["AMPAS_AUDIT_BIN"] = str(suite / "harness" / "audit")
    env.pop("AMPAS_CLAIMS", None)
    return subprocess.run([sys.executable, str(suite / "harness" / "ampas_review.py"), "verify"],
                          capture_output=True, text=True, encoding="utf-8", env=env, timeout=900)


def test_baseline_verifies(tmp_path):
    suite = _copy(tmp_path)
    r = _verify(suite)
    assert r.returncode == 0 and "0 failures" in r.stdout, r.stdout


def test_statement_drift_is_caught(tmp_path):
    """Dropping the b <= a hypothesis from SUB must invalidate the sign-off."""
    suite = _copy(tmp_path)
    p = suite / "reference" / "AmpasRef" / "Challenge.lean"
    t = p.read_text(encoding="utf-8")
    assert "∀ a b : Nat, b ≤ a → a - b + b = a" in t
    p.write_text(t.replace("∀ a b : Nat, b ≤ a → a - b + b = a",
                           "∀ a b : Nat, a - b + b = a"), encoding="utf-8", newline="\n")
    _rebuild(suite)
    r = _verify(suite)
    assert r.returncode != 0
    assert "STATEMENT DRIFT" in r.stdout and "SUB" in r.stdout


def test_closure_drift_is_caught_with_the_statement_untouched(tmp_path):
    """The important one: redefining IsEven changes what EVEN means while
    the statement text stays byte-identical. The freeze must still break,
    and must name the constant that changed."""
    suite = _copy(tmp_path)
    p = suite / "reference" / "AmpasRef" / "Defs.lean"
    t = p.read_text(encoding="utf-8")
    assert "def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k" in t
    p.write_text(t.replace("def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k",
                           "def IsEven (_ : Nat) : Prop := True"), encoding="utf-8", newline="\n")
    # the statement of EVEN is untouched
    assert "IsEven a → IsEven b → IsEven (a + b)" in \
        (suite / "reference" / "AmpasRef" / "Challenge.lean").read_text(encoding="utf-8")
    _rebuild(suite)
    r = _verify(suite)
    assert r.returncode != 0
    assert "CLOSURE DRIFT" in r.stdout
    assert "Ampas.IsEven" in r.stdout


def test_tampering_with_an_attestation_breaks_the_signature(tmp_path):
    """Quietly dropping the hypothesis from the attested prose."""
    suite = _copy(tmp_path)
    p = suite / "reference" / "attestations" / "DIV.json"
    d = json.loads(p.read_text(encoding="utf-8"))
    d["text"] = "For every natural number n, n / n = 1."
    p.write_text(json.dumps(d, indent=2, ensure_ascii=False), encoding="utf-8", newline="\n")
    r = _verify(suite)
    assert r.returncode != 0
    assert "SIGNATURE INVALID" in r.stdout


def test_a_missing_attestation_is_caught(tmp_path):
    suite = _copy(tmp_path)
    (suite / "reference" / "attestations" / "ADD.json").unlink()
    r = _verify(suite)
    assert r.returncode != 0
    assert "no attestation" in r.stdout and "ADD" in r.stdout


def test_an_incomplete_checklist_is_caught(tmp_path):
    """The human part has to actually be there, and it is signed, so
    flipping it also breaks the signature."""
    suite = _copy(tmp_path)
    p = suite / "reference" / "attestations" / "EVEN.json"
    d = json.loads(p.read_text(encoding="utf-8"))
    d["reviewer"]["checklist"]["definitions_reviewed"] = False
    p.write_text(json.dumps(d, indent=2, ensure_ascii=False), encoding="utf-8", newline="\n")
    r = _verify(suite)
    assert r.returncode != 0
    assert "EVEN" in r.stdout


def test_redefining_a_definition_also_breaks_the_guards(tmp_path):
    """Second, independent signal: with IsEven := True the necessity guards
    are no longer provable, so the reference does not even compile."""
    suite = _copy(tmp_path)
    p = suite / "reference" / "AmpasRef" / "Defs.lean"
    p.write_text(p.read_text(encoding="utf-8").replace(
        "def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k",
        "def IsEven (_ : Nat) : Prop := True"), newline="\n")
    env = dict(os.environ)
    env["PATH"] = f"{LEAN_ROOT / 'bin'}:{env.get('PATH','')}"
    env["LEAN_PATH"] = str(suite / TRUSTED_REL)
    for m in ["Defs", "Challenge"]:
        subprocess.run([str(LEAN_EXE), "-o",
                        str(suite / TRUSTED_REL / "AmpasRef" / f"{m}.olean"),
                        str(suite / "reference" / "AmpasRef" / f"{m}.lean")],
                       capture_output=True, text=True, encoding="utf-8", env=env, cwd=suite, timeout=600)
    g = subprocess.run([str(LEAN_EXE), "-o", str(tmp_path / "g.olean"),
                        str(suite / "reference" / "AmpasRef" / "Guards.lean")],
                       capture_output=True, text=True, encoding="utf-8", env=env, cwd=suite, timeout=600)
    assert g.returncode != 0, "the guards must stop compiling when IsEven is redefined"
