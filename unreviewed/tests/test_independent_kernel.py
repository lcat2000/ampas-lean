"""The independent kernel: it must confirm the real proofs and reject bad ones.

A checker that accepted everything would also report "re-checked", so the
rejection tests below are what make the confirmation mean anything.
"""
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import ampas_lean as A                                   # noqa: E402
from kernel.parse import parse_export                    # noqa: E402
from kernel.check import Checker, check_env              # noqa: E402
from kernel import terms as T                            # noqa: E402

CLAIMS = {
    "Genuine": ["Ampas.Claims.add_comm_nat", "Ampas.Claims.sub_add_cancel_nat",
                "Ampas.Claims.even_add_even", "Ampas.Claims.dvd_trans_nat",
                "Ampas.Claims.exists_greater", "Ampas.Claims.div_self_pos"],
    "PLSol": ["Ampas.Claims.pl_independent"],
    "ELSol": ["Ampas.Claims.el_comm_independent"],
}


def _export(tmp: Path, source: Path, module: str, roots: list) -> Path:
    """Compile a corpus module and export the closure of the given roots."""
    build = tmp / "b"
    build.mkdir(exist_ok=True)
    for olean in (ROOT / "build").rglob("*.olean"):
        dest = build / olean.relative_to(ROOT / "build")
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(olean.read_bytes())
    src = tmp / f"{module}.lean"
    src.write_bytes(source.read_bytes())
    lean_path = str(build)
    env = {"PATH": f"{A.LEAN_BIN}:/usr/bin:/bin", "LEAN_PATH": lean_path,
           "HOME": str(tmp), "LEAN_NUM_THREADS": "2"}
    r = subprocess.run([str(A.LEAN_BIN / "lean"), "-o", str(build / f"{module}.olean"),
                        str(src)], cwd=tmp, env=env, capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
    out = tmp / "x.export"
    r = subprocess.run([str(A.LEAN_BIN / "lean"), "--run", str(A.EXPORT_LEAN), module,
                        str(out)] + roots, cwd=tmp, env=env, capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
    return out


@pytest.fixture(scope="session")
def exports():
    tmp = Path(tempfile.mkdtemp(prefix="ampas-kernel-tests-"))
    out = {}
    for module, roots in CLAIMS.items():
        d = tmp / module
        d.mkdir()
        out[module] = _export(d, ROOT / "corpus" / f"{module}.lean", module, roots)
    return out


# ---- the real proofs are confirmed, in full
@pytest.mark.parametrize("module", sorted(CLAIMS))
def test_claim_closure_is_fully_rechecked(exports, module):
    env = parse_export(str(exports[module]))
    sys.setrecursionlimit(60000)
    res = check_env(env)
    assert res["errors"] == [], res["errors"][:3]
    assert res["checked"] == res["total"] > 0


# ---- and bad proofs are rejected
def test_kernel_bypass_is_rejected():
    """The skipKernelTC attack: the elaborator accepted `false_thm : False :=
    True.intro`; the independent kernel must reject it."""
    tmp = Path(tempfile.mkdtemp(prefix="ampas-bypass-"))
    exp = _export(tmp, ROOT / "corpus" / "attacks" / "A01_kernel_bypass.lean",
                  "A01_kernel_bypass", ["Ampas.Claims.add_comm_nat"])
    env = parse_export(str(exp))
    sys.setrecursionlimit(60000)
    res = check_env(env)
    assert res["errors"], "the independent kernel accepted a kernel bypass"
    assert any("false_thm" in n for n, _ in res["errors"])


def test_a_swapped_theorem_type_is_rejected(exports):
    """Mutation: give one theorem another theorem's declared type. The
    closure must stop checking."""
    text = Path(exports["Genuine"]).read_text().splitlines()
    thms = [i for i, l in enumerate(text) if l.startswith("#THM ")]
    assert len(thms) >= 2
    # point the last theorem at the first theorem's declared type: that index
    # is defined early, so every reference stays backward and the file still
    # parses -- the rejection has to come from type checking
    first_type = text[thms[0]].split(" ")[2]
    last = text[thms[-1]].split(" ")
    assert last[2] != first_type
    last[2] = first_type
    text[thms[-1]] = " ".join(last)
    tmp = Path(tempfile.mkdtemp(prefix="ampas-mut-")) / "m.export"
    tmp.write_text("\n".join(text) + "\n")
    env = parse_export(str(tmp))
    sys.setrecursionlimit(60000)
    res = check_env(env)
    assert res["errors"], "a swapped theorem type was accepted"


def test_K_reduction_needs_the_constructor_to_have_the_right_type(exports):
    """Regression (a real bug this checker had): K-like reduction may replace
    the major premise of Eq.rec by Eq.refl only when that constructor really
    has the premise's type. Without the check, any equality proof in context
    would make its two sides definitionally equal."""
    env = parse_export(str(exports["ELSol"]))
    ch = Checker(env)

    def nm(s):
        for k in env.decls:
            if k.str == s:
                return k
        pytest.skip(f"{s} not in the export")

    prop = T.sort(T.ZERO)
    p = ch.fresh(prop)                                    # p : Prop, opaque
    false_ = T.const(nm("False"), [])
    eq1 = T.const(nm("Eq"), [T.succ(T.ZERO)])
    h = ch.fresh(T.apps(eq1, [prop, p, false_]))          # h : p = False
    # p and False must NOT become definitionally equal
    assert not ch.is_def_eq(p, false_)
    # and the eliminator must not treat h as rfl
    rec = env.decls[nm("Eq.rec")] if any(k.str == "Eq.rec" for k in env.decls) else None
    if rec is not None:
        assert ch._to_ctor_when_k(rec, h) is h


def test_level_arithmetic():
    one = T.succ(T.ZERO)
    u = T.param(T.Name.anonymous().child("u"))
    assert T.level_eq(one, T.limax(one, one))
    assert T.level_eq(T.lmax(one, u), T.limax(u, T.limax(u, one)))
    assert T.level_eq(T.limax(u, T.ZERO), T.ZERO)
    assert not T.level_eq(u, one)
    assert not T.level_eq(T.ZERO, one)
