"""A second frontend for `harness/kernel3`: lean4export's NDJSON format.

ROADMAP 6/1.3b. `kernel3` has five specification passes, each differentially
tested, and four adversarial vectors — all four of which this repository wrote
itself. The [Lean Kernel Arena](https://arena.lean-lang.org/) publishes 198
tests for exactly the layer `kernel3` occupies: 72 that must be REJECTED
(including 19 regressions for real Lean kernel bugs) and 126 that must be
ACCEPTED. They are in lean4export's NDJSON format, version 3.1.0, so reading
that format is what stands between `kernel3` and its first external
measurement.

**This module is a translation, and a translation can be the thing that
fails.** If it drops a declaration, mangles a de Bruijn index or silently
ignores a record kind, the arena result measures this file rather than the
checker — and would do so in the dangerous direction, since a dropped
declaration is one `kernel3` cannot object to. Three things guard against
that:

  * every record kind in the format is handled explicitly, and an unknown one
    RAISES rather than being skipped (`tests/test_ndjson.py` pins the list
    against the kinds the arena corpus actually contains);
  * `harness/ndjson_differential.py` exports the same Lean environment through
    BOTH frontends and compares the resulting `Env` declaration by
    declaration, by `decl_fingerprint`, so a divergence is a test failure
    rather than a surprise in the arena numbers;
  * nothing here interprets anything. It builds the same `Decl`/`Expr`
    structures `parse.py` builds and makes no judgement about them.

**One real difference between the formats**, and it matters for the recursor
and iota passes: NDJSON carries an inductive **block** — its types, its
constructors and its recursors — in a single `inductive` record, whereas the
AMPAS format has separate `#IND`, `#CTOR` and `#REC` lines. The block is
unpacked here in that order, so the `Env` that comes out has the same shape
either way. The block also carries `numNested`, which the AMPAS format does
not; it is read and kept on the declaration (`num_nested`) but nothing in
`kernel3` consults it yet, and it is NOT folded into any existing field.
"""
from __future__ import annotations

import json

from .parse import Decl, Env
from .terms import (Name, ZERO, succ, lmax, limax, param, bvar, sort, const,
                    app, lam, pi, elet, proj, natlit, strlit, Expr, Level)

# Every record kind the format defines. An unknown kind is an error, never a
# skipped line: a skipped declaration is one the checker cannot object to.
EXPR_KINDS = {"bvar", "sort", "const", "app", "lam", "forallE", "letE",
              "proj", "natVal", "strVal"}
LEVEL_KINDS = {"succ", "max", "imax", "param"}
DECL_KINDS = {"def", "thm", "axiom", "opaque", "quot", "inductive"}


def _mark_safety(decl, record: dict) -> None:
    """Carry the record's `safety` / `isUnsafe` onto the declaration.

    The AMPAS format has no field for either, because `harness/Export.lean`
    emits only what the trusted reference environment contains and lean4export
    excludes unsafe declarations unless `--export-unsafe` is passed. So an
    absent flag means "safe" for both frontends, and a PRESENT one means the
    file was made with that flag or by hand -- which is what the arena's
    `140_falseFromUnsafe` and `141_falseFromPartial` do, and what
    `harness/kernel3/safety.py` then objects to.

    The first version of this frontend read both fields and threw them away,
    so a `def` marked `unsafe` that a theorem then used was accepted.
    """
    decl.safety = str(record.get("safety") or
                      ("unsafe" if record.get("isUnsafe") else "safe"))


class NdjsonError(Exception):
    """A record this frontend does not understand, with its line number."""


def parse_ndjson(path: str) -> Env:
    """Read a lean4export NDJSON file into the same Env `parse_export` builds."""
    names: dict = {0: Name.anonymous()}
    levels: dict = {0: ZERO}
    exprs: dict = {}
    env = Env()
    env.mode = "proof"

    def N(i) -> Name:
        try:
            return names[int(i)]
        except KeyError:
            raise NdjsonError(f"name index {i} used before it was defined")

    def L(i) -> Level:
        try:
            return levels[int(i)]
        except KeyError:
            raise NdjsonError(f"level index {i} used before it was defined")

    def E(i) -> Expr:
        try:
            return exprs[int(i)]
        except KeyError:
            raise NdjsonError(f"expression index {i} used before it was defined")

    def LP(xs) -> list:
        return [N(x) for x in (xs or [])]

    with open(path, "r", encoding="utf-8") as f:
        for lineno, raw in enumerate(f, 1):
            line = raw.strip()
            if not line:
                continue
            try:
                o = json.loads(line)
            except json.JSONDecodeError as e:
                raise NdjsonError(f"line {lineno}: not JSON: {e}") from None
            try:
                _record(o, env, names, levels, exprs, N, L, E, LP)
            except NdjsonError as e:
                raise NdjsonError(f"line {lineno}: {e}") from None
    return env


def _record(o, env, names, levels, exprs, N, L, E, LP):
    # ---- the header. Only the format version is acted on: a file that says
    # it is a format this frontend was not written against is refused rather
    # than read optimistically.
    if "meta" in o:
        v = ((o["meta"].get("format") or {}).get("version"))
        if v is not None and not str(v).startswith("3."):
            raise NdjsonError(f"export format version {v}; this reader is for 3.x")
        env.module = str((o["meta"].get("lean") or {}).get("version") or "")
        return

    # ---- names
    if "in" in o:
        i = int(o["in"])
        if "str" in o:
            s = o["str"]
            names[i] = N(s["pre"]).child(str(s["str"]))
        elif "num" in o:
            n = o["num"]
            names[i] = N(n["pre"]).child(int(n["i"]))
        else:
            raise NdjsonError(f"name record with neither str nor num: {sorted(o)}")
        return

    # ---- levels
    if "il" in o:
        i = int(o["il"])
        kinds = set(o) & LEVEL_KINDS
        if len(kinds) != 1:
            raise NdjsonError(f"level record with kinds {sorted(set(o) - {'il'})}")
        k = kinds.pop()
        if k == "succ":
            levels[i] = succ(L(o["succ"]))
        elif k == "max":
            a, b = o["max"]
            levels[i] = lmax(L(a), L(b))
        elif k == "imax":
            a, b = o["imax"]
            levels[i] = limax(L(a), L(b))
        else:
            levels[i] = param(N(o["param"]))
        return

    # ---- expressions
    if "ie" in o:
        i = int(o["ie"])
        kinds = set(o) & EXPR_KINDS
        if len(kinds) != 1:
            raise NdjsonError(f"expression record with kinds {sorted(set(o) - {'ie'})}")
        k = kinds.pop()
        v = o[k]
        if k == "bvar":
            exprs[i] = bvar(int(v))
        elif k == "sort":
            exprs[i] = sort(L(v))
        elif k == "const":
            exprs[i] = const(N(v["name"]), [L(u) for u in (v.get("us") or [])])
        elif k == "app":
            exprs[i] = app(E(v["fn"]), E(v["arg"]))
        elif k == "lam":
            exprs[i] = lam(N(v["name"]), E(v["type"]), E(v["body"]))
        elif k == "forallE":
            exprs[i] = pi(N(v["name"]), E(v["type"]), E(v["body"]))
        elif k == "letE":
            exprs[i] = elet(N(v["name"]), E(v["type"]), E(v["value"]), E(v["body"]))
        elif k == "proj":
            # kernel3's `proj` takes the structure's type name, the index and
            # the term, in that order. An earlier draft of this frontend
            # dropped `typeName` on the belief that it was not carried; it is,
            # and dropping it would have fed every projection a wrong-arity
            # call -- 46 of the arena's tests failed to parse at all, which is
            # how it was found. The arena's proj-non-structure and
            # proj-of-*-prop tests are precisely about that name.
            exprs[i] = proj(N(v["typeName"]), int(v["idx"]), E(v["struct"]))
        elif k == "natVal":
            exprs[i] = natlit(int(v))
        else:
            exprs[i] = strlit(str(v))
        return

    # ---- declarations
    kinds = set(o) & DECL_KINDS
    if len(kinds) != 1:
        raise NdjsonError(f"unknown record: keys {sorted(o)}")
    k = kinds.pop()
    v = o[k]

    if k in ("def", "thm", "opaque"):
        d = Decl({"def": "def", "thm": "thm", "opaque": "opaque"}[k],
                 N(v["name"]), E(v["type"]), LP(v.get("levelParams")),
                 value=E(v["value"]))
        env.add(d)
        _mark_safety(d, v)
        return
    if k == "axiom":
        d = Decl("ax", N(v["name"]), E(v["type"]), LP(v.get("levelParams")))
        env.add(d)
        _mark_safety(d, v)
        return
    if k == "quot":
        env.add(Decl("quot", N(v["name"]), E(v["type"]), LP(v.get("levelParams"))))
        return

    # an inductive BLOCK: types, then constructors, then recursors, so the Env
    # ends up in the same order the AMPAS format's separate lines produce
    for t in v.get("types") or []:  # noqa: PLR1704
        env.add(Decl("ind", N(t["name"]), E(t["type"]), LP(t.get("levelParams")),
                     num_params=int(t["numParams"]),
                     num_indices=int(t["numIndices"]),
                     is_rec=bool(t.get("isRec")),
                     is_reflexive=bool(t.get("isReflexive")),
                     all_names=LP(t.get("all")),
                     ctors=LP(t.get("ctors"))))
        d = env.decls[N(t["name"])]
        d.num_nested = int(t.get("numNested", 0))
        _mark_safety(d, t)
    for c in v.get("ctors") or []:
        d = Decl("ctor", N(c["name"]), E(c["type"]), LP(c.get("levelParams")),
                 induct=N(c["induct"]), cidx=int(c["cidx"]),
                 num_params=int(c["numParams"]),
                 num_fields=int(c["numFields"]))
        env.add(d)
        _mark_safety(d, c)
    for r in v.get("recs") or []:
        d = Decl("rec", N(r["name"]), E(r["type"]), LP(r.get("levelParams")),
                 num_params=int(r["numParams"]),
                 num_indices=int(r["numIndices"]),
                 num_motives=int(r["numMotives"]),
                 num_minors=int(r["numMinors"]),
                 k=bool(r.get("k")),
                 all_names=LP(r.get("all")),
                 rules=[(N(x["ctor"]), int(x["nfields"]), E(x["rhs"]))
                        for x in (r.get("rules") or [])])
        env.add(d)
        _mark_safety(d, r)
