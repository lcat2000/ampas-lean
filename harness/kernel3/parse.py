"""AMPAS independent kernel: reader for the AMPAS export format.

The format is documented in harness/EXPORT_FORMAT.md. It is index based, so
shared subterms stay shared: every name, level and expression is defined on
its own line and referred to by its index afterwards.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from .terms import (Name, ZERO, succ, lmax, limax, param, bvar, sort, const, app, lam, pi,
                    elet, proj, natlit, strlit, Expr, Level)


# ---------------------------------------------------------------- declarations
@dataclass
class Decl:
    kind: str                  # ax | def | thm | opaque | quot | ind | ctor | rec
    name: Name
    type: Expr
    lvl_params: list = field(default_factory=list)
    value: Expr | None = None
    # inductive
    num_params: int = 0
    num_indices: int = 0
    is_rec: bool = False
    is_reflexive: bool = False
    all_names: list = field(default_factory=list)
    ctors: list = field(default_factory=list)
    # constructor
    induct: Name | None = None
    cidx: int = 0
    num_fields: int = 0
    # recursor
    num_motives: int = 0
    num_minors: int = 0
    k: bool = False
    rules: list = field(default_factory=list)   # (ctor Name, nfields int, rhs Expr)


@dataclass
class Env:
    decls: dict = field(default_factory=dict)       # Name -> Decl
    order: list = field(default_factory=list)       # declaration order
    module: str = ""
    mode: str = "proof"
    roots: list = field(default_factory=list)

    def get(self, n: Name) -> Decl | None:
        return self.decls.get(n)

    def add(self, d: Decl):
        if d.name in self.decls:
            raise ValueError(f"duplicate declaration {d.name}")
        self.decls[d.name] = d
        self.order.append(d.name)


def parse_export(path: str) -> Env:
    names: dict = {0: Name.anonymous()}
    levels: dict = {0: ZERO}
    exprs: dict = {}
    env = Env()

    def N(tok) -> Name:
        return names[int(tok)]

    def L(tok) -> Level:
        return levels[int(tok)]

    def E(tok) -> Expr:
        return exprs[int(tok)]

    with open(path, "r", encoding="utf-8") as f:
        for lineno, raw in enumerate(f, 1):
            line = raw.rstrip("\n")
            if not line:
                continue
            tok = line.split(" ")
            try:
                if tok[0] == "#VERSION":
                    if tok[1] != "1":
                        raise ValueError(f"unsupported export version {tok[1]}")
                    continue
                if tok[0] == "#MODE":
                    env.mode = tok[1]
                    continue
                if tok[0] == "#MODULE":
                    env.module = tok[1]
                    continue
                if tok[0] == "#ROOTS":
                    env.roots = tok[1:]
                    continue
                if tok[0].startswith("#"):
                    _decl(env, tok, N, E)
                    continue
                # an indexed definition: <idx> #TAG ...
                idx, tag = int(tok[0]), tok[1]
                rest = tok[2:]
                if tag == "#NS":
                    names[idx] = N(rest[0]).child(" ".join(rest[1:]))
                elif tag == "#NI":
                    names[idx] = N(rest[0]).child(int(rest[1]))
                elif tag == "#US":
                    levels[idx] = succ(L(rest[0]))
                elif tag == "#UM":
                    levels[idx] = lmax(L(rest[0]), L(rest[1]))
                elif tag == "#UIM":
                    levels[idx] = limax(L(rest[0]), L(rest[1]))
                elif tag == "#UP":
                    levels[idx] = param(N(rest[0]))
                elif tag == "#EV":
                    exprs[idx] = bvar(int(rest[0]))
                elif tag == "#ES":
                    exprs[idx] = sort(L(rest[0]))
                elif tag == "#EC":
                    exprs[idx] = const(N(rest[0]), [L(x) for x in rest[1:]])
                elif tag == "#EA":
                    exprs[idx] = app(E(rest[0]), E(rest[1]))
                elif tag == "#EL":
                    exprs[idx] = lam(N(rest[1]), E(rest[2]), E(rest[3]))
                elif tag == "#EP":
                    exprs[idx] = pi(N(rest[1]), E(rest[2]), E(rest[3]))
                elif tag == "#EZ":
                    exprs[idx] = elet(N(rest[0]), E(rest[1]), E(rest[2]), E(rest[3]))
                elif tag == "#EJ":
                    exprs[idx] = proj(N(rest[0]), int(rest[1]), E(rest[2]))
                elif tag == "#ELN":
                    exprs[idx] = natlit(int(rest[0]))
                elif tag == "#ELS":
                    hx = [h for h in rest if h]        # the empty string has no bytes
                    exprs[idx] = strlit(bytes(int(h, 16) for h in hx).decode("utf-8"))
                else:
                    raise ValueError(f"unknown tag {tag}")
            except Exception as e:
                raise ValueError(f"{path}:{lineno}: {e}\n  {line[:200]}") from e
    return env


def _params(tok, i, N) -> tuple[list, int]:
    n = int(tok[i])
    return [N(x) for x in tok[i + 1:i + 1 + n]], i + 1 + n


def _decl(env: Env, tok: list, N, E):
    head = tok[0]
    if head == "#AX":
        ps, _ = _params(tok, 3, N)
        env.add(Decl("ax", N(tok[1]), E(tok[2]), ps))
    elif head in ("#DEF", "#THM", "#OPAQ"):
        kind = {"#DEF": "def", "#THM": "thm", "#OPAQ": "opaque"}[head]
        ps, _ = _params(tok, 4, N)
        env.add(Decl(kind, N(tok[1]), E(tok[2]), ps, value=E(tok[3])))
    elif head == "#THMTYPE":
        ps, _ = _params(tok, 3, N)
        env.add(Decl("thmtype", N(tok[1]), E(tok[2]), ps))
    elif head == "#QUOT":
        ps, _ = _params(tok, 3, N)
        env.add(Decl("quot", N(tok[1]), E(tok[2]), ps))
    elif head == "#IND":
        name, ty = N(tok[1]), E(tok[2])
        nparams, nindices = int(tok[3]), int(tok[4])
        isrec, isrefl = tok[5] == "1", tok[6] == "1"
        alls, i = _params(tok, 7, N)
        ctors, i = _params(tok, i, N)
        ps, _ = _params(tok, i, N)
        env.add(Decl("ind", name, ty, ps, num_params=nparams, num_indices=nindices,
                     is_rec=isrec, is_reflexive=isrefl, all_names=alls, ctors=ctors))
    elif head == "#CTOR":
        ps, _ = _params(tok, 7, N)
        env.add(Decl("ctor", N(tok[1]), E(tok[2]), ps, induct=N(tok[3]), cidx=int(tok[4]),
                     num_params=int(tok[5]), num_fields=int(tok[6])))
    elif head == "#REC":
        name, ty = N(tok[1]), E(tok[2])
        nparams, nindices = int(tok[3]), int(tok[4])
        nmotives, nminors = int(tok[5]), int(tok[6])
        k = tok[7] == "1"
        alls, i = _params(tok, 8, N)
        nrules = int(tok[i]); i += 1
        rules = []
        for _ in range(nrules):
            rules.append((N(tok[i]), int(tok[i + 1]), E(tok[i + 2])))
            i += 3
        ps, _ = _params(tok, i, N)
        env.add(Decl("rec", name, ty, ps, num_params=nparams, num_indices=nindices,
                     num_motives=nmotives, num_minors=nminors, k=k, all_names=alls,
                     rules=rules))
    else:
        raise ValueError(f"unknown declaration {head}")
