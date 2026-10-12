"""AMPAS independent kernel: names, universe levels and terms.

Written from the rules of Lean's type theory (dependent type theory with
universe polymorphism, inductive families, proof irrelevance, definitional
eta, and literal/quotient reduction). It shares no code with Lean; the only
thing taken from Lean is the exported declarations themselves.

Terms are hash-consed, so structurally equal terms are the same object and
caches can be keyed on identity.
"""
from __future__ import annotations

from typing import Optional

# ---------------------------------------------------------------- names
class Name:
    __slots__ = ("parts", "_h", "_s")
    _intern: dict = {}

    def __init__(self, parts: tuple):
        self.parts = parts
        self._h = hash(parts)
        self._s = ".".join(str(p) for p in parts) if parts else "[anonymous]"

    @staticmethod
    def mk(parts: tuple) -> "Name":
        got = Name._intern.get(parts)
        if got is None:
            got = Name(parts)
            Name._intern[parts] = got
        return got

    @staticmethod
    def anonymous() -> "Name":
        return Name.mk(())

    def child(self, part) -> "Name":
        return Name.mk(self.parts + (part,))

    def __hash__(self):
        return self._h

    def __eq__(self, other):
        return self is other

    def __repr__(self):
        return self._s

    @property
    def str(self) -> str:
        return self._s


# ---------------------------------------------------------------- levels
class Level:
    __slots__ = ("kind", "a", "b", "name", "_h")
    _intern: dict = {}

    def __init__(self, kind, a=None, b=None, name=None):
        self.kind, self.a, self.b, self.name = kind, a, b, name
        self._h = hash((kind, id(a), id(b), id(name)))

    @staticmethod
    def _mk(kind, a=None, b=None, name=None) -> "Level":
        key = (kind, id(a), id(b), id(name))
        got = Level._intern.get(key)
        if got is None:
            got = Level(kind, a, b, name)
            Level._intern[key] = got
        return got

    def __hash__(self):
        return self._h

    def __eq__(self, other):
        return self is other

    def __repr__(self):
        k = self.kind
        if k == "zero":
            return "0"
        if k == "succ":
            return f"({self.a!r}+1)"
        if k == "max":
            return f"max({self.a!r},{self.b!r})"
        if k == "imax":
            return f"imax({self.a!r},{self.b!r})"
        return f"{self.name!r}"


ZERO = Level._mk("zero")


def succ(l: Level) -> Level:
    return Level._mk("succ", l)


def lmax(a: Level, b: Level) -> Level:
    return Level._mk("max", a, b)


def limax(a: Level, b: Level) -> Level:
    return Level._mk("imax", a, b)


def param(n: Name) -> Level:
    return Level._mk("param", name=n)


def level_subst(l: Level, s: dict) -> Level:
    """Substitute level parameters (Name -> Level)."""
    k = l.kind
    if k == "zero":
        return l
    if k == "succ":
        a = level_subst(l.a, s)
        return l if a is l.a else succ(a)
    if k == "max":
        a, b = level_subst(l.a, s), level_subst(l.b, s)
        return l if (a is l.a and b is l.b) else lmax(a, b)
    if k == "imax":
        a, b = level_subst(l.a, s), level_subst(l.b, s)
        return l if (a is l.a and b is l.b) else limax(a, b)
    return s.get(l.name, l)


def _offset(l: Level) -> tuple[Level, int]:
    n = 0
    while l.kind == "succ":
        l = l.a
        n += 1
    return l, n


def _never_zero_raw(l: Level) -> bool:
    """Provably greater than zero, without re-simplifying (used by simplify)."""
    k = l.kind
    if k == "succ":
        return True
    if k == "max":
        return _never_zero_raw(l.a) or _never_zero_raw(l.b)
    if k == "imax":
        return _never_zero_raw(l.b)
    return False


def _mk_max(a: Level, b: Level) -> Level:
    if a is b:
        return a
    if a.kind == "zero":
        return b
    if b.kind == "zero":
        return a
    # fold a chain of successors over zero on both sides
    ba, na = _offset(a)
    bb, nb = _offset(b)
    if ba.kind == "zero" and bb.kind == "zero":
        return a if na >= nb else b
    if ba is bb:
        return a if na >= nb else b
    return lmax(a, b)


def simplify(l: Level) -> Level:
    """Push imax towards max/zero where its shape is already determined, and
    collapse the easy max cases."""
    k = l.kind
    if k in ("zero", "param"):
        return l
    if k == "succ":
        return succ(simplify(l.a))
    if k == "max":
        return _mk_max(simplify(l.a), simplify(l.b))
    # imax
    a, b = simplify(l.a), simplify(l.b)
    if b.kind == "zero":
        return ZERO                      # imax u 0 = 0
    if _never_zero_raw(b):
        return _mk_max(a, b)             # imax u v = max u v when v > 0
    if a is b:
        return a                         # imax u u = u
    if a.kind == "zero":
        return b                         # imax 0 v = v
    return limax(a, b)


def _params(l: Level, acc: set):
    k = l.kind
    if k == "param":
        acc.add(l.name)
    elif k == "succ":
        _params(l.a, acc)
    elif k in ("max", "imax"):
        _params(l.a, acc)
        _params(l.b, acc)


def level_params(l: Level) -> set:
    acc: set = set()
    _params(l, acc)
    return acc


def level_leq(a: Level, b: Level, diff: int = 0) -> bool:
    """a <= b + diff. Successors are stripped first, then max is distributed,
    then an imax whose second argument is a parameter is decided by splitting
    that parameter into 0 and succ. Atoms that do not match are not <=, which
    is the conservative answer."""
    a, b = simplify(a), simplify(b)
    if a is b and diff >= 0:
        return True
    if a.kind == "zero" and diff >= 0:
        return True
    if a.kind == "succ":
        return level_leq(a.a, b, diff - 1)
    if b.kind == "succ":
        return level_leq(a, b.a, diff + 1)
    if a.kind == "max":
        return level_leq(a.a, b, diff) and level_leq(a.b, b, diff)
    if b.kind == "max":
        return level_leq(a, b.a, diff) or level_leq(a, b.b, diff)
    if a.kind == "imax" and a.b.kind == "param":
        return _split(a.b.name, a, b, diff)
    if b.kind == "imax" and b.b.kind == "param":
        return _split(b.b.name, a, b, diff)
    if a.kind == "imax":
        return level_leq(a.a, b, diff) and level_leq(a.b, b, diff)
    if b.kind == "imax":
        return level_leq(a, b.b, diff)
    return False


def _split(p: Name, a: Level, b: Level, diff: int) -> bool:
    z = {p: ZERO}
    s = {p: succ(param(p))}
    return (level_leq(level_subst(a, z), level_subst(b, z), diff)
            and level_leq(level_subst(a, s), level_subst(b, s), diff))


def level_eq(a: Level, b: Level) -> bool:
    if a is b:
        return True
    return level_leq(a, b, 0) and level_leq(b, a, 0)


def levels_eq(xs: list, ys: list) -> bool:
    return len(xs) == len(ys) and all(level_eq(x, y) for x, y in zip(xs, ys))


def is_never_zero(l: Level) -> bool:
    """True when the level is provably greater than zero (used to tell a
    Sort apart from Prop)."""
    l = simplify(l)
    if l.kind == "succ":
        return True
    if l.kind == "max":
        return is_never_zero(l.a) or is_never_zero(l.b)
    if l.kind == "imax":
        return is_never_zero(l.b)
    return False


def is_definitely_zero(l: Level) -> bool:
    return simplify(l).kind == "zero"


# ---------------------------------------------------------------- terms
BVAR, FVAR, SORT, CONST, APP, LAM, PI, LET, PROJ, NATLIT, STRLIT = range(11)


class Expr:
    __slots__ = ("kind", "a", "b", "c", "name", "lvls", "idx", "val", "_h", "_loose")
    _intern: dict = {}

    def __init__(self, kind, a=None, b=None, c=None, name=None, lvls=None, idx=0, val=None):
        self.kind, self.a, self.b, self.c = kind, a, b, c
        self.name, self.lvls, self.idx, self.val = name, lvls, idx, val
        self._h = hash((kind, id(a), id(b), id(c), id(name),
                        tuple(id(x) for x in lvls) if lvls else None, idx, val))
        self._loose = None

    @staticmethod
    def _mk(kind, a=None, b=None, c=None, name=None, lvls=None, idx=0, val=None) -> "Expr":
        key = (kind, id(a), id(b), id(c), id(name),
               tuple(id(x) for x in lvls) if lvls else None, idx, val)
        got = Expr._intern.get(key)
        if got is None:
            got = Expr(kind, a, b, c, name, lvls, idx, val)
            Expr._intern[key] = got
        return got

    def __hash__(self):
        return self._h

    def __eq__(self, other):
        return self is other

    def __repr__(self):
        k = self.kind
        if k == BVAR:
            return f"#{self.idx}"
        if k == FVAR:
            return f"fv{self.idx}"
        if k == SORT:
            return f"Sort {self.a!r}"
        if k == CONST:
            return f"{self.name!r}"
        if k == APP:
            return f"({self.a!r} {self.b!r})"
        if k == LAM:
            return f"(fun {self.name!r}:{self.a!r} => {self.b!r})"
        if k == PI:
            return f"(({self.name!r}:{self.a!r}) -> {self.b!r})"
        if k == LET:
            return f"(let {self.name!r} := {self.b!r}; {self.c!r})"
        if k == PROJ:
            return f"{self.a!r}.{self.idx}"
        if k == NATLIT:
            return str(self.val)
        return repr(self.val)

    @property
    def loose(self) -> int:
        """1 + the largest loose de Bruijn index, or 0 if closed."""
        if self._loose is None:
            self._loose = _loose_range(self)
        return self._loose


def bvar(i: int) -> Expr:
    return Expr._mk(BVAR, idx=i)


def fvar(i: int) -> Expr:
    return Expr._mk(FVAR, idx=i)


def sort(l: Level) -> Expr:
    return Expr._mk(SORT, a=l)


def const(n: Name, lvls: list) -> Expr:
    return Expr._mk(CONST, name=n, lvls=tuple(lvls))


def app(f: Expr, a: Expr) -> Expr:
    return Expr._mk(APP, a=f, b=a)


def apps(f: Expr, args) -> Expr:
    for a in args:
        f = app(f, a)
    return f


def lam(n: Name, d: Expr, b: Expr) -> Expr:
    return Expr._mk(LAM, a=d, b=b, name=n)


def pi(n: Name, d: Expr, b: Expr) -> Expr:
    return Expr._mk(PI, a=d, b=b, name=n)


def elet(n: Name, t: Expr, v: Expr, b: Expr) -> Expr:
    return Expr._mk(LET, a=t, b=v, c=b, name=n)


def proj(s: Name, i: int, e: Expr) -> Expr:
    return Expr._mk(PROJ, a=e, name=s, idx=i)


def natlit(n: int) -> Expr:
    return Expr._mk(NATLIT, val=n)


def strlit(s: str) -> Expr:
    return Expr._mk(STRLIT, val=s)


def _loose_range(e: Expr) -> int:
    k = e.kind
    if k == BVAR:
        return e.idx + 1
    if k in (FVAR, SORT, CONST, NATLIT, STRLIT):
        return 0
    if k == APP:
        return max(e.a.loose, e.b.loose)
    if k in (LAM, PI):
        return max(e.a.loose, e.b.loose - 1 if e.b.loose > 0 else 0)
    if k == LET:
        return max(e.a.loose, e.b.loose, e.c.loose - 1 if e.c.loose > 0 else 0)
    if k == PROJ:
        return e.a.loose
    return 0


def instantiate(e: Expr, vals: list, shift: int = 0) -> Expr:
    """Replace loose BVar(shift + i) by vals[i] (vals[0] is the innermost)."""
    if e.loose <= shift:
        return e
    k = e.kind
    if k == BVAR:
        i = e.idx - shift
        if 0 <= i < len(vals):
            return vals[i]
        return e
    if k == APP:
        return app(instantiate(e.a, vals, shift), instantiate(e.b, vals, shift))
    if k == LAM:
        return lam(e.name, instantiate(e.a, vals, shift), instantiate(e.b, vals, shift + 1))
    if k == PI:
        return pi(e.name, instantiate(e.a, vals, shift), instantiate(e.b, vals, shift + 1))
    if k == LET:
        return elet(e.name, instantiate(e.a, vals, shift), instantiate(e.b, vals, shift),
                    instantiate(e.c, vals, shift + 1))
    if k == PROJ:
        return proj(e.name, e.idx, instantiate(e.a, vals, shift))
    return e


def instantiate1(e: Expr, v: Expr) -> Expr:
    return instantiate(e, [v])


def expr_level_subst(e: Expr, s: dict) -> Expr:
    """Substitute universe parameters throughout a term."""
    if not s:
        return e
    k = e.kind
    if k == SORT:
        l = level_subst(e.a, s)
        return e if l is e.a else sort(l)
    if k == CONST:
        ls = [level_subst(l, s) for l in e.lvls]
        return e if all(x is y for x, y in zip(ls, e.lvls)) else const(e.name, ls)
    if k == APP:
        return app(expr_level_subst(e.a, s), expr_level_subst(e.b, s))
    if k == LAM:
        return lam(e.name, expr_level_subst(e.a, s), expr_level_subst(e.b, s))
    if k == PI:
        return pi(e.name, expr_level_subst(e.a, s), expr_level_subst(e.b, s))
    if k == LET:
        return elet(e.name, expr_level_subst(e.a, s), expr_level_subst(e.b, s),
                    expr_level_subst(e.c, s))
    if k == PROJ:
        return proj(e.name, e.idx, expr_level_subst(e.a, s))
    return e


def unfold_apps(e: Expr) -> tuple[Expr, list]:
    """Head and argument list (left to right)."""
    args = []
    while e.kind == APP:
        args.append(e.b)
        e = e.a
    args.reverse()
    return e, args
