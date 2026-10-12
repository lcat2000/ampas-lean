"""AMPAS independent kernel: type checker.

Implements the type theory Lean's kernel implements — dependent function
types, universe-polymorphic sorts with the imax rule, inductive families via
their recursors (iota), structure projections, let (zeta), beta, delta,
definitional proof irrelevance, definitional eta (functions and structures),
K-like reduction for subsingleton eliminators, Nat literal arithmetic and
the quotient rules — written here from those rules rather than from Lean's
code.

What it establishes: every exported declaration is well-typed, and every
definition's and theorem's value has its declared type. What it assumes (and
reports): the inductive declarations themselves, i.e. that each #IND/#CTOR
/#REC triple is a legitimate inductive specification (positivity, the shape
of the generated recursor and its rules). Constructor and recursor types,
and every recursor rule's right-hand side, ARE type-checked here, so a rule
with an ill-typed body is caught; what is not re-derived is that the
recursor is the one the inductive specification would generate.
"""
from __future__ import annotations

from .parse import Decl, Env
from .terms import (APP, BVAR, CONST, FVAR, LAM, LET, NATLIT, PI, PROJ, SORT, STRLIT,
                    Expr, Level, Name, ZERO, app, apps, bvar, const, elet, expr_level_subst,
                    fvar, instantiate, instantiate1, is_definitely_zero, lam,
                    level_eq, level_subst, levels_eq, limax, natlit, pi, proj, sort, strlit,
                    succ, unfold_apps)


class TypeError_(Exception):
    pass


def _n(*parts) -> Name:
    out = Name.anonymous()
    for p in parts:
        out = out.child(p)
    return out


NAT = _n("Nat")
NAT_ZERO = _n("Nat", "zero")
NAT_SUCC = _n("Nat", "succ")
STRING = _n("String")
BOOL_TRUE = _n("Bool", "true")
BOOL_FALSE = _n("Bool", "false")
QUOT = _n("Quot")
QUOT_MK = _n("Quot", "mk")
QUOT_LIFT = _n("Quot", "lift")
QUOT_IND = _n("Quot", "ind")

# Nat operations the kernel evaluates on literals
_NAT_BIN = {
    _n("Nat", "add"): lambda a, b: a + b,
    _n("Nat", "sub"): lambda a, b: a - b if a > b else 0,
    _n("Nat", "mul"): lambda a, b: a * b,
    _n("Nat", "div"): lambda a, b: a // b if b else 0,
    _n("Nat", "mod"): lambda a, b: a % b if b else a,
    _n("Nat", "pow"): lambda a, b: a ** b,
    _n("Nat", "gcd"): None,       # handled separately (recursive)
    _n("Nat", "land"): lambda a, b: a & b,
    _n("Nat", "lor"): lambda a, b: a | b,
    _n("Nat", "xor"): lambda a, b: a ^ b,
    _n("Nat", "shiftLeft"): lambda a, b: a << b,
    _n("Nat", "shiftRight"): lambda a, b: a >> b,
}
_NAT_PRED = {
    _n("Nat", "beq"): lambda a, b: a == b,
    _n("Nat", "ble"): lambda a, b: a <= b,
}


class Checker:
    def __init__(self, env: Env, allow_unchecked_inductives: bool = True):
        self.env = env
        self.allow_unchecked_inductives = allow_unchecked_inductives
        self.fv_types: dict = {}
        self._next_fv = 0
        self._whnf_cache: dict = {}
        self._infer_cache: dict = {}
        self._defeq_cache: dict = {}
        self.stats = {"declarations": 0, "inductive_specs_assumed": 0}

    # ---------------------------------------------------------------- helpers
    def fresh(self, ty: Expr) -> Expr:
        i = self._next_fv
        self._next_fv += 1
        x = fvar(i)
        self.fv_types[i] = ty
        return x

    def abstract(self, e: Expr, x: Expr, depth: int = 0) -> Expr:
        """Replace the free variable x by BVar(depth)."""
        k = e.kind
        if k == FVAR:
            return bvar(depth) if e is x else e
        if k == APP:
            return app(self.abstract(e.a, x, depth), self.abstract(e.b, x, depth))
        if k == LAM:
            return lam(e.name, self.abstract(e.a, x, depth), self.abstract(e.b, x, depth + 1))
        if k == PI:
            return pi(e.name, self.abstract(e.a, x, depth), self.abstract(e.b, x, depth + 1))
        if k == LET:
            return elet(e.name, self.abstract(e.a, x, depth), self.abstract(e.b, x, depth),
                        self.abstract(e.c, x, depth + 1))
        if k == PROJ:
            return proj(e.name, e.idx, self.abstract(e.a, x, depth))
        return e

    def inst_decl_type(self, d: Decl, lvls) -> Expr:
        if len(lvls) != len(d.lvl_params):
            raise TypeError_(f"{d.name}: expected {len(d.lvl_params)} universe arguments, "
                             f"got {len(lvls)}")
        if not d.lvl_params:
            return d.type
        return expr_level_subst(d.type, dict(zip(d.lvl_params, lvls)))

    def inst_decl_value(self, d: Decl, lvls) -> Expr:
        if not d.lvl_params:
            return d.value
        return expr_level_subst(d.value, dict(zip(d.lvl_params, lvls)))

    # ---------------------------------------------------------------- whnf
    def whnf(self, e: Expr) -> Expr:
        got = self._whnf_cache.get(e)
        if got is not None:
            return got
        out = self._whnf_core(e)
        self._whnf_cache[e] = out
        return out

    def _whnf_core(self, e: Expr) -> Expr:
        cur = e
        while True:
            k = cur.kind
            if k == LET:
                cur = instantiate1(cur.c, cur.b)
                continue
            if k in (APP, CONST, PROJ):
                head, args = unfold_apps(cur)
                hk = head.kind
                if hk == LAM and args:
                    cur = self._beta(head, args)
                    continue
                if hk == LET:
                    cur = apps(instantiate1(head.c, head.b), args)
                    continue
                if hk == PROJ:
                    # a projection can be the head of an application: a class
                    # method such as LE.le unfolds to one
                    red = self._reduce_proj(head)
                    if red is None:
                        return cur
                    cur = apps(red, args)
                    continue
                if hk == CONST:
                    red = self._reduce_const(head, args)
                    if red is not None:
                        cur = red
                        continue
                return cur
            return cur

    @staticmethod
    def _beta(head: Expr, args: list) -> Expr:
        n = 0
        f = head
        vals = []
        while f.kind == LAM and n < len(args):
            vals.append(args[n])
            f = f.b
            n += 1
        body = instantiate(f, list(reversed(vals)))
        return apps(body, args[n:])

    def _reduce_proj(self, e: Expr) -> Expr | None:
        s = self.whnf(e.a)
        head, args = unfold_apps(s)
        if head.kind != CONST:
            return None
        d = self.env.get(head.name)
        if d is None or d.kind != "ctor":
            return None
        start = len(args) - d.num_fields
        i = start + e.idx
        if i < 0 or i >= len(args):
            return None
        return args[i]

    def _reduce_const(self, head: Expr, args: list) -> Expr | None:
        name = head.name
        d = self.env.get(name)
        if d is None:
            return None
        if d.kind == "rec":
            return self._reduce_rec(d, head, args)
        if d.kind in ("quot",):
            return self._reduce_quot(name, args)
        if name in _NAT_BIN or name in _NAT_PRED or name == NAT_SUCC:
            red = self._reduce_nat(name, args)
            if red is not None:
                return red
        if d.kind in ("def", "thm"):
            # delta: unfold a definition or a theorem (both carry a value whose
            # type is the declared type). Axioms and opaque constants do not
            # unfold.
            val = self.inst_decl_value(d, list(head.lvls))
            return apps(val, args)
        return None

    def _reduce_nat(self, name: Name, args: list) -> Expr | None:
        if name == NAT_SUCC and len(args) == 1:
            a = self.whnf(args[0])
            if a.kind == NATLIT:
                return natlit(a.val + 1)
            return None
        if len(args) < 2:
            return None
        a, b = self.whnf(args[0]), self.whnf(args[1])
        if a.kind != NATLIT or b.kind != NATLIT:
            return None
        extra = args[2:]
        if name in _NAT_PRED:
            v = _NAT_PRED[name](a.val, b.val)
            return apps(const(BOOL_TRUE if v else BOOL_FALSE, []), extra)
        f = _NAT_BIN.get(name)
        if f is None:
            if name == _n("Nat", "gcd"):
                import math
                return apps(natlit(math.gcd(a.val, b.val)), extra)
            return None
        return apps(natlit(f(a.val, b.val)), extra)

    @staticmethod
    def _nat_to_ctor(e: Expr) -> Expr:
        if e.kind == NATLIT:
            if e.val == 0:
                return const(NAT_ZERO, [])
            return app(const(NAT_SUCC, []), natlit(e.val - 1))
        return e

    def _to_ctor_when_k(self, d: Decl, major: Expr) -> Expr:
        """K-like reduction: for an eliminator over a subsingleton inductive
        with a single, field-free constructor (Eq and friends), the major
        premise may be replaced by that constructor built from its type's
        parameters -- but ONLY when that constructor really has the major
        premise's type. Without this last check the rule would make any two
        things definitionally equal as soon as an equality proof exists."""
        ty = self.whnf(self.infer(major))
        head, targs = unfold_apps(ty)
        if head.kind != CONST:
            return major
        if d.all_names and head.name is not d.all_names[0]:
            return major
        ind = self.env.get(head.name)
        if ind is None or ind.kind != "ind" or len(ind.ctors) != 1:
            return major
        ctor = self.env.get(ind.ctors[0])
        if ctor is None or ctor.num_fields != 0:
            return major
        if len(targs) < ctor.num_params:
            return major
        # the constructor takes exactly the inductive's parameters
        ctor_app = apps(const(ctor.name, list(head.lvls)), targs[:ctor.num_params])
        try:
            if not self.is_def_eq(self.infer(ctor_app), ty):
                return major
        except TypeError_:
            return major
        return ctor_app

    def _reduce_rec(self, d: Decl, head: Expr, args: list) -> Expr | None:
        major_idx = d.num_params + d.num_motives + d.num_minors + d.num_indices
        if len(args) <= major_idx:
            return None
        major = self.whnf(args[major_idx])
        major = self._nat_to_ctor(major)
        if d.k:
            major = self._to_ctor_when_k(d, major)
        mhead, margs = unfold_apps(major)
        if mhead.kind != CONST:
            return None
        rule = None
        for (cname, nfields, rhs) in d.rules:
            if cname is mhead.name:
                rule = (cname, nfields, rhs)
                break
        if rule is None:
            return None
        _, nfields, rhs = rule
        if len(margs) < nfields:
            return None
        if len(head.lvls) != len(d.lvl_params):
            return None
        if d.lvl_params:
            rhs = expr_level_subst(rhs, dict(zip(d.lvl_params, list(head.lvls))))
        # the rule's right-hand side is a closed term abstracted over the
        # recursor's parameters, motives and minor premises, then the
        # constructor's fields; the indices are not among its binders
        take = d.num_params + d.num_motives + d.num_minors
        fields = margs[len(margs) - nfields:]
        out = apps(rhs, list(args[:take]) + list(fields))
        return apps(out, args[major_idx + 1:])

    def _reduce_quot(self, name: Name, args: list) -> Expr | None:
        # Quot.lift f h (Quot.mk r a)  ==>  f a
        # Quot.ind  p   (Quot.mk r a)  ==>  p a
        if name is QUOT_LIFT:
            arg_i, f_i = 5, 3
        elif name is QUOT_IND:
            arg_i, f_i = 4, 3
        else:
            return None
        if len(args) <= arg_i:
            return None
        mk = self.whnf(args[arg_i])
        mh, margs = unfold_apps(mk)
        if mh.kind != CONST or mh.name is not QUOT_MK or len(margs) != 3:
            return None
        out = app(args[f_i], margs[2])
        return apps(out, args[arg_i + 1:])

    # ---------------------------------------------------------------- defeq
    def is_def_eq(self, a: Expr, b: Expr) -> bool:
        if a is b:
            return True
        key = (a, b)
        got = self._defeq_cache.get(key)
        if got is not None:
            return got
        out = self._def_eq_core(a, b)
        self._defeq_cache[key] = out
        return out

    def _def_eq_core(self, a: Expr, b: Expr) -> bool:
        a, b = self.whnf(a), self.whnf(b)
        if a is b:
            return True
        ka, kb = a.kind, b.kind
        if ka == SORT and kb == SORT:
            return level_eq(a.a, b.a)
        if ka == NATLIT and kb == NATLIT:
            return a.val == b.val
        if ka == STRLIT and kb == STRLIT:
            return a.val == b.val
        # Nat literals against successor/zero form
        if ka == NATLIT or kb == NATLIT:
            if self._def_eq_nat_mixed(a, b):
                return True
        # two different free variables are not structurally equal, but they
        # may still be equal by proof irrelevance, so do not return here
        if ka == PI and kb == PI:
            if self.is_def_eq(a.a, b.a):
                x = self.fresh(a.a)
                if self.is_def_eq(instantiate1(a.b, x), instantiate1(b.b, x)):
                    return True
            return False
        if ka == LAM and kb == LAM:
            if self.is_def_eq(a.a, b.a):
                x = self.fresh(a.a)
                if self.is_def_eq(instantiate1(a.b, x), instantiate1(b.b, x)):
                    return True
            # the domains may differ while both sides are proofs of one
            # proposition, so fall through to proof irrelevance below
        # eta for functions
        if ka == LAM and kb != LAM:
            x = self.fresh(a.a)
            return self.is_def_eq(instantiate1(a.b, x), app(b, x))
        if kb == LAM and ka != LAM:
            x = self.fresh(b.a)
            return self.is_def_eq(app(a, x), instantiate1(b.b, x))
        if self._def_eq_app(a, b):
            return True
        if ka == PROJ and kb == PROJ and a.idx == b.idx and a.name is b.name:
            if self.is_def_eq(a.a, b.a):
                return True
        # definitional proof irrelevance
        if self._proof_irrel(a, b):
            return True
        # structure eta
        if self._struct_eta(a, b) or self._struct_eta(b, a):
            return True
        return False

    def _def_eq_app(self, a: Expr, b: Expr) -> bool:
        ha, aa = unfold_apps(a)
        hb, ab = unfold_apps(b)
        if len(aa) != len(ab):
            return False
        if ha.kind == CONST and hb.kind == CONST:
            if ha.name is not hb.name or not levels_eq(list(ha.lvls), list(hb.lvls)):
                return False
        elif ha.kind == FVAR and hb.kind == FVAR:
            if ha is not hb:
                return False
        elif ha.kind == PROJ and hb.kind == PROJ:
            if not (ha.idx == hb.idx and ha.name is hb.name and self.is_def_eq(ha.a, hb.a)):
                return False
        else:
            return False
        if not aa:
            return True
        return all(self.is_def_eq(x, y) for x, y in zip(aa, ab))

    def _def_eq_nat_mixed(self, a: Expr, b: Expr) -> bool:
        lit, other = (a, b) if a.kind == NATLIT else (b, a)
        h, args = unfold_apps(other)
        if h.kind == CONST and h.name is NAT_ZERO and not args:
            return lit.val == 0
        if h.kind == CONST and h.name is NAT_SUCC and len(args) == 1:
            if lit.val == 0:
                return False
            return self.is_def_eq(natlit(lit.val - 1), args[0])
        return False

    def _is_prop(self, e: Expr) -> bool:
        ty = self.whnf(self.infer(e))
        return ty.kind == SORT and is_definitely_zero(ty.a)

    def _proof_irrel(self, a: Expr, b: Expr) -> bool:
        try:
            ta = self.infer(a)
        except TypeError_:
            return False
        tta = self.whnf(self.infer(ta))
        if not (tta.kind == SORT and is_definitely_zero(tta.a)):
            return False
        try:
            tb = self.infer(b)
        except TypeError_:
            return False
        return self.is_def_eq(ta, tb)

    def _struct_eta(self, a: Expr, b: Expr) -> bool:
        """a is a constructor application of a structure and b is not: equal
        when b's projections match a's fields."""
        ha, aargs = unfold_apps(a)
        if ha.kind != CONST:
            return False
        ctor = self.env.get(ha.name)
        if ctor is None or ctor.kind != "ctor":
            return False
        ind = self.env.get(ctor.induct)
        if ind is None or len(ind.ctors) != 1 or ind.num_indices != 0:
            return False
        if len(aargs) != ctor.num_params + ctor.num_fields:
            return False
        hb, _ = unfold_apps(b)
        if hb.kind == CONST and hb.name is ha.name:
            return False
        try:
            tb = self.whnf(self.infer(b))
        except TypeError_:
            return False
        hbt, _ = unfold_apps(tb)
        if hbt.kind != CONST or hbt.name is not ctor.induct:
            return False
        fields = aargs[ctor.num_params:]
        for i, f in enumerate(fields):
            if not self.is_def_eq(f, proj(ctor.induct, i, b)):
                return False
        return True

    # ---------------------------------------------------------------- infer
    def infer(self, e: Expr) -> Expr:
        got = self._infer_cache.get(e)
        if got is not None:
            return got
        out = self._infer_core(e)
        self._infer_cache[e] = out
        return out

    def _infer_core(self, e: Expr) -> Expr:
        k = e.kind
        if k == FVAR:
            ty = self.fv_types.get(e.idx)
            if ty is None:
                raise TypeError_(f"unknown free variable {e!r}")
            return ty
        if k == BVAR:
            raise TypeError_(f"loose de Bruijn variable {e!r}")
        if k == SORT:
            return sort(succ(e.a))
        if k == NATLIT:
            return const(NAT, [])
        if k == STRLIT:
            return const(STRING, [])
        if k == CONST:
            d = self.env.get(e.name)
            if d is None:
                raise TypeError_(f"unknown constant {e.name}")
            return self.inst_decl_type(d, list(e.lvls))
        if k == APP:
            fty = self.ensure_pi(self.infer(e.a))
            aty = self.infer(e.b)
            if not self.is_def_eq(aty, fty.a):
                raise TypeError_(
                    f"argument type mismatch applying {e.a!r}:\n"
                    f"  expected {fty.a!r}\n  got      {aty!r}")
            return instantiate1(fty.b, e.b)
        if k == LAM:
            self.ensure_sort(self.infer(e.a))
            x = self.fresh(e.a)
            bty = self.infer(instantiate1(e.b, x))
            return pi(e.name, e.a, self.abstract(bty, x))
        if k == PI:
            u = self.ensure_sort(self.infer(e.a))
            x = self.fresh(e.a)
            v = self.ensure_sort(self.infer(instantiate1(e.b, x)))
            return sort(limax(u, v))
        if k == LET:
            self.ensure_sort(self.infer(e.a))
            vty = self.infer(e.b)
            if not self.is_def_eq(vty, e.a):
                raise TypeError_(f"let value type mismatch:\n  expected {e.a!r}\n  got {vty!r}")
            return self.infer(instantiate1(e.c, e.b))
        if k == PROJ:
            return self._infer_proj(e)
        raise TypeError_(f"cannot infer the type of {e!r}")

    def ensure_sort(self, ty: Expr) -> Level:
        t = self.whnf(ty)
        if t.kind != SORT:
            raise TypeError_(f"a type was expected, got {ty!r}")
        return t.a

    def ensure_pi(self, ty: Expr) -> Expr:
        t = self.whnf(ty)
        if t.kind != PI:
            raise TypeError_(f"a function type was expected, got {ty!r}")
        return t

    def _infer_proj(self, e: Expr) -> Expr:
        sty = self.whnf(self.infer(e.a))
        head, targs = unfold_apps(sty)
        if head.kind != CONST or head.name is not e.name:
            raise TypeError_(f"projection {e!r}: the value is not of structure {e.name}")
        ind = self.env.get(e.name)
        if ind is None or ind.kind != "ind" or len(ind.ctors) != 1:
            raise TypeError_(f"projection {e!r}: {e.name} is not a structure")
        ctor = self.env.get(ind.ctors[0])
        cty = self.inst_decl_type(ctor, list(head.lvls))
        # instantiate the constructor's parameters with the structure's
        for i in range(ctor.num_params):
            cty = self.ensure_pi(cty)
            if i >= len(targs):
                raise TypeError_(f"projection {e!r}: missing structure parameters")
            cty = instantiate1(cty.b, targs[i])
        # walk the fields, replacing earlier ones by projections of the value
        for i in range(e.idx):
            cty = self.ensure_pi(cty)
            cty = instantiate1(cty.b, proj(e.name, i, e.a))
        cty = self.ensure_pi(cty)
        return cty.a

    # ---------------------------------------------------------------- decls
    def check_decl(self, d: Decl) -> None:
        if len(set(d.lvl_params)) != len(d.lvl_params):
            raise TypeError_(f"{d.name}: repeated universe parameter")
        self.ensure_sort(self.infer(d.type))
        if d.kind in ("def", "thm", "opaque"):
            vty = self.infer(d.value)
            if not self.is_def_eq(vty, d.type):
                raise TypeError_(
                    f"{d.name}: the value does not have the declared type\n"
                    f"  declared {d.type!r}\n  inferred {vty!r}")
        elif d.kind == "ctor":
            ind = self.env.get(d.induct)
            if ind is None or ind.kind != "ind":
                raise TypeError_(f"{d.name}: constructor of unknown inductive {d.induct}")
            ty = d.type
            for _ in range(d.num_params + d.num_fields):
                ty = self.ensure_pi(ty)
                ty = instantiate1(ty.b, self.fresh(ty.a))
            head, _ = unfold_apps(self.whnf(ty))
            if head.kind != CONST or head.name is not d.induct:
                raise TypeError_(f"{d.name}: does not construct {d.induct}")
            self.stats["inductive_specs_assumed"] += 1
        elif d.kind == "rec":
            for (cname, nfields, rhs) in d.rules:
                ctor = self.env.get(cname)
                if ctor is None or ctor.kind != "ctor":
                    raise TypeError_(f"{d.name}: rule for unknown constructor {cname}")
                if ctor.num_fields != nfields:
                    raise TypeError_(f"{d.name}: rule for {cname} declares {nfields} fields, "
                                     f"the constructor has {ctor.num_fields}")
                # the right-hand side is closed, so it is type-checked here:
                # a rule with an ill-typed body is caught
                if rhs.loose != 0:
                    raise TypeError_(f"{d.name}: rule for {cname} is not closed")
                self.infer(rhs)
            self.stats["inductive_specs_assumed"] += 1
        elif d.kind in ("ind", "ax", "quot"):
            if d.kind == "ind":
                self.stats["inductive_specs_assumed"] += 1
        self.stats["declarations"] += 1


def check_env(env: Env, progress=None) -> dict:
    ch = Checker(env)
    errors = []
    for i, name in enumerate(env.order):
        d = env.decls[name]
        try:
            ch.check_decl(d)
        except TypeError_ as ex:
            errors.append((name.str, str(ex)))
        except RecursionError:
            errors.append((name.str, "recursion limit while checking"))
        if progress and i % 50 == 0:
            progress(i, len(env.order), name)
    return {"checked": ch.stats["declarations"], "total": len(env.order),
            "inductive_specs_assumed": ch.stats["inductive_specs_assumed"],
            "errors": errors}
