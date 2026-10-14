"""Iota rules — the third and last of `kernel3`'s assumed properties.

ROADMAP 2c. `harness/kernel3/positivity.py` closed the first, and
`harness/kernel3/recursor.py` the second: it counts the iota rules and checks
which constructor each belongs to. Neither looks at what a rule *computes*. A
forged right-hand side — one that returns the wrong minor premise, drops a
recursive call, or passes a constructor's fields in the wrong order — is
accepted on its specification by both, and caught only by the provenance gate.

This pass re-derives each rule's right-hand side from the constructor and the
recursor, and compares it to the stored one. For a constructor `c` of family
member `I` with parameters `p`, motives `m`, minor premises `n` and fields `f`:

    λ p… m… n… f…, nᶜ f₀ … f_{k-1} rec₀ … rec_{j-1}

where `nᶜ` is the minor premise for `c` — its position fixed by `c`'s index in
the family's constructor order — and one recursive call follows per *recursive*
field, in field order:

    λ b…, I.rec levels p… m… n… (indices of that field's type) (fᵢ b…)

The recursive call carries the recursor's own universe parameters, not fresh
ones. The reason to build the term and α-compare rather than interrogate the
stored one piecewise is that a piecewise check tests the properties you
thought of; a derivation tests the rule.

**Why this is the riskiest of the three, and what follows from that.**
Re-deriving a recursor's rules is close to generating the recursor, so the pass
is doing the kernel's own work and a bug in its de Bruijn arithmetic rejects
valid code. It therefore follows the same discipline as the other two, with
the differential test over the sets Lean itself generated these rules for
carrying most of the weight, and it CLASSIFIES rather than judges: a rule
whose expected form this pass cannot build comes back `UNCLASSIFIED`, never
`OK`. It changes no verdict, and `kernel3`'s provenance gate is untouched.

**Where it declines.** Nested inductives (whose auxiliary recursors have more
motives than family members), reflexive fields whose recursive call shape this
pass does not model, and anything whose binder structure does not match the
expected prefix. Those are counted by cause in the differential record.

**What remains assumed even with all three passes clean.** That the
*declaration set* is the one Lean produced. These three passes check an
inductive's specification against the rules Lean would have followed; they do
not establish that the export came from Lean at all. That is what the
provenance gate is for, and ASSUMPTIONS A3 is written against that boundary,
not against this one.
"""
from __future__ import annotations

from .positivity import occurs
from .terms import Expr, bvar, const, apps, param

# Imported, never restated.
from .terms import BVAR, CONST, APP, LAM, PI, LET  # noqa: E402

NOT_IN_EXPORT = "NOT_IN_EXPORT"
NESTED = "NESTED_AUXILIARY_RECURSOR"
AMBIGUOUS_FIELD = "RECURSIVENESS_NEEDS_REDUCTION"

# Elaboration gadgets. `optParam α d` and `autoParam α tac` are both
# definitionally `α` -- they carry a default value and a tactic for the
# elaborator, and the kernel unfolds them away. Lean strips them when it
# generates a recursor's rule binders, so the derivation has to strip them too
# or every structure with a defaulted field reads as forged (12 autoParam and 3
# optParam cases in Lean's own Init alone).
#
# Stripped on the DERIVED side only, never on the stored one: that way a rule
# that drops a gadget Lean also drops is accepted, while a rule that ADDS one
# is still a violation. A symmetric strip would be a quiet widening -- it would
# stop the comparison seeing a wrapper a forgery introduced.
GADGETS = ("optParam", "autoParam")


def _lams(e: Expr) -> tuple[list, Expr]:
    doms = []
    while e.kind == LAM:
        doms.append(e.a)
        e = e.b
    return doms, e


def _telescope(e: Expr) -> tuple[list, Expr]:
    doms = []
    while e.kind == PI:
        doms.append(e.a)
        e = e.b
    return doms, e


def _head_and_args(e: Expr) -> tuple[Expr, list]:
    args = []
    while e.kind == APP:
        args.append(e.b)
        e = e.a
    args.reverse()
    return e, args


def alpha_eq(a: Expr, b: Expr) -> bool:
    """Structural equality ignoring binder names.

    `Expr` interns on the binder name too and compares by identity, so two
    terms that differ only in a binder's name are different objects. Lean's
    own names for a constructor's fields are not part of the rule's meaning —
    `Or.inl`'s field is called `a._@._internal._hyg.0` in one rule and `h` in
    the next — so a name-sensitive comparison would report every rule forged.
    """
    if a is b:
        return True
    if a is None or b is None or a.kind != b.kind:
        return False
    k = a.kind
    if k == BVAR:
        return a.idx == b.idx
    if k == CONST:
        return a.name is b.name and list(a.lvls or []) == list(b.lvls or [])
    if k in (APP, LAM, PI):
        return alpha_eq(a.a, b.a) and alpha_eq(a.b, b.b)
    if k == LET:
        return (alpha_eq(a.a, b.a) and alpha_eq(a.b, b.b)
                and alpha_eq(a.c, b.c))
    if k == PROJ:
        return a.idx == b.idx and alpha_eq(a.a, b.a)
    # SORT / NATLIT / STRLIT / FVAR
    return (a.a is b.a and a.b is b.b and a.idx == b.idx and a.val == b.val)


def relabel(e: Expr, move, depth: int = 0) -> Expr:
    """Rewrite free de Bruijn indices through `move`.

    `move(k)` takes a free index relative to the term's own enclosing context
    and returns its index in the target context. Indices bound inside `e` are
    left alone, which is what `depth` tracks.
    """
    k = e.kind
    if k == BVAR:
        if e.idx < depth:
            return e
        return bvar(move(e.idx - depth) + depth)
    if k == APP:
        return Expr._mk(APP, a=relabel(e.a, move, depth), b=relabel(e.b, move, depth))
    if k in (LAM, PI):
        return Expr._mk(k, a=relabel(e.a, move, depth),
                        b=relabel(e.b, move, depth + 1), name=e.name)
    if k == LET:
        # a = type, b = value, c = body under one more binder. Omitting this
        # case left every index inside a `let` unrewritten, and six of Lean's
        # own structures have a field whose type opens with one.
        return Expr._mk(LET, a=relabel(e.a, move, depth),
                        b=relabel(e.b, move, depth),
                        c=relabel(e.c, move, depth + 1), name=e.name)
    return e


def strip_gadgets(e: Expr) -> Expr:
    """Remove `optParam`/`autoParam` wrappers, as Lean does, outermost first.

    Only an application of exactly one of those constants to exactly two
    arguments is unwrapped, and only to its first argument. Nothing else is
    touched, so this cannot swallow a wrapper a forgery introduced under some
    other name.
    """
    while True:
        head, args = _head_and_args(e)
        if (head.kind == CONST and len(args) == 2
                and str(head.name) in GADGETS):
            e = args[0]
            continue
        return e


def _recursive_fields(ctor, family) -> tuple[list, str | None]:
    """((field index, field type, head name)…, reason to decline).

    A field is recursive when its type's conclusion is headed by a member of
    the family. That test is SYNTACTIC, and Lean's is not: Lean decides
    recursiveness after delta-reduction, so a field typed
    `constType (I α) (I α)` -- headed by a DEFINITION that unfolds to expose
    the family -- is recursive to Lean and not to this test.

    The first version of this pass answered "not recursive" there and derived
    a rule with no recursive call, then reported Lean's legitimate rule
    forged. It did that to three of the arena's tests
    (`055_reduceCtorParam.mk`, `119_reduceCtorParamRefl.mk`,
    `120_reduceCtorParamRefl2.mk`), and the 3410-recursor differential over
    Init and Mathlib could not have caught it: neither library has a
    constructor field whose type needs unfolding to reveal its recursion.

    Rather than bring reduction into a pass written to avoid depending on it,
    the ambiguous case DECLINES: a field whose type mentions the family
    anywhere but is not headed by a family member is one this pass cannot
    classify, so there is no derivation to compare against. That turns three
    false rejections into three honest declines, in the direction the pass's
    discipline requires.
    """
    cdoms, _ = _telescope(ctor.type)
    out = []
    for i, f in enumerate(cdoms[ctor.num_params:]):
        _, concl = _telescope(f)
        head, _ = _head_and_args(concl)
        if head.kind == CONST and head.name in family:
            out.append((i, f, head.name))
        elif occurs(f, family):
            return [], (
                f"{AMBIGUOUS_FIELD}: field {i} mentions the inductive family "
                f"but its type is not headed by a family member, so whether "
                f"it is recursive depends on reduction, which this pass does "
                f"not do")
    return out, None


def expected_rhs(rec, ctor, minor_index: int, env, family):
    """Build the right-hand side Lean's recursor would have for this rule.

    Returns (Expr, None) or (None, reason) when this pass cannot build it.
    """
    P, M, N = rec.num_params, rec.num_motives, rec.num_minors
    cdoms, _ = _telescope(ctor.type)
    fields = cdoms[ctor.num_params:]
    K = len(fields)
    T = P + M + N + K

    def rule_pos(ctor_pos: int) -> int:
        """Where a binder of the constructor's telescope sits in the rule's.

        The constructor's telescope is parameters then fields; the rule's is
        parameters, motives, minor premises, then fields. So a parameter keeps
        its place and a field is displaced by everything between -- which is
        the whole of the arithmetic this pass has to get right.
        """
        return ctor_pos if ctor_pos < P else P + M + N + (ctor_pos - P)

    def mover(in_scope: int, depth: int, own: int = 0):
        """`move` for a term under `in_scope` constructor binders at `depth`.

        `depth` is how many binders are in scope where the rewritten term will
        sit, which differs from term to term: a field's own binder type sits
        shallower than the rule's body, and each lambda of a recursive call
        sits one deeper than the last. Getting this uniform was the first
        version's bug -- it used the body's depth everywhere, so every
        constructor with a field came back forged.

        `own` counts binders of a recursive field's own telescope that are
        already in scope; those map to the lambdas the recursive call
        introduces rather than to anything of the constructor's.
        """
        def move(free: int) -> int:
            pos = in_scope + own - 1 - free
            if pos < 0:
                raise IndexError("free index escapes the constructor telescope")
            if pos >= in_scope:                 # one of the field's own binders
                return depth - 1 - (T + (pos - in_scope))
            return depth - 1 - rule_pos(pos)
        return move

    def at(pos: int) -> int:
        return T - 1 - pos

    body_args = [bvar(at(P + M + N + i)) for i in range(K)]

    recursive, decline = _recursive_fields(ctor, family)
    if decline is not None:
        return None, decline
    for i, ftype, head_name in recursive:
        ind = env.get(head_name)
        if ind is None:
            return None, f"{NOT_IN_EXPORT}: the field's inductive {head_name} is absent"
        fbinders, fconcl = _telescope(ftype)
        L = len(fbinders)
        _, fargs = _head_and_args(fconcl)
        if len(fargs) < ind.num_params:
            return None, "a recursive field's type is not applied to the parameters"
        indices = fargs[ind.num_params:]

        try:
            call_indices = [relabel(a, mover(P + i, T + L, own=L)) for a in indices]
            call_binders = [relabel(fbinders[b], mover(P + i, T + b, own=b))
                            for b in range(L)]
        except IndexError as exc:
            return None, f"could not place a recursive field: {exc}"
        # the callee is the recursor of the member the FIELD is of, which is
        # this recursor for a single inductive and a sibling's for a mutual
        # family: `DiseqCnstr.mk`'s proof field calls `DiseqCnstrProof.rec`.
        # Hardcoding this recursor passed all 137 recursive calls in Lean's
        # own Init -- none of which is mutual -- and failed 25 in Mathlib.
        call = const(head_name.child("rec"),
                     [param(p) for p in (rec.lvl_params or [])])
        call = apps(call, [bvar(at(j) + L) for j in range(P + M + N)])
        call = apps(call, call_indices)
        # the field itself, applied to the binders the call introduced
        target = apps(bvar(at(P + M + N + i) + L),
                      [bvar(L - 1 - b) for b in range(L)])
        call = apps(call, [target])
        for b in reversed(range(L)):
            call = Expr._mk(LAM, a=call_binders[b], b=call, name=ctor.name)
        body_args.append(call)

    body = apps(bvar(at(P + M + minor_index)), body_args)

    rec_doms, _ = _telescope(rec.type)
    if len(rec_doms) < P + M + N:
        return None, "the recursor's type has fewer binders than it declares"
    prefix = rec_doms[:P + M + N] + [
        strip_gadgets(relabel(f, mover(P + i, P + M + N + i)))
        for i, f in enumerate(fields)]
    out = body
    for d in reversed(prefix):
        out = Expr._mk(LAM, a=d, b=out, name=ctor.name)
    return out, None


def check_rule(rec, ctor, nfields: int, rhs: Expr, minor_index: int,
               env, family) -> tuple[str, str]:
    """(verdict, reason) for one iota rule."""
    if nfields != ctor.num_fields:
        return "VIOLATION", (
            f"the rule takes {nfields} fields but {ctor.name} declares "
            f"{ctor.num_fields}")
    try:
        want, why = expected_rhs(rec, ctor, minor_index, env, family)
    except (IndexError, AttributeError, RecursionError) as exc:
        return "UNCLASSIFIED", f"could not derive the expected rule: {exc!r}"
    if want is None:
        return "UNCLASSIFIED", why

    got_doms, got_body = _lams(rhs)
    want_doms, want_body = _lams(want)
    if len(got_doms) != len(want_doms):
        return "VIOLATION", (
            f"the rule abstracts {len(got_doms)} arguments where the recursor's "
            f"parameters, motives, minor premises and {ctor.name}'s fields make "
            f"{len(want_doms)}")
    if not alpha_eq(got_body, want_body):
        return "VIOLATION", (
            f"the rule's body is not what {ctor.name} and this recursor derive: "
            f"expected `{want_body!r}`, found `{got_body!r}`")
    for i, (g, w) in enumerate(zip(got_doms, want_doms)):
        if not alpha_eq(g, w):
            return "VIOLATION", (
                f"the rule's binder {i} has type `{g!r}` where the derivation "
                f"gives `{w!r}`")
    return "OK", "the rule is the one this constructor and recursor derive"


def check_recursor(rec, env) -> tuple[str, str]:
    """(verdict, reason) for every iota rule of one recursor."""
    family = list(rec.all_names) or [rec.induct or rec.name]
    inds = [env.get(n) for n in family]
    if any(i is None or i.kind != "ind" for i in inds):
        return "UNCLASSIFIED", f"{NOT_IN_EXPORT}: a family member is not in this export"
    if rec.num_motives != len(family):
        return "UNCLASSIFIED", (
            f"{NESTED}: {rec.num_motives} motives for a family of {len(family)}")

    all_ctors = [c for i in inds for c in i.ctors]
    worst = ("OK", "every rule is the one derived")
    for cname, nfields, rhs in rec.rules:
        if cname not in all_ctors:
            return "VIOLATION", (
                f"a rule names {cname}, not a constructor of this family")
        ctor = env.get(cname)
        if ctor is None:
            return "UNCLASSIFIED", f"{NOT_IN_EXPORT}: constructor {cname}"
        verdict, reason = check_rule(rec, ctor, nfields, rhs,
                                     all_ctors.index(cname), env, family)
        if verdict == "VIOLATION":
            return verdict, f"{cname}: {reason}"
        if verdict == "UNCLASSIFIED" and worst[0] == "OK":
            worst = (verdict, f"{cname}: {reason}")
    return worst


def check_env(env) -> dict:
    """Classify the iota rules of every recursor in `env`.

    `ok` means the rules are the ones this constructor and recursor derive. It
    does not mean the export came from Lean: see this module's docstring.
    """
    out = {"checked": 0, "ok": [], "violations": [], "unclassified": []}
    for name in env.order:
        d = env.get(name)
        if d is None or d.kind != "rec":
            continue
        out["checked"] += 1
        verdict, reason = check_recursor(d, env)
        if verdict == "OK":
            out["ok"].append(str(name))
        elif verdict == "VIOLATION":
            out["violations"].append([str(name), reason])
        else:
            out["unclassified"].append([str(name), reason])
    return out
