"""Strict positivity of inductive specifications — a SEPARATE pass.

ROADMAP 2. `harness/kernel3` assumes every inductive declaration is a
legitimate specification, and two hand-written forgeries in
`tests/forgeries/` prove `False` through that hole. The provenance gate stops
them producing a clean result, but that is containment, not a fix.

**Why this is not written into the checker.** Checking positivity WIDENS what
can be accepted: if `kernel3` currently reports every inductive as an assumed
specification, a bug here turns one of those reports into an endorsement, and
a mistake in this direction is unsoundness rather than a false alarm. So:

  * it lives in its own module with its own tests;
  * it is differentially tested against the declaration sets both Lean kernels
    accept -- every inductive they accept must pass, every forgery must fail;
  * it classifies rather than judges. A specification it does not understand
    comes back UNCLASSIFIED, never OK. `tests/test_positivity.py` fails if
    UNCLASSIFIED is ever treated as a pass.

**What it does not close.** Positivity is ONE of three properties `kernel3`
assumes about an inductive; the others are the recursor's shape and the iota
rules. A specification that passes this pass is not a checked specification,
and the record must not say so -- `kernel3`'s provenance gate stays exactly as
it is. The forgery `forge_large_elim.export` makes the point: it is a forged
recursor, positivity has nothing to say about it, and it must still be caught
by provenance.

The rule, for an inductive family `all` whose constructor type is
`∀ (params...) (a₁ : A₁) ... (aₘ : Aₘ), I params indices`:

  * no member of `all` may occur in a parameter's type;
  * for each argument type `Aᵢ`, viewed as `∀ (x₁:B₁) ... (x_k:B_k), C`:
      - if no member of `all` occurs in `Aᵢ` at all, it is fine;
      - otherwise no member of `all` may occur in ANY `Bⱼ` -- this is the
        strict part, and it is what `Bad.mk : (Bad → MyFalse) → Bad` violates:
        the recursive occurrence sits to the left of an arrow;
      - and `C` must be a member of `all` applied to arguments in which no
        member of `all` occurs.
  * the constructor's own conclusion must be an application of the inductive
    being declared.

Nested inductives (a recursive occurrence under another inductive's
parameter, which Lean permits when the other inductive is suitably positive)
are NOT handled: they come back UNCLASSIFIED with that reason, because
accepting them needs the other inductive's own positivity and this pass does
not compute it.
"""
from __future__ import annotations

from .terms import Expr

# Node kinds are small ints in terms.py (`BVAR, FVAR, ... = range(11)`).
# Imported rather than restated: a rename or reorder there would otherwise
# make this pass inspect nothing and report every specification clean, which
# is the one failure direction that matters here.
from .terms import PI, APP, CONST  # noqa: E402


def occurs(e: Expr, names: set) -> bool:
    """Does any of `names` occur as a constant anywhere in `e`?"""
    stack = [e]
    while stack:
        x = stack.pop()
        if x is None:
            continue
        if x.kind == CONST and x.name in names:
            return True
        for part in (x.a, x.b, x.c):
            if isinstance(part, Expr):
                stack.append(part)
    return False


def _telescope(e: Expr) -> tuple[list, Expr]:
    """Split `∀ x₁:B₁ ... x_k:B_k, C` into ([B₁..B_k], C)."""
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


def check_constructor(ctor_type: Expr, num_params: int, family: set,
                      induct) -> tuple[str, str]:
    """(verdict, reason) for one constructor. verdict: OK | VIOLATION | UNCLASSIFIED."""
    doms, concl = _telescope(ctor_type)
    if len(doms) < num_params:
        return "UNCLASSIFIED", (
            f"the type has {len(doms)} binders but the declaration claims "
            f"{num_params} parameters")

    # parameters may not mention the family
    for i, d in enumerate(doms[:num_params]):
        if occurs(d, family):
            return "VIOLATION", (
                f"parameter {i} has type mentioning the inductive family, so the "
                f"family is not uniform in its own parameters")

    # the conclusion must be the inductive being declared
    head, _ = _head_and_args(concl)
    if head.kind != CONST or head.name != induct:
        return "UNCLASSIFIED", (
            f"the conclusion is not an application of {induct}; "
            f"head is {head.kind}")

    for i, d in enumerate(doms[num_params:], start=num_params):
        if not occurs(d, family):
            continue                      # no recursion here: nothing to check
        inner_doms, inner_concl = _telescope(d)
        for j, b in enumerate(inner_doms):
            if occurs(b, family):
                return "VIOLATION", (
                    f"argument {i}: the inductive family occurs in binder {j} of "
                    f"that argument's own telescope, i.e. to the LEFT of an "
                    f"arrow. That is a non-strictly-positive occurrence and it "
                    f"is what lets a diagonal argument derive False")
        ih, iargs = _head_and_args(inner_concl)
        if ih.kind != CONST or ih.name not in family:
            return "UNCLASSIFIED", (
                f"argument {i} mentions the family but its conclusion is headed "
                f"by {ih.kind}{'/' + str(ih.name) if ih.kind == CONST else ''}; "
                f"this is the nested-inductive shape, which this pass does not "
                f"decide")
        for k, a in enumerate(iargs):
            if occurs(a, family):
                return "UNCLASSIFIED", (
                    f"argument {i}: the recursive occurrence is applied to an "
                    f"argument {k} that itself mentions the family; deciding "
                    f"this needs the nested case")
    return "OK", "strictly positive"


def check_env(env) -> dict:
    """Classify every inductive in `env`.

    Returns counts plus the per-declaration findings. `ok` is NOT a licence:
    see this module's docstring for the two properties it says nothing about.
    """
    out = {"checked": 0, "ok": [], "violations": [], "unclassified": []}
    for name in env.order:
        d = env.get(name)
        if d is None or d.kind != "ind":
            continue
        out["checked"] += 1
        family = set(d.all_names) or {d.name}
        worst = ("OK", "strictly positive")
        for cname in d.ctors:
            c = env.get(cname)
            if c is None:
                worst = ("UNCLASSIFIED", f"constructor {cname} is not in the export")
                break
            verdict, reason = check_constructor(c.type, d.num_params, family, d.name)
            if verdict == "VIOLATION":
                worst = (verdict, f"{cname}: {reason}")
                break
            if verdict == "UNCLASSIFIED" and worst[0] == "OK":
                worst = (verdict, f"{cname}: {reason}")
        if worst[0] == "OK":
            out["ok"].append(str(name))
        elif worst[0] == "VIOLATION":
            out["violations"].append([str(name), worst[1]])
        else:
            out["unclassified"].append([str(name), worst[1]])
    return out
