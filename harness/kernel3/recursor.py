"""Recursor shape — the second of `kernel3`'s three assumed properties.

ROADMAP 2b. `harness/kernel3/positivity.py` closed the first. This one closes
the second, and `tests/forgeries/forge_large_elim.export` is its live vector: a
`Prop` with two constructors given a hand-written recursor whose motive
eliminates into `Sort u`. Proof irrelevance then makes two types
interchangeable and `False` follows. The two exports differ in one token —
`Sort 0` against `Sort u` — and nothing in the checker looked at it.

**Same discipline as positivity, for the same reason.** Checking a recursor's
shape WIDENS what could be accepted, so this is a separate pass with its own
tests, differentially tested against the declaration sets Lean itself accepts,
and it CLASSIFIES rather than judges: a shape it does not model comes back
`UNCLASSIFIED`, never `OK`. It changes no verdict; `kernel3`'s provenance gate
is untouched.

What it checks, for a recursor of an inductive family `I₁ … I_k`:

  1. **Family.** Every member resolves to an inductive in the environment.
  2. **Arity.** One motive per family member, one minor premise per
     constructor of the family, and the recursor's own parameter and index
     counts equal the inductive's.
  3. **Rules.** Exactly one iota rule per constructor, each naming a
     constructor of this family, each with that constructor's own field count.
     A missing, duplicated or foreign rule is a violation.
  4. **K-like reduction.** `k` may be set only for a single `Prop` inductive
     with exactly one constructor that has no fields. `Eq` and `HEq` are the
     cases that qualify.
  5. **Elimination universe.** If the inductive is not a `Prop`, eliminating
     into any `Sort` is fine. If it IS a `Prop`, the motive must target `Prop`
     — *unless* the inductive is a subsingleton, in which case large
     elimination is sound and Lean does generate it: at most one constructor,
     and every field of it either a proof (its type is a `Prop`) or an
     argument the conclusion's indices already pin down. `Eq.refl`'s `a` is
     the second case; `And.intro`'s two fields are the first.

**Where it declines.** Deciding whether a field's type is a `Prop` sometimes
needs a declaration the export does not contain: `--specs` carries the assumed
declarations only, so a field typed `a ≠ 0` cannot be decided without `Ne`.
Those come back `UNCLASSIFIED` with `FIELD_TYPE_NOT_IN_EXPORT`, counted
separately in the differential report, because the cause is the export's scope
and not the recursor. Nested inductives generate auxiliary recursors over the
nesting type (`Lean.Syntax.rec` has three motives for one family) and are
declined too — the same declaration positivity declines.

**What it still does not close.** The iota rules' right-hand sides. This pass
counts them and checks which constructor each belongs to; it does not check
that a rule actually computes what the constructor's fields say it should. So
a specification passing both this pass and positivity is still not a checked
specification, and ASSUMPTIONS A3 stands.
"""
from __future__ import annotations

from .terms import Expr

# Imported, never restated: a reorder in terms.py would otherwise make this
# pass inspect nothing and report every recursor clean.
from .terms import BVAR, SORT, CONST, APP, PI  # noqa: E402

# reasons that are the export's scope rather than the declaration's shape
FIELD_TYPE_NOT_IN_EXPORT = "FIELD_TYPE_NOT_IN_EXPORT"


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


def result_sort(ty: Expr):
    """The `Sort` a telescope ends in, or None if it does not end in one."""
    _, concl = _telescope(ty)
    return concl.a if concl.kind == SORT else None


def is_prop_valued(ty: Expr) -> bool:
    """Does this type end in `Prop`? `Sort u` with `u` a parameter does not."""
    s = result_sort(ty)
    return s is not None and s.kind == "zero"


def field_is_proof(ty: Expr, ctx: list, pos: int, env):
    """Is `ty` -- the type of binder `pos` in telescope `ctx` -- a Prop?

    True / False / None, where None means this pass cannot tell. Three shapes
    are decided and nothing else is guessed:

      * a `Sort` is data, never a proof;
      * an application of a constant whose declared type ends in a `Sort`,
        fully applied, has that sort -- so `Nat` is data and `Ne a b` is a
        proof. A constant the export does not contain gives None;
      * an application of a bound variable, resolved against `ctx`: a field
        typed `a` where `a : Prop` is a parameter is a proof, and one typed
        `r a a` where `r : α → α → Prop` is too.
    """
    inner, concl = _telescope(ty)
    head, args = _head_and_args(concl)
    if head.kind == SORT:
        return False
    if head.kind == CONST:
        d = env.get(head.name)
        if d is None:
            return None
        hdoms, hconcl = _telescope(d.type)
        if hconcl.kind != SORT:
            return None
        if len(args) != len(hdoms):
            return None          # partially applied: still a function
        return hconcl.a.kind == "zero"
    if head.kind == BVAR:
        if head.idx < len(inner):
            return None          # bound inside this type's own telescope
        ref = pos - 1 - (head.idx - len(inner))
        if ref < 0 or ref >= len(ctx):
            return None
        rdoms, rconcl = _telescope(ctx[ref])
        if rconcl.kind != SORT or len(args) != len(rdoms):
            return None
        return rconcl.a.kind == "zero"
    return None


def subsingleton(induct, env) -> tuple[str, str]:
    """May this inductive be eliminated into a large `Sort`?

    ("YES"|"NO"|"UNKNOWN", reason). An inductive with no constructors (`False`)
    qualifies: there is nothing to extract data from.
    """
    if len(induct.ctors) > 1:
        return "NO", (
            f"a Prop with {len(induct.ctors)} constructors cannot be eliminated "
            f"into a large Sort: the recursor would read which constructor was "
            f"used, and proof irrelevance makes that unsound")
    for cname in induct.ctors:
        c = env.get(cname)
        if c is None:
            return "UNKNOWN", f"constructor {cname} is not in the export"
        cdoms, cconcl = _telescope(c.type)
        _, cargs = _head_and_args(cconcl)
        index_args = cargs[c.num_params:]
        for k, f in enumerate(cdoms[c.num_params:]):
            pos = c.num_params + k
            proof = field_is_proof(f, cdoms, pos, env)
            if proof is True:
                continue
            # a field the conclusion's indices already pin down carries no
            # free information, so it may be eliminated (`Eq.refl`'s `a`)
            bidx = len(cdoms) - pos - 1
            if any(a.kind == BVAR and a.idx == bidx for a in index_args):
                continue
            if proof is False:
                return "NO", (
                    f"{cname} field {k} is data and is not fixed by the "
                    f"conclusion's indices, so a large recursor would extract "
                    f"data from a proof")
            return "UNKNOWN", (
                f"{FIELD_TYPE_NOT_IN_EXPORT}: {cname} field {k}'s type cannot "
                f"be decided from this export")
    return "YES", "subsingleton: nothing to extract"


def check_recursor(rec, env) -> tuple[str, str]:
    """(verdict, reason) for one recursor. OK | VIOLATION | UNCLASSIFIED."""
    family = list(rec.all_names) or [rec.induct or rec.name]
    inds = [env.get(n) for n in family]
    if any(i is None or i.kind != "ind" for i in inds):
        return "UNCLASSIFIED", "a family member is not an inductive in this export"

    if rec.num_motives != len(family):
        return "UNCLASSIFIED", (
            f"{rec.num_motives} motives for a family of {len(family)}: this is "
            f"an auxiliary recursor of a nested inductive, whose shape this "
            f"pass does not model")

    total_ctors = sum(len(i.ctors) for i in inds)
    if rec.num_minors != total_ctors:
        return "VIOLATION", (
            f"{rec.num_minors} minor premises for {total_ctors} constructors")

    # Which family member does THIS recursor eliminate? A mutual family gets
    # one recursor per member, each carrying a motive and minor premises for
    # the whole family but iota rules for its own constructors only. Reading
    # the member off the conclusion rather than off the name or the family
    # order is what makes that work: the conclusion is `motive_j indices x`,
    # whose head is the bound variable of motive_j.
    doms, concl = _telescope(rec.type)
    chead, _ = _head_and_args(concl)
    if chead.kind != BVAR:
        return "UNCLASSIFIED", "the recursor's conclusion is not an applied motive"
    mot_pos = len(doms) - 1 - chead.idx
    if not (rec.num_params <= mot_pos < rec.num_params + rec.num_motives):
        return "UNCLASSIFIED", (
            f"the conclusion's head is binder {mot_pos}, which is not one of "
            f"the {rec.num_motives} motive binders")
    mdoms, mconcl = _telescope(doms[mot_pos])
    if len(mdoms) != rec.num_indices + 1 or mconcl.kind != SORT:
        return "UNCLASSIFIED", (
            f"the motive takes {len(mdoms)} arguments for {rec.num_indices} "
            f"indices and does not end in a Sort; this pass cannot read its "
            f"elimination universe")
    thead, _ = _head_and_args(_telescope(mdoms[-1])[1])
    if thead.kind != CONST or thead.name not in family:
        return "UNCLASSIFIED", (
            "the motive's last argument is not of a family member's type")
    target = env.get(thead.name)

    # the major premise -- the recursor's own last binder -- must be of the
    # same type the motive is about, or the two halves describe different
    # eliminations
    major, _ = _head_and_args(_telescope(doms[-1])[1])
    if major.kind != CONST or major.name is not thead.name:
        return "UNCLASSIFIED", (
            "the major premise and the motive are not about the same inductive")

    if rec.num_params != target.num_params:
        return "VIOLATION", (
            f"{rec.num_params} parameters but {target.name} declares "
            f"{target.num_params}")
    if rec.num_indices != target.num_indices:
        return "VIOLATION", (
            f"{rec.num_indices} indices but {target.name} declares "
            f"{target.num_indices}")
    if len(rec.rules) != len(target.ctors):
        return "VIOLATION", (
            f"{len(rec.rules)} iota rules for {target.name}'s "
            f"{len(target.ctors)} constructors")

    all_ctors = list(target.ctors)
    seen = set()
    for cname, nfields, _rhs in rec.rules:
        if cname not in all_ctors:
            return "VIOLATION", (
                f"an iota rule names {cname}, not a constructor of {target.name}")
        if cname in seen:
            return "VIOLATION", f"two iota rules for {cname}"
        seen.add(cname)
        c = env.get(cname)
        if c is None:
            return "UNCLASSIFIED", f"constructor {cname} is not in the export"
        if nfields != c.num_fields:
            return "VIOLATION", (
                f"the iota rule for {cname} takes {nfields} fields but the "
                f"constructor declares {c.num_fields}")
    missing = [c for c in all_ctors if c not in seen]
    if missing:
        return "VIOLATION", f"no iota rule for {missing[0]}"

    if rec.k:
        if len(family) != 1 or not is_prop_valued(target.type):
            return "VIOLATION", (
                "K-like reduction is set on a recursor that is not for a "
                "single Prop inductive")
        if len(target.ctors) != 1:
            return "VIOLATION", (
                f"K-like reduction is set but the inductive has "
                f"{len(target.ctors)} constructors")
        c = env.get(target.ctors[0])
        if c is None:
            return "UNCLASSIFIED", "the single constructor is not in the export"
        if c.num_fields != 0:
            return "VIOLATION", (
                f"K-like reduction is set but {c.name} has {c.num_fields} "
                f"fields, so two proofs need not be the same term")

    if not is_prop_valued(target.type):
        return "OK", "the inductive is not a Prop, so any elimination is fine"
    if mconcl.a.kind == "zero":
        return "OK", "Prop inductive eliminating into Prop"

    # large elimination of a Prop: sound only for a subsingleton
    if len(family) > 1:
        return "UNCLASSIFIED", (
            "large elimination of a mutual Prop family: this pass does not "
            "decide it")
    verdict, why = subsingleton(target, env)
    if verdict == "YES":
        return "OK", f"large elimination of a Prop, permitted: {why}"
    if verdict == "NO":
        return "VIOLATION", f"large elimination of a Prop: {why}"
    return "UNCLASSIFIED", f"large elimination of a Prop, undecided: {why}"


def check_env(env) -> dict:
    """Classify every recursor in `env`.

    `ok` is NOT a licence: the iota rules' right-hand sides are not checked.
    See this module's docstring.
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
