"""Declaration well-formedness — a fifth pass, found by the arena.

ROADMAP 3/6c. Two of the nine bad arena tests `kernel3` still accepts are not
about terms, inductives or flags. They are about whether the DECLARATION is a
legitimate declaration at all:

  bad/tutorial/014_selfProof    theorem selfProof : (p : Prop) → p := selfProof
  bad/tutorial/012_nonPropThm   theorem nonPropThm : Prop := (x : Prop) → x

`014` is the serious one, and it is not an exotic kernel edge case — it is the
most obvious bogus proof there is. The theorem's value is a reference to
itself, so it type-checks against its own declared type, and what it proves is
`∀ p : Prop, p`: everything, `False` included. Lean's kernel rejects it for a
structural reason this checker did not share: Lean adds a declaration to the
environment only AFTER checking it, so the self-reference is an unknown
constant. `kernel3`'s reader adds first and checks after, which makes the
constant resolve.

`docs/ARENA-RESULT.md` listed both under "outside what `kernel3` checks rather
than bugs in it". For `014` that was **an overstatement of this checker's
scope boundary**: it is a missing check, decidable by reading the declaration.
That record is corrected rather than quietly amended.

**Containment, stated accurately.** The same document attributed the
containment of these tests to the provenance gate. It does not apply: both are
*defined* declarations carrying a value, not assumed ones, so the gate has
nothing to report — `introduced_assumptions` is 0 for both in
`evidence/arena_run_after_fixes.json`. What contains them inside AMPAS's own
pipeline is the **compile step**: a submission is compiled by Lean, which
rejects both before any export exists. That is the containment, and it is
exactly the one ASSUMPTIONS A3 says evaporates when the checker is pointed at
an export of unknown provenance.

**Why a pass and not a change to `check.py`.** Same rule as the other four:
the term checker is the thing under review, and these classify rather than
judge. Nothing here reads a type, so this pass stays independent of the
checker it corroborates.
"""
from __future__ import annotations

from .terms import CONST, PI, SORT
from .positivity import occurs

# Declaration kinds that carry a value this pass can read.
VALUED_KINDS = ("def", "thm", "opaque")


def self_referential(decl) -> bool:
    """Does a declaration's value mention the declaration itself?

    In an export, never legitimately. Lean compiles every form of recursion
    away before a value is exported: structural recursion through `brecOn`,
    well-founded recursion through `WellFounded.fix`, and a mutual block
    through a single `brecOn` application. So an exported `def`, `thm` or
    `opaque` whose value names itself did not come from Lean, and the shape it
    has is `014_selfProof`'s.

    That claim is a claim about real declarations, so it is measured rather
    than assumed: `harness/spec_diff.py --pass declaration` runs this over
    every valued declaration in the trusted reference's full export, and a
    single violation there means this rule is wrong, not Lean.
    """
    if decl.kind not in VALUED_KINDS or decl.value is None:
        return False
    return occurs(decl.value, {decl.name})


def mutual_block_referential(decl) -> list:
    """Which OTHER members of its own mutual block a value mentions.

    Reported, never a violation. Mutual recursion is compiled away like every
    other kind, so this should also be empty — but "should" is the word that
    put three bugs in the iota pass, and unlike the self case there is no
    arena test pinning it. It is recorded so the differential says what the
    libraries actually contain, and a rule can be added later on evidence
    instead of on expectation.
    """
    if decl.kind not in VALUED_KINDS or decl.value is None:
        return []
    others = {n for n in (decl.all_names or []) if n is not decl.name}
    return sorted(str(n) for n in others if occurs(decl.value, {n}))


def _conclusion(e):
    """Strip the ∀ prefix: `∀ x₁ … x_k, C` -> `C`."""
    while e is not None and e.kind == PI:
        e = e.b
    return e


def theorem_type_is_a_universe(decl) -> bool:
    """Is a theorem's statement a UNIVERSE rather than a proposition?

    `012_nonPropThm` declares a `thm` of type `Prop`. A theorem's type must be
    a proposition — `Prop : Type`, not `Prop : Prop` — so this is a definition
    wearing a theorem's label.

    **What this covers, exactly.** The type's conclusion being a `Sort`, which
    is decidable by looking at it: the type of `∀ …, Sort u` is
    `Sort (imax … (u+1))` and never `Prop`, whatever the levels are. That is
    the arena's test and the whole of what is claimed here.

    **What it does not cover.** A `thm` whose type is some other non-Prop, say
    `theorem foo : Nat := 5`. Deciding that needs `infer` and a level
    comparison, which would make this pass depend on the term checker it
    exists to corroborate. It is left out deliberately, and it is the milder
    case: `kernel3`'s proof irrelevance is driven by the inferred type of a
    term, not by the kind of the declaration it came from, so a mislabelled
    theorem does not thereby become irrelevant. `014` is the one that proves
    `False`; this one is a label error.
    """
    if decl.kind != "thm":
        return False
    c = _conclusion(decl.type)
    return c is not None and c.kind == SORT


def check_env(env) -> dict:
    """Classify every declaration: OK, VIOLATION or UNCLASSIFIED.

    Both rules are decidable by reading the declaration, so there is no
    UNCLASSIFIED outcome — as in `safety.py`, and unlike the three inductive
    passes, which all have shapes they cannot judge. The key is kept so every
    pass has the same shape for `harness/spec_diff.py`.
    """
    out = {"checked": 0, "ok": [], "violations": [], "unclassified": [],
           "mutual_block_references": []}
    for name in env.order:
        d = env.get(name)
        if d is None:
            continue
        out["checked"] += 1
        why = []
        if self_referential(d):
            why.append(
                f"the value of this {d.kind} refers to `{name}` itself. Lean "
                f"adds a declaration only after checking it, so no export from "
                f"Lean contains this: every form of recursion is compiled away "
                f"before a value is exported. Accepting it proves whatever the "
                f"declared type says")
        if theorem_type_is_a_universe(d):
            why.append(
                "the statement of this theorem is a universe, not a "
                "proposition: the type of `Sort u` is `Sort (u+1)`, never "
                "`Prop`, so this is a definition carrying a theorem's label")
        if why:
            out["violations"].append([str(name), "; ".join(why)])
        else:
            out["ok"].append(str(name))
        mb = mutual_block_referential(d)
        if mb:
            out["mutual_block_references"].append([str(name), mb])
    return out
