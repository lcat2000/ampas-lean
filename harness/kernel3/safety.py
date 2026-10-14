"""`unsafe` and `partial` declarations — a fourth pass, found by the arena.

ROADMAP 6c. Lean marks a declaration `unsafe` or `partial` when it is NOT
checked the way a proof must be: `unsafe` opts out of the kernel's guarantees
entirely, and `partial` opts out of the termination requirement, so a
`partial def` can be a non-terminating loop whose type says it returns
anything at all — including `False`.

The arena has two tests that do exactly that, `bad/tutorial/140_falseFromUnsafe`
and `bad/tutorial/141_falseFromPartial`, and `kernel3` accepted both: the
NDJSON frontend read the `safety` and `isUnsafe` fields and threw them away,
so the flag never reached a checker. Nothing written in this repository would
have found it, because `harness/Export.lean` has no such field to drop —
AMPAS's own exports cannot contain an unsafe declaration.

**Why this is a pass and not a change to `check.py`.** The term checker is the
thing under review; the other specification passes were kept out of it on
purpose and this follows the same rule. It also classifies rather than judges,
and it changes no verdict on its own.

**Why an absent flag is `safe`.** Neither exporter emits unsafe declarations
by default — lean4export needs `--export-unsafe`, and `harness/Export.lean`
has no equivalent. So a declaration with no flag is one the exporter vouched
for, and a declaration WITH the flag is one that reached the file because
somebody asked for it or wrote it by hand. Either way it must not carry a
proof.
"""
from __future__ import annotations

UNSAFE_KINDS = ("unsafe", "partial")


def declared_safety(decl) -> str:
    """`safe`, `unsafe` or `partial`. Absent means safe: see the module docstring."""
    return str(getattr(decl, "safety", "safe") or "safe")


def check_env(env) -> dict:
    """Report every declaration the exporter did not vouch for.

    A VIOLATION, not a decline: `unsafe` and `partial` are what Lean itself
    calls these, and a proof may not rest on either. There is nothing
    undecidable about reading a flag.
    """
    out = {"checked": 0, "ok": [], "violations": [], "unclassified": []}
    for name in env.order:
        d = env.get(name)
        if d is None:
            continue
        out["checked"] += 1
        s = declared_safety(d)
        if s in UNSAFE_KINDS:
            out["violations"].append([str(name), (
                f"declared `{s}`: Lean does not check it the way a proof must "
                f"be checked, so nothing in the environment may depend on it "
                f"({'termination is not required' if s == 'partial' else
                   'the kernel guarantees nothing'})")])
        else:
            out["ok"].append(str(name))
    return out
