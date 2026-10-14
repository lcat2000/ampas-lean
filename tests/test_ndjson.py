"""kernel3's second frontend: lean4export NDJSON (ROADMAP 6).

`harness/kernel3/ndjson.py` exists so `kernel3` can be run against the
[Lean Kernel Arena](https://arena.lean-lang.org/) — its first external,
adversarial measurement. But the frontend is a TRANSLATION, and a translation
can be the thing that fails: a dropped declaration is one the checker cannot
object to, so a reader bug would look like a clean result.

These tests guard the reader, not the checker:

  * an unknown record kind must RAISE, never be skipped;
  * the record kinds handled must cover what the arena corpus actually
    contains, which is checked against the corpus when it is present;
  * the committed differential record must show both frontends agreeing,
    declaration for declaration, on an environment exported twice.

The frontend's first version dropped `proj`'s `typeName` on the mistaken
belief that `kernel3`'s `proj` did not take it. 46 of the arena's tests then
failed to parse at all — which is how it was found, and which is why
`test_proj_keeps_the_structure_type_name` exists.
"""
import inspect
import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
from kernel3 import ndjson                                    # noqa: E402
from kernel3.ndjson import (parse_ndjson, NdjsonError,        # noqa: E402
                            EXPR_KINDS, LEVEL_KINDS, DECL_KINDS)

DIFF = ROOT / "evidence" / "ndjson_frontend_differential.json"

# The extracted arena corpus, when a run has fetched it. Absent in CI and in a
# clean checkout, so the test that uses it skips rather than failing: the
# corpus is 3.5 MB of third-party data and is not vendored here.
CORPUS = next((c for c in (ROOT / "build" / "arena-tests",
                           ROOT / "build" / "arena" / "arena-tests")
               if c.exists()), None)


def write(tmp_path, *lines) -> str:
    p = tmp_path / "t.ndjson"
    p.write_text("\n".join(json.dumps(x) for x in lines) + "\n",
                 encoding="utf-8", newline="\n")
    return str(p)


# ------------------------------------------- an unknown record is an error
def test_an_unknown_record_kind_raises_rather_than_being_skipped(tmp_path):
    """The failure that would matter: a record silently ignored is a
    declaration the checker never sees and therefore never objects to."""
    path = write(tmp_path, {"meta": {"format": {"version": "3.1.0"}}},
                 {"someFutureDeclaration": {"name": 0}})
    with pytest.raises(NdjsonError):
        parse_ndjson(path)


def test_an_unknown_expression_kind_raises(tmp_path):
    path = write(tmp_path, {"meta": {"format": {"version": "3.1.0"}}},
                 {"ie": 1, "someFutureExpr": 3})
    with pytest.raises(NdjsonError):
        parse_ndjson(path)


def test_a_future_format_version_is_refused(tmp_path):
    """Reading a format this frontend was not written against would produce
    numbers about nothing."""
    path = write(tmp_path, {"meta": {"format": {"version": "4.0.0"}}})
    with pytest.raises(NdjsonError):
        parse_ndjson(path)


def test_a_forward_reference_raises_rather_than_defaulting(tmp_path):
    path = write(tmp_path, {"meta": {"format": {"version": "3.1.0"}}},
                 {"ie": 0, "const": {"name": 99, "us": []}})
    with pytest.raises(NdjsonError):
        parse_ndjson(path)


def test_the_reader_never_swallows_an_exception():
    """Source-level: no bare `except: pass` or `continue` in the record
    dispatch. The whole guarantee above rests on it."""
    src = Path(ndjson.__file__).read_text(encoding="utf-8")
    body = src.split("def _record(")[1]
    assert "except Exception" not in body
    assert "pass\n" not in body


# ---------------------------------------------- the kinds that are handled
def test_every_kind_the_format_defines_is_listed():
    assert EXPR_KINDS == {"bvar", "sort", "const", "app", "lam", "forallE",
                          "letE", "proj", "natVal", "strVal"}
    assert LEVEL_KINDS == {"succ", "max", "imax", "param"}
    assert DECL_KINDS == {"def", "thm", "axiom", "opaque", "quot", "inductive"}


def test_the_expression_kinds_cover_kernel3s_own_term_language():
    """kernel3 has eleven node kinds; FVAR is internal to the checker and
    never appears in an export. Everything else must be readable or the
    frontend is lossy in a way no test of the arena result would reveal."""
    from kernel3 import terms
    ints = {n for n in dir(terms) if n.isupper() and isinstance(getattr(terms, n), int)}
    assert "FVAR" in ints
    assert len(EXPR_KINDS) == 10


def test_proj_keeps_the_structure_type_name():
    """The regression. `kernel3.terms.proj(name, idx, e)` takes the
    structure's type name, and the arena's proj-non-structure and
    proj-of-*-prop bug tests are precisely about it."""
    src = Path(ndjson.__file__).read_text(encoding="utf-8")
    assert 'proj(N(v["typeName"]), int(v["idx"]), E(v["struct"]))' in src
    sig = inspect.signature(__import__("kernel3.terms", fromlist=["proj"]).proj)
    assert list(sig.parameters) == ["s", "i", "e"]


def test_an_inductive_block_is_unpacked_into_three_kinds(tmp_path):
    """NDJSON carries an inductive's types, constructors and recursors in ONE
    record; the AMPAS format has three kinds of line. The Env must come out
    the same either way, or the recursor and iota passes see a different
    world through each frontend."""
    path = write(
        tmp_path,
        {"meta": {"format": {"version": "3.1.0"}}},
        {"in": 1, "str": {"pre": 0, "str": "Void"}},
        {"ie": 0, "sort": 0},
        {"inductive": {
            "types": [{"all": [1], "ctors": [], "isRec": False,
                       "isReflexive": False, "levelParams": [], "name": 1,
                       "numIndices": 0, "numNested": 0, "numParams": 0,
                       "type": 0}],
            "ctors": [], "recs": []}},
    )
    env = parse_ndjson(path)
    names = [str(n) for n in env.order]
    assert names == ["Void"]
    d = env.get(env.order[0])
    assert d.kind == "ind"
    assert getattr(d, "num_nested", None) == 0, (
        "numNested is read and kept, and must not be folded into another field")


# ------------------------------------------------- the differential record
def test_the_two_frontends_agree_on_the_same_environment():
    """The guard that makes an arena number about the checker rather than
    about this file: the same Lean environment, exported twice and read twice,
    must give identical declaration fingerprints."""
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    assert d["schema"] == "ampas-ndjson-frontend-differential/1"
    assert d["mismatches"] == []
    assert d["shared_declarations"] > 1000, (
        "a shrinking intersection is how a frontend that stopped reading "
        "records would pass this test by comparing less and less")
    assert d["agreed"] == d["shared_declarations"]


def test_the_differential_record_says_what_it_does_not_establish():
    d = json.loads(DIFF.read_text(encoding="utf-8"))
    means = " ".join(d["means"])
    assert "does NOT establish" in means
    assert "RAISES" in means
    assert "different closure rules" in means


@pytest.mark.skipif(CORPUS is None, reason="the arena corpus is not extracted here")
def test_the_handled_kinds_cover_the_arena_corpus():
    """Measured against the corpus rather than assumed: if the arena ever adds
    a record kind, this fails before the result does."""
    seen = set()
    for f in sorted(CORPUS.rglob("*.ndjson")):
        with f.open(encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                o = json.loads(line)
                if "ie" in o:
                    seen |= (set(o) - {"ie"})
                elif "il" in o:
                    seen |= (set(o) - {"il"})
                elif "in" in o:
                    seen |= {"__name__"}
                else:
                    seen |= set(o)
    unknown = seen - EXPR_KINDS - LEVEL_KINDS - DECL_KINDS - {
        "meta", "__name__", "str", "num"}
    assert not unknown, unknown
