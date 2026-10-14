# kernel3 against the Lean Kernel Arena: the first external measurement

> **This document is in three dated parts and the earlier ones are not
> rewritten.** What follows is the first measurement, 2026-10-14, when
> `kernel3` had three specification passes and wrongly accepted 23 of 72.
> "After the fixes" and "Round 9" below carry it to five passes and 7, and
> Round 9 retracts a claim this part makes.

**ROADMAP 6.** `harness/kernel3` has three specification passes, each
differentially tested over 3410 recursors, and four adversarial vectors — all
four written in this repository. "Thirteen attacks with recorded catching
layers is evidence that those thirteen are caught, and nothing more" applies to
the third check as much as to the corpus, and nothing inside this repository
can fix it.

The [Lean Kernel Arena](https://arena.lean-lang.org/) publishes 198 tests for
exactly this layer: **72 that must be rejected** (19 of them regressions for
real Lean kernel bugs) and **126 that must be accepted**. Third-party,
adversarial, and not written with `kernel3` in mind.

Full per-test record: [`evidence/arena_run.json`](../evidence/arena_run.json).
Reproduce with `harness/arena_run.py`.

## The numbers

| configuration | wrongly accepted | wrongly rejected | correct | declined |
| --- | --- | --- | --- | --- |
| `term_only` — what AMPAS's third check does today | **28** | 9 | 151 | 10 |
| `with_spec_passes` — plus positivity, recursor, iota | **23** | 12 | 153 | 10 |

By the arena's own ranking — wrongly-accepted first — 23 is a poor score. The
honest comparison: con-leche and lean4lean each have **0**.

## kernel3 wrongly accepts 23 of the 72

This is not a surprise in *kind*. [ASSUMPTIONS A3](../ASSUMPTIONS.md) has always
said the inductive specification layer is assumed rather than checked, and
that

> point this checker at an olean of unknown provenance — the case where an
> independent checker is most valuable — and the hole is live.

The arena *is* that case. What changed is that the sentence was an argument and
is now a measurement with 23 named tests:

| cause | n | tests |
| --- | --- | --- |
| inductive specification well-formedness | 8 | `047_inductBadNonSort2`, `049_inductTooFewParams`, `050_inductWrongCtorParams`, `051_inductWrongCtorResParams`, `052_inductWrongCtorResLevel`, `053_inductInIndex`, `056_reduceCtorType.mk`, `061_typeWithTooHighTypeField.mk` |
| projection typing on `Prop` / `imax` | 5 | `proj-of-imax-prop`, `090_projProp2`, `092_projProp4`, `093_projProp5`, `094_projProp6` |
| recursor well-formedness | 4 | `orphan-rec`, `extra-rec`, `073_BogusRecursor`, `136_misnamed_rec_user` |
| declaration well-formedness | 2 | `012_nonPropThm`, `014_selfProof` |
| `unsafe` / `partial` flags the frontend drops | 2 | `140_falseFromUnsafe`, `141_falseFromPartial` |
| elimination universe: a level **parameter** may be zero | 1 | `large-elim-param` |
| a duplicate shape `Env.add` does not catch | 1 | `137_dup_rec_def2` |

In AMPAS's own pipeline most of these are contained: the provenance gate
reports any assumed declaration whose fingerprint is not in the trusted
baseline, and that baseline comes from an olean Lean itself compiled. **That
containment is real and it is not an excuse.** The arena measures the checker,
and the checker is what A3 describes.

## What the three specification passes bought, measured from outside

Of the 28 bad tests the term layer accepts, the passes added by
[ROADMAP 2a–2c](../ROADMAP.md) reject **5**:

- `large-elim-prop-bool` — the recursor pass
- `nat-rec-rules` — the iota pass
- `054_indNeg`, `057_indNegReducible`, `117_reflOccLeft` — positivity

`forge_large_elim` and `forge_iota` were written here to exercise the first two
shapes. The arena confirms them against vectors nobody here wrote, which is the
first external evidence that those passes do anything.

## What the passes cost: three false rejections, and the bug behind them

All three come from the iota pass, all have one cause, and **only the arena
could have found it**:

`055_reduceCtorParam.mk`, `119_reduceCtorParamRefl.mk`,
`120_reduceCtorParamRefl2.mk`.

The pass decides whether a constructor field is *recursive* by looking at the
head of its type's conclusion, **syntactically**. Lean decides it after
δ-reduction. In these tests the field's type is `constType (I α) (I α)` —
headed by a *definition* that unfolds to expose the family — so Lean generates
a recursive call, the pass derives a rule without one, and then reports the
legitimate rule forged.

The Init and Mathlib differential (3410 recursors, 0 violations) could not have
found this: **neither library has a constructor field whose type needs
unfolding to reveal its recursion.** The arena has three, and names them after
the behaviour.

The pair `055` (good) and `056` (bad) states the problem as sharply as it can
be stated: the pass **rejects the valid one and accepts the invalid one**.

## The nine term-layer false rejections confirm the adjudication list

Independent of the specification passes, the term layer rejects 9 tests that
must be accepted — and every one is an incompleteness already recorded in
`reference/third_check_adjudications.json` or its immediate neighbourhood:

- `Nat.decidableBallLT.match_5` appears **by name** — TC-02, the nested `imax`
  identity `level_leq` cannot decide;
- `108_unitEta1`, `109_unitEta2`, `075_typeSingletonRecReduction`,
  `proj-cheap-struct` are the structure-eta and
  to-constructor-when-structure area TC-01 describes;
- `church-numerals`, `grind-ring-5`, `magma-list-*`, `init-prelude` are the
  same mechanisms at library scale.

These are in the **rejecting** direction, which is the safe one. The arena
confirming them is the first external evidence that the adjudications describe
real mechanisms rather than convenient ones.

## The ten declines

Six are `bad/tutorial/dup_*`: duplicate declarations, which `kernel3`'s
`Env.add` refuses outright, so the environment never builds. That is the right
*outcome* for a bad test by a legitimate mechanism — but the mechanism is the
**reader**, not the type checker, and this record says so rather than counting
them as rejections.

Four are `good/perf` tests that hit the 180-second per-test timeout. A timeout
is not a verdict. Performance was never a claim of this checker: it is a
from-scratch Python type checker whose purpose is corroborating one submission,
not library-scale throughput.

## What is not claimed

- **That this is a good result.** It is not. 23 against 0 for the two checkers
  AMPAS compares itself to.
- **That it is a surprise.** `kernel3` is a term-layer checker and says so; the
  arena measures full kernels.
- **That the 23 are all equally out of scope.** At least four are bugs in work
  this repository has just finished: `large-elim-param` is a rule of the
  recursor pass that is wrong in the **accepting** direction (a level
  *parameter* may be instantiated to zero, making a two-constructor inductive
  a `Prop`, and the pass treats a parameter as "not a `Prop`"); `orphan-rec` is
  a shape the pass *declines* where it could decide; and the two
  `unsafe`/`partial` tests are flags the NDJSON frontend reads and throws away.

Those four, and the iota recursive-field bug above, are what the next round
addresses. The measurement is recorded first, before any of them is touched,
so that the improvement is measured against a number that was written down
before it was known how to improve it.

---

# After the fixes (same day)

Five bugs the arena found were fixed, each re-validated by the differential
test over Init and Mathlib before being believed. Re-measured:
[`evidence/arena_run_after_fixes.json`](../evidence/arena_run_after_fixes.json).

| configuration | wrongly accepted | wrongly rejected | correct | declined |
| --- | --- | --- | --- | --- |
| `term_only` | 28 | 9 | 151 | 10 |
| `with_spec_passes` | **23 → 9** | **12 → 9** | 153 → 170 | 10 |

`wrongly_rejected` returning to 9 is the term layer's own figure: **the
specification passes now cost nothing**, where before they cost three false
rejections.

## The five fixes

1. **A level parameter may be instantiated to `Prop`.** `is_prop_valued` asked
   whether a sort was *literally* zero, so `MyBool : Sort u` with two
   constructors got a large eliminator. It now asks whether the sort *could* be
   zero. Wrong in the **accepting** direction — the direction ROADMAP 2 warned
   about.
2. **A recursor with `all: []` is malformed**, not undecidable. It was declined,
   and declining let `rogue : False` through.
3. **Fewer motives than family members is malformed.** The pass tested `!=` and
   called both directions "a nested auxiliary recursor"; a nested auxiliary has
   *more*. Measured over 3410 real recursors: 0 fewer, 183 more.
4. **A recursor's name ties it to its inductive.** Must be `<member>.rec` or
   `<member>.rec_N`; all 3410 are, with no exception to carve.
5. **Recursiveness sometimes needs reduction**, and the iota pass decided it
   syntactically. The ambiguous case now declines instead of deriving a wrong
   rule. Plus a fourth pass, `safety.py`, for the `unsafe`/`partial` flags the
   frontend was reading and throwing away.

## Six of the fourteen were caught for the wrong reason

The fixes targeted five tests and the count moved by fourteen. **An unexplained
improvement is as suspicious as an unexplained regression**, so:
`050_inductWrongCtorParams`, `051_inductWrongCtorResParams`,
`052_inductWrongCtorResLevel`, `053_inductInIndex`, `056_reduceCtorType.mk` and
`061_typeWithTooHighTypeField.mk` are all rejected by one rule —
`0 motives for a family of 1` — and **none of them is about recursors**.

`050` is the clearest. Its inductive declares a parameter of type `Sort 0`
while its constructor takes one of type `Sort 1`. kernel3 has no opinion about
that mismatch. What it does have an opinion about is the recursor the file
carries alongside, which is a **stub**: 0 motives, 0 minors, 0 rules, typed
`Sort 0`. Lean could not generate a real recursor for an ill-formed inductive,
so the author attached a degenerate one, and the new motive rule trips on that.

The outcome is right and the mechanism is adjacent to the defect. **Had the
author attached a plausible-looking recursor, kernel3 would accept these six
again.** They count in the fourteen because the arena scores outcomes; they are
called out here because this repository scores mechanisms — `evidence/ablation.json`
exists for exactly this distinction.

## The nine that remain

| cause | tests |
| --- | --- |
| projection typing on `Prop` / `imax` | `proj-of-imax-prop`, `090_projProp2`, `092_projProp4`, `093_projProp5`, `094_projProp6` |
| declaration well-formedness | `012_nonPropThm`, `014_selfProof` |
| inductive well-formedness | `047_inductBadNonSort2`, `049_inductTooFewParams` |

These are outside what `kernel3` checks rather than bugs in it: the projection
typing rule, whether a theorem's type is a `Prop`, whether a definition refers
to itself, and whether an inductive's own declaration is well formed. Closing
them would turn a term-layer corroborating checker into a full kernel, which is
a different decision and is not taken here.

> **That paragraph was wrong about two of the nine, and it is corrected below
> rather than edited away.** `014_selfProof` and `012_nonPropThm` are not a
> scope boundary; they are missing checks, decidable by reading the
> declaration. See "Round 9" at the end of this document.

And note what `047` and `049` are: inductive well-formedness tests whose
recursors happen to be *plausible* — which is exactly what the six incidental
catches would look like if their stubs were better.


---

# Round 9: two of the nine were missing checks, not scope

**ROADMAP 3.** Two of the nine remaining misses are not about terms,
inductives or flags. They are about whether the declaration is a declaration:

```
bad/tutorial/014_selfProof    theorem selfProof : (p : Prop) → p := selfProof
bad/tutorial/012_nonPropThm   theorem nonPropThm : Prop := (x : Prop) → x
```

`014` is **the most obvious bogus proof there is.** The theorem's value is a
reference to itself, so it type-checks against its own declared type, and what
it proves is `∀ p : Prop, p` — everything, `False` included. Lean rejects it
for a structural reason `kernel3` did not share: Lean adds a declaration to the
environment only *after* checking it, so the self-reference is an unknown
constant. `kernel3`'s reader adds first and checks after, which makes the
constant resolve.

Calling that "outside what `kernel3` checks" was **an overstatement of this
checker's scope boundary.** It is a missing check, and `harness/kernel3/
declaration.py` is a fifth specification pass that makes it:

1. **A value may not mention its own declaration.** In an export, never
   legitimately: Lean compiles every form of recursion away before a value is
   exported — structural through `brecOn`, well-founded through
   `WellFounded.fix`, a mutual block through one `brecOn` application.
2. **A theorem's statement may not be a universe.** The type of `∀ …, Sort u`
   is `Sort (imax … (u+1))` and never `Prop`, whatever the levels are, so a
   `thm` with that type is a definition carrying a theorem's label.

## The containment claim above was also wrong for these two

This document says most of the misses are contained because "the provenance
gate reports any assumed declaration whose fingerprint is not in the trusted
baseline". **That mechanism does not apply here.** Both are *defined*
declarations carrying a value, not assumed ones, so the gate has nothing to
report — `introduced_assumptions` is `0` for both, in this document's own
evidence file.

What contains them inside AMPAS's pipeline is the **compile step**: a
submission is compiled by Lean, which rejects both before an export exists.
That is a real containment and a different one, and it is precisely the
containment [ASSUMPTIONS A3](../ASSUMPTIONS.md) says evaporates when the
checker is pointed at an export of unknown provenance — which is what the
arena is.

## What the rules were measured against before being believed

ROADMAP 2's discipline applies: both rules are in the **rejecting** direction,
so the risk is rejecting legitimate work rather than accepting a forgery.

| export | valued declarations | violations |
| --- | --- | --- |
| `AmpasRef.Guards` + its Init closure | 1250 of 1466 | 0 |
| `AmpasRef.ChallengeMathlib` + its Mathlib closure | 2599 of 2978 | 0 |

Record: [`evidence/declaration_differential.json`](../evidence/declaration_differential.json).
A single violation there would mean the rule is wrong rather than Lean.

This pass needs a **full** export, not a `--specs` one: it reads values, and
`--specs` carries only assumed declarations, which have none.

**One rule was measured and not adopted.** A value mentioning another member
of its own mutual block should be as impossible as mentioning itself, and the
differential finds **0** of those across all 3849 valued declarations — but
nothing in the arena pins it, and "should" is the word that put three bugs in
the iota pass. It is recorded as `mutual_block_references` and is not a
violation, so a rule can be added later on evidence instead of expectation.

## The measurement

| configuration | wrongly accepted | wrongly rejected | correct | declined |
| --- | --- | --- | --- | --- |
| round 7, `with_spec_passes` | 9 | 9 | 170 | 10 |
| round 9, `with_spec_passes` | **9 → 7** | 9 → 8 | 172 | 10 → 11 |

Record: [`evidence/arena_run_round9.json`](../evidence/arena_run_round9.json).

**Only the first column is this round's work, and only two tests moved for it:**
`012_nonPropThm` and `014_selfProof`, both `ACCEPTED → REJECTED`. The targeted
count and the actual count agree, which round 7's six incidental catches are
the reason for checking.

**`wrongly_rejected` 9 → 8 is NOT an improvement and is not claimed as one.**
`good/perf/proj-cheap-struct` moved `REJECTED → DECLINED` because it was
killed by the OOM killer — `exit -9` at 71 seconds under a 180-second
timeout — since this run shared the machine with other work. A resource kill
is not a verdict, which is the distinction `INCONCLUSIVE` exists for
throughout this repository, and the `declined` column rising by the same one
is the same event counted in the other direction. The term layer still rejects
that test for the structure-eta reason TC-01 describes.

## The seven that remain

| cause | tests |
| --- | --- |
| projection typing on `Prop` / `imax` | `proj-of-imax-prop`, `090_projProp2`, `092_projProp4`, `093_projProp5`, `094_projProp6` |
| inductive well-formedness | `047_inductBadNonSort2`, `049_inductTooFewParams` |

The five projection tests are a genuine typing rule this checker does not
implement, and the two inductive ones are the hole A3 describes — the same one
six of round 7's "caught" tests fall into, as that section says. For those
seven the scope sentence above stands; for `012` and `014` it did not.
