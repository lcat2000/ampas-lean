# Evidence from the recorded run

**繁體中文：[INDEX.zh-TW.md](INDEX.zh-TW.md)**

These are the results of the run recorded in the repository. `scripts/verify.sh`
writes **fresh** results into `build/` instead of overwriting these, so you can
diff your run against the record.

| File | Content | Reproduced by |
| --- | --- | --- |
| `environment.json` | toolchain, the provenance/scope of each of the three checks and their hashes, the sandbox and the resource limits. The third check's `provenance` / `covers` / `does_not_cover` fields are here | recorded by hand plus hashing |
| `corpus_results_threechecks.json` | core corpus, 16 submissions, all three checks | `harness/ampas_lean.py corpus/manifest.json` with `AMPAS_THIRD_CHECK=1` |
| `corpus_results_mathlib3.json` | Mathlib corpus, 2 submissions, all three checks | the same, with `AMPAS_CLAIMS` / `AMPAS_EXTRA_LEAN_PATH` / `AMPAS_KERNEL_BASELINE` for the Mathlib tier |
| `fermat_validation.json` | the external validation pair, 5 submissions | `harness/ampas_lean.py corpus/manifest_fermat.json` with the Fermat catalogue |
| `ablation.json` | which layer actually caught each attack — **not** merely that all were rejected | `harness/ablation.py <the result files>` |
| `review_verification.json` | the 10 core claims: freeze, signature, guards, drift detection | `harness/ampas_review.py verify` |
| `review_verification_mathlib.json` | the same for the Mathlib claim | the same with `AMPAS_CLAIMS` |
| `baseline_fresh_replay.json` | `leanchecker --fresh`: all of Init replayed into an empty kernel (a one-off baseline, ~3 min) | `baseline()` in `harness/ampas_lean.py` |
| `sample_reports.json` | full driver output for a few submissions, as a format sample | driver output |
| `positivity_differential.json` | the positivity pass run over every inductive in the trusted reference set and the Mathlib set | `harness/positivity_diff.py` (see below) |
| `corpus_results.json` | round-1 record (single kernel) | history |
| `corpus_results_twokernels.json` | round-2 record (two kernels, no third check) | history |
| `corpus_results_mathlib.json` | round-2 Mathlib record | history |

The history files are kept so the rounds can be compared: between rounds 2 and
3 the only difference should be the third check's fields, with the verdicts
themselves unchanged. They are, and `tests/test_math_verification.py` would
notice if they were not.

**Note on paths.** The recorded files contain absolute paths from the machine
that produced them (`/home/claude/...`). They are a record of that run, not
configuration; nothing reads them back.

## counterexample_search*.json — bounded counterexample search

`build/counterexample_search.json` (core), `..._mathlib.json`, `..._fermat.json`,
reproducing the committed `reference/counterexample_search*.json`.

    export AMPAS_TRUSTED_OLEAN=$PWD/.lake/build/lib/lean
    python3 harness/counterexample.py --out build/counterexample_search.json

What each field means, and what a clean result is allowed to mean, is in
ASSUMPTIONS A1b. The number to look at first is `checked_points` against
`box_size`: points where a hypothesis failed say nothing about the conclusion,
and points that could not be decided say nothing either, so only the remainder
actually exercised the statement. The validation case is FERMAT-CLAIM, which
must come back REFUTED with witness `[5]`.

## derivation_search.json — bounded derivation search

`build/derivation_search.json`, reproducing `reference/derivation_search.json`,
plus the generated witnesses in `build/refutations/`.

    export AMPAS_TRUSTED_OLEAN=$PWD/.lake/build/lib/lean
    python3 harness/derivation_search.py --out build/derivation_search.json

The four independence claims, which the numeric search cannot reach.
PL-BOGUS must come back REFUTED, and the fields to read are under `kernel`:
`kernel_replay` and `kernel_replay_fresh` (elaboration is not the kernel), and
`statement_check.negates_frozen_statement_structurally` — without that, a
refutation might be about a statement adjacent to the frozen one, which is the
`FermatWeaker` failure mode pointed the other way. `axioms: []` means the
refutation rests on nothing at all.

For the other three, read `bound` before reading `outcome`: NO_DERIVATION
means nothing was found inside that universe, and nothing more. ASSUMPTIONS
A1c is the full statement of what it is and is not worth.

## record_corrections — known-wrong fields in a historical record

`evidence/corpus_results_threechecks.json` carries a `record_corrections`
entry. It names a field this repository now knows to be wrong in that file,
the value recorded, the correct value, and why the file was annotated rather
than regenerated.

The case: `third_check.status` for `A01_kernel_bypass` reads
`DISAGREEMENT (unadjudicated)`. All three checkers in fact agreed — the
declaration was rejected by the third check and by both Lean kernels, and
`kernel_replay: false` / `kernel_replay_independent: false` are recorded in
the same file. The status was computed from the third check's errors alone and
never consulted them. `evidence/ablation.json` recorded the truth
("primary kernel, independent kernel, third check") the whole time; the two
records disagreed for nine rounds and nothing compared them.

**Why it was not regenerated.** This file is the tier-3 reference run, with
lean4lean and the Mathlib corpus. Re-running it here would produce a tier-1
core-only record and lose the `independent kernel` signal and the Mathlib
rows — replacing a historical record instead of annotating it. No verdict in
the file was ever affected: A01 is rejected either way.

`tests/test_record_consistency.py` honours the annotation and requires it to
still be needed: if the field ever stops carrying the wrong value, the test
fails and asks for the correction to be removed. A correction cannot be used
to excuse an arbitrary value either — it must name the value the file
actually contains.

## reverification.json — which stored verdicts would not reproduce today

    export AMPAS_TRUSTED_OLEAN=$PWD/.lake/build/lib/lean
    python3 harness/reverify.py --out build/reverification.json
    python3 harness/reverify.py --rerun      # actually re-execute the corpus

Compares each stored record's `provenance` block against the live toolchain
and the current `reference/kernel_advisories.json`. States: AFFECTED,
KERNEL_CHANGED, NO_PROVENANCE, SAME_KERNEL.

**Read `re_execution` before reading the states.** Without `--rerun` nothing
is re-executed, so SAME_KERNEL means a record would be *expected* to
reproduce, not that it did.

Today every stored record in `evidence/` is NO_PROVENANCE: they were issued
before provenance was recorded, so their kernels cannot be identified from
the record. That is thirty certified claims, and the gap closes forwards only.

## positivity_differential.json — strict positivity, differentially tested

    export AMPAS_TRUSTED_OLEAN=$PWD/.lake/build/lib/lean
    LEAN_PATH=$AMPAS_TRUSTED_OLEAN lean --run harness/Export.lean \
        --specs AmpasRef.Guards build/guards.specs
    python3 harness/positivity_diff.py build/positivity_core.json \
        AmpasRef.Guards=build/guards.specs

`scripts/verify.sh` runs this at tier 1 and adds the Mathlib set at tier 3,
which is where the committed record comes from.

`harness/kernel3/positivity.py` decides strict positivity for an inductive
specification. **Read the asymmetry before reading the numbers:**

- a **VIOLATION** over these sets would be a bug in the pass, not a finding
  about Lean — Lean's own kernel accepted every one of these declarations when
  the modules were built. The script exits non-zero on one.
- **UNCLASSIFIED** is the pass declining to decide, which is the direction a
  mistake is allowed to go. It is recorded with a reason per declaration so
  that growth in it is visible rather than silent.
- **OK** says this pass agrees with Lean where it has an opinion. It does
  **not** say the specification is checked.

The record: 3285 inductives, 0 violations, 45 unclassified — all 45 the nested
shape, a recursive occurrence under another inductive's parameter (`Array`,
mostly), which needs that inductive's own positivity.

**What a clean result here does not buy.** Positivity is one of three
properties `harness/kernel3` assumes about an inductive; the recursor's shape
and the iota rules are the other two and neither is checked anywhere in this
repository. So a specification that passes positivity can still be a forgery —
`tests/forgeries/forge_large_elim.export` is one, and it passes this pass
because what it forges is the recursor. The provenance gate is what catches
it, and this pass does not relax it. ASSUMPTIONS A3 and ROADMAP 2.
