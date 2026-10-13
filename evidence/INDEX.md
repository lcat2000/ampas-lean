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
