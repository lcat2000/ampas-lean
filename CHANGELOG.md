# Changelog

Dates are the verification rounds, not releases.

## 0.3.0 — the third check, and what it does not establish

Reviewed the from-scratch Python type checker that had appeared in the harness
unreviewed, line by line, and wired it in as a **third** check with its scope
enforced in code rather than in prose.

**Findings**

- **F-1 (high, fixed)** — a `--statement` export (types, no proofs) reported
  `27/27 checked, 0 errors`. `env.mode` was parsed and never checked. Now
  refused, and `#THMTYPE` declarations are reported as unproved.
- **F-2 (high, contained not fixed)** — inductive specifications are assumed,
  not derived. Two hand-written forgeries prove `False` through the hole
  (`Prop` large elimination; a non-positive inductive). A small-elimination
  control is correctly rejected, which locates the hole in the specification
  layer. Contained by a provenance gate that reports any assumed declaration
  outside the trusted baseline instead of vouching for it. Not fixed because
  widening what a checker under review accepts is the unsound direction.
- **F-6 (medium)** — iota reduction lacks to-constructor-when-structure, so the
  checker is incomplete on instance-heavy library code. **This overturned the
  gate design**: "third check errors ⇒ reject" looked fine on the core corpus
  (16/16) but vetoed a correct, twice-kernel-verified Mathlib proof. Letting
  the least complete of three implementations overrule the other two was wrong.
- **F-3/F-4/F-5 (low)** — `instantiate` does not lift substituted loose bvars
  (currently unreachable); `_reduce_proj` does not check the projected
  structure; `Nat.pow` is unbounded.

**Also fixed**

- A resource limit is no longer read as a kernel rejection. Exit 124 / −24 /
  −9 / 137 / `TIMEOUT` now yields `INCONCLUSIVE` — never certified, but not a
  statement about the proof. Found when two concurrent test sessions on a
  two-core machine made a certified claim flip to rejected.
- The provenance baseline is now the whole trusted environment (2,157 assumed
  declarations) rather than the reference statements' closure (213), which had
  reported legitimate Init inductives as introduced assumptions for three
  correct submissions.
- Baselines store fingerprint hashes rather than serialized types: 14 MB → 800 KB.

**Added** `harness/make_baseline.py`, `harness/ablation.py`,
`tests/test_third_check.py` (18 tests, 13 of them needing no Lean),
`tests/forgeries/`, `reference/third_check_adjudications.json`.

**External validation.** Tested on a case from the history of mathematics
rather than the suite's own corpus: Fermat's assertion that every Fermat number
is prime (c. 1640, false) against Euler's refutation (1732,
$F_5 = 641 \times 6700417$). Five submissions, 5/5 as expected. The informative
one proves the restricted statement `n ≤ 3` under the general claim's name —
no `sorry`, no added axiom, both kernels satisfied — and only the statement
comparator catches it.

This run also surfaced **TC-02**, a fourth incompleteness instance with a
distinct mechanism (`level_leq` cannot decide a nested `imax` identity). It
changed no verdict: every affected submission had an independent real reason to
be rejected.

**Packaged for publication**: Lake project with a pinned toolchain, tiered
verification scripts, path-independent harness, interpreted-auditor fallback so
no C toolchain is required, CI over tiers 0–1.

## 0.2.0 — a second kernel, a sign-off process, and Mathlib

- **Second independent kernel**: lean4lean at a pinned revision. Certification
  requires both Lean kernels. 18/18 submissions agreed; the kernel-bypass
  attack was rejected by both.
- **Formalization sign-off**: content-addressed freeze of the *elaborated*
  statement plus the dependency closure *including definition bodies*;
  guard theorems whose types the auditor computes from the statement;
  Ed25519 signatures; drift detection. 11 claims frozen and signed, 0 failures;
  7 drift tests, including the case where a definition changes while the
  statement text stays byte-identical.
- **Axiom independence**: A3 shown independent of A1+A2 via negation-as-identity.
  This exposed a design flaw — a refutation (`¬P`) was being asked for a
  non-vacuity proof of the very thing it refutes — now handled as a
  `REFUTATION` requiring a nontriviality guard instead.
- **Mathlib** pinned by revision and built from source (no prebuilt cache),
  one claim end-to-end, plus an attack that shadows `Nat.Prime` and is caught
  by the closure check naming it.
- Unreviewed code found in the harness was quarantined to `unreviewed/`.

## 0.1.0 — a pipeline that actually runs Lean

Established that earlier rounds had never executed Lean, and built the
pipeline: sandboxed compile, kernel replay, the auditor (axiom closure,
statement comparison, flags), a 15-submission adversarial corpus with recorded
per-attack catching layers, and reproduction from a clean copy.
