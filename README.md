# AMPAS — a Lean proof-verification harness, and an honest account of its limits

[![tier 0–1](https://img.shields.io/badge/verify-tiers%200--3-informational)](#verifying-it-yourself)
[![Lean](https://img.shields.io/badge/Lean-4.33.0-blue)](lean-toolchain)
[![licence](https://img.shields.io/badge/licence-Apache--2.0-green)](LICENSE)

**繁體中文版：[README.zh-TW.md](README.zh-TW.md)**

This repository checks submitted Lean 4 proofs against *frozen* reference
statements, and it is built around one distinction:

> A Lean kernel accepting a theorem means its proof type-checks **under the
> axioms and definitions it actually used**. It does not mean the original
> natural-language mathematical claim has been proved.

Most of the engineering here is about the gap between those two things, and
about not overstating what any one checker establishes. The parts that detect
nothing are documented as carefully as the parts that do:
[ASSUMPTIONS.md](ASSUMPTIONS.md) is the file to read before trusting any
result from this repository.

## What it actually does

A submission is a `.lean` file claiming to prove one of the frozen reference
statements. It goes through:

| Layer | What it establishes |
| --- | --- |
| **Sandboxed compile** | Unprivileged user, read-only trusted oleans, CPU/memory/file-size caps, trusted artifacts hashed before and after |
| **Kernel replay** (`leanchecker`) | Lean's own kernel re-checks every declaration from the olean |
| **Second kernel** ([lean4lean](https://github.com/digama0/lean4lean)) | An independently written kernel re-checks the same oleans. Certification requires **both** |
| **Third check** ([`harness/kernel3`](docs/review-third-check.md)) | A from-scratch type checker in Python sharing no code with Lean — corroborates the *term layer* only |
| **Axiom audit** | Transitive axioms against a per-claim policy; flags `sorryAx`, native evaluation, `opaque` in statements, `unsafe`, `partial` |
| **Closure check** | Every constant the statement depends on, **including definition bodies**, compared against the reference |
| **Statement comparator** | The elaborated statement against the frozen one, structurally or up to kernel definitional equality |
| **Counterexample search** | Before a statement can be frozen, a bounded search tries to falsify it, and the result is signed into the record. Fermat's claim dies at n = 5 |
| **Formalization sign-off** | A content-addressed freeze, machine-derived guard theorems, an Ed25519 signature, and drift detection |

The last row is the one that cannot be automated, and the repository does not
pretend otherwise. See [docs/review-formalization.md](docs/review-formalization.md).

## Results of the recorded run

| Corpus | Submissions | Outcome |
| --- | --- | --- |
| Core (`corpus/manifest.json`) | 16 (4 genuine, 12 attacks) | 16/16 as expected; both Lean kernels agreed on all; third check confirmed 15 and **corroborated** the Lean kernels on the kernel-bypass attack — it objected to the same declaration they rejected, and caught nothing they missed |
| Mathlib (`reference/claims_mathlib.json`) | 2 | 2/2 as expected |
| External validation (`corpus/manifest_fermat.json`) | 5 | 5/5 as expected |
| Counterexample search | 13 statements | 1 refuted (Fermat's claim, at n = 5, as it should be), 8 searched clean, 4 out of reach and recorded as such |
| Derivation search | the 4 out of reach | PL-BOGUS refuted — kernel-accepted, no axioms; 3 NO_DERIVATION over a stated universe |
| Triangulation | 3 claim pairs | 3 EQUIVALENT, checked against the named statements — and the method's limit proved as a theorem (A1d) |
| Tests | 207 | all pass from a clean checkout (218 collected; the Mathlib fixtures skip below tier 3) |

Every attack is rejected **by the layer that should catch it**, not merely
rejected — `build/ablation.json` records which signal fired for each, because
a suite where one layer does all the work while the others do nothing would
look identical on a pass/fail summary.

### The external validation pair

The corpus was written by the same hands as the harness, so it was also tested
on a case taken from the history of mathematics instead:

- **Fermat** (c. 1640) asserted every Fermat number $F_n = 2^{2^n}+1$ is prime,
  having checked $F_0 \ldots F_4$. The claim is **false**.
- **Euler** (1732) refuted it: $F_5 = 4294967297 = 641 \times 6700417$.

| Submission | Expected | Result | Caught by |
| --- | --- | --- | --- |
| Euler's refutation, from the factorization | certified | **CERTIFIED** | — (axioms: `propext` only) |
| Fermat's claim: the cases he checked, then `sorry` | rejected | **REJECTED** | axiom policy (`sorryAx`) + `SORRY` flag |
| Fermat's claim with **no `sorry`**, gap moved into an `axiom` | rejected | **REJECTED** | axiom policy, naming the axiom |
| Fermat's claim, **every line genuinely proved** — of the restricted statement `n ≤ 3`, filed under the general claim | rejected | **REJECTED** | statement comparator |
| Euler's statement, but proving it for $2^{32}$ rather than $2^{32}+1$ | rejected | **REJECTED** | statement comparator |

The third row is the one worth dwelling on: no `sorry`, no extra axiom, honest
Lean, both kernels satisfied — and the formalization simply is not the claim it
is filed under. Only the statement comparator stands between that and a
certificate.

## Verifying it yourself

Four tiers. Each is self-contained, and a tier you cannot run never
invalidates one you can.

```bash
git clone https://github.com/lcat2000/ampas-lean.git && cd ampas-lean

# tier 0 — no Lean needed, a few seconds
pip install pytest
python3 -m pytest tests/test_third_check.py -q -k "not pipeline"

# tiers 0–1 — pinned Lean toolchain only, ~6 minutes
pip install -r requirements.txt
./scripts/bootstrap.sh
./scripts/verify.sh 1

# tier 2 — add the second independent kernel
./scripts/build-lean4lean.sh && ./scripts/verify.sh 2

# tier 3 — add the Mathlib claims (~20 min, builds Mathlib from source)
./scripts/build-mathlib-tier.sh && ./scripts/verify.sh
```

Full details, including what to do when the auditor will not link, are in
[INSTALL.md](INSTALL.md).

**Tier 0 is the interesting one to run first.** It needs no Lean at all and it
pins the *scope* of the third check against hand-written forgery exports: a
statement-mode export must be refused, two forged inductive specifications that
prove `False` must not be vouched for, and the small-elimination control must
still be rejected. Those tests exist so no later change can quietly widen what
a clean result means.

## What this repository does not establish

The short version; [ASSUMPTIONS.md](ASSUMPTIONS.md) has the full list with the
evidence for each.

- **Formalization fidelity is not machine-decided.** Freezing, signing and
  guards make a human judgement auditable, attributable and resistant to silent
  drift. They do not make it correct.
- **Triangulation is much weaker than it sounds, and the repository proves
  it.** Rendering a claim twice and proving the renderings equivalent was the
  roadmap's most promising idea for checking fidelity. It is not one:
  equivalence of propositions is vacuous between two *true* statements, so an
  equivalence proof cannot distinguish a faithful rendering from a different
  true one. `Ampas.Triangulation.indistinguishable` proves exactly that —
  "the sum of two evens is even" and "the **product** of two evens is even"
  are different claims, both true, equivalent in two applications. Three
  pairs are on record and each rules out a misreading that would have changed
  its claim's truth value; that is what they are worth, and ASSUMPTIONS A1d
  says so rather than letting three green lines imply more.
- **A bounded derivation search refuted one claim and corroborates three.**
  The four independence claims are out of the numeric search's reach, so
  derivations are enumerated instead. PL-BOGUS — a control the catalogue
  declares false — is now **refuted by a derivation the Lean kernel accepted
  with no axioms**, checked against the frozen statement itself; previously
  nothing here proved it false, only that nobody could prove it true. The
  other three come back NO_DERIVATION over a stated universe, which is **not**
  a proof of independence: their truth comes from kernel-checked proofs in the
  corpus, and the search is a cross-check. ASSUMPTIONS A1c is precise about
  the difference.
- **The counterexample search is not evidence of truth.** It refuses to let a
  demonstrably false statement be frozen, which is worth having and is how
  Fermat's claim dies here. But "no counterexample" means no counterexample
  *in a committed box of small values* — with the box set to the evidence
  Fermat himself had, n ≤ 4, it finds nothing — and it says nothing whatever
  about whether a statement means what its text says. It reaches four of the
  thirteen claims not at all, because `PL.Derives` and `EL.Derives` have no
  decision procedure; those records say NOT_SEARCHABLE with the reason rather
  than passing quietly. ASSUMPTIONS A1b has the full list of ways to misread
  a clean result.
- **Multiple kernels agreeing is weaker evidence than it looks.** In 2026
  several Lean kernel soundness bugs surfaced; for one of them, cross-checking
  with an independent kernel *also accepted* the illicit proof because of that
  kernel's own unrelated bug
  ([Tao, 2026-10-09](https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/)).
  Independence of implementations is not independence of failure.
- **The third check corroborates the term layer and nothing more.** It does not
  derive that an inductive specification is legitimate, and two forgeries in
  `tests/forgeries/` prove `False` through that hole. Its provenance gate
  reports such declarations instead of vouching for them.
- **The trusted base shrank but did not vanish.** Lean's *elaborator* (the step
  that produces the olean), the OS and the sandbox are all still trusted.
- **Mathlib coverage is one claim**, over a 387-olean dependency cone, not the
  whole library.
- **The signature now binds the records to a key in the reviewer's custody —
  and custody is a stated claim, not proof of one.** All 13 attestations are
  signed by `kai-chang-2026-10`, a key generated on the repository owner's own
  machine and never present in the container that builds this repository; the
  public key record states that custody, because it cannot be read off a key.
  What that establishes: the records were signed by whoever holds that private
  key, and nothing has been altered since. What it does not establish: that
  the holder is who the record says. There is no external identity binding —
  no web of trust, no certificate, no signed commit chain tying the key to a
  GitHub account — so the custody line is an assertion by the same party it
  describes. Verifying it independently means getting the key's fingerprint
  from him through some other channel.
- **Most fidelity judgements are still not independently reviewed.** All 13
  were reviewed by the same assistant that wrote the harness
  ([REVIEW-CHECKLIST.md](REVIEW-CHECKLIST.md)). **All 13** have since been
  read and confirmed personally by the repository owner, which is an
  independent reading — independent of the harness's author, which is the
  property that was missing. It changed the repository rather than ratifying
  it: EL-IND's text called a trivialized equational theory "inconsistent"
  (wrong — a pure equational theory always has a one-element model); the
  PL-AXIOM-IND guard was worth less than claimed (it excludes only a calculus
  proving nothing at all); the two false-claim controls mixed the claim with
  the verdict on it, so `faithful` was ambiguous, and the two are now separate
  fields; "the fifth Fermat number" was ambiguous for F₅; and a performance
  claim was asserted without evidence. All corrected.

  **What is still missing:** the reviewer judged the definitions as given,
  without re-running Lean himself, so the fidelity judgements and the kernel
  results rest on different parties; the key's custody is asserted by its
  holder and not bound to any external identity; and one reader is not open
  review.
- **`unreviewed/` is not part of the deliverable** and nothing loads it. See its
  README.

## Repository layout

```
reference/     frozen statements, second renderings and their equivalence
               proofs, guards, claim catalogues, attestations, provenance
               baselines, pins, adjudications, search boxes and results
corpus/        test data: genuine submissions, 13 attacks, the Fermat pair
harness/       the driver, the Lean auditor, the third checker, the
               counterexample searcher, baseline and ablation tools
tests/         51 tests, including the offline scope tests and forgery vectors
scripts/       bootstrap and tiered verification
evidence/      results of the recorded run, with an index of what each file is
mathlib-tier/  the optional Mathlib Lake project, kept separate so core claims
               cannot acquire a Mathlib dependency
docs/          the two review documents and build notes
unreviewed/    quarantined code, kept for comparison, loaded by nothing
```

## Next work

[ROADMAP.md](ROADMAP.md), in priority order. The top items:

1. Replace cross-kernel agreement as the strongest claim — it is now known to
   be defeatable — with something stronger, and say what that would be.
2. Close the third check's inductive-specification gap in the one direction
   that is safe: a positivity check, verified against both Lean kernels rather
   than bolted onto the checker under review.
3. Bind the signing key to an identity outside this repository. As of
   2026-10-13 all 13 attestations are signed by a key held by the repository
   owner rather than by the build container, which was the gap. What is left
   is that nothing ties that key to him except the record's own say-so: a
   fingerprint published elsewhere, or signed commits, would make the
   attribution checkable by a stranger.
4. Widen review beyond one reader. One confirmation is independent of the
   harness's author — the property that was missing — but it is not open
   review.

## Licence

Apache-2.0 — see [LICENSE](LICENSE).

The Lean toolchain and Mathlib are separate works under their own licences
(both Apache-2.0); `lean4lean` is upstream at
[digama0/lean4lean](https://github.com/digama0/lean4lean) and is fetched, not
vendored.
