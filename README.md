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
| **Second kernel** ([lean4lean](https://github.com/digama0/lean4lean)) | A second kernel re-checks the same oleans; certification requires **both**. Upstream describes it as "derived directly from the C++ kernel implementation … not really an independent implementation", so this buys agreement between relatives, not independent confirmation — see ASSUMPTIONS A2 |
| **Third check** ([`harness/kernel3`](docs/review-third-check.md)) | A from-scratch type checker in Python sharing no code with Lean — corroborates the *term layer* only |
| **Axiom audit** | Transitive axioms against a per-claim policy; flags `sorryAx`, native evaluation, `opaque` in statements, `unsafe`, `partial` |
| **Closure check** | Every constant the statement depends on, **including definition bodies**, compared against the reference |
| **Statement comparator** | The elaborated statement against the frozen one, structurally or up to kernel definitional equality |
| **Counterexample search** | Before a statement can be frozen, a bounded search tries to falsify it, and the result is signed into the record. Fermat's claim dies at n = 5 |
| **Formalization sign-off** | A content-addressed freeze, machine-derived guard theorems, an Ed25519 signature, and drift detection |
| **Checklist evidence** | Five of the reviewer's six checklist items now point at the object they are a claim about — the binder order, the conventions in play, the definitions, the conclusion — each bound to the statement's hash. The sixth, `statement_matches_text`, points at nothing and is marked so |

The last row is the one that cannot be automated, and the repository does not
pretend otherwise: a checker carrying a ZFC model-theoretic consistency proof
accepts a well-formed statement of the wrong claim
([docs/CONLECHE-EVALUATION.md](docs/CONLECHE-EVALUATION.md)). What the
evidence makes visible is carelessness, not error. See
[docs/review-formalization.md](docs/review-formalization.md) and ASSUMPTIONS A1e.

## Results of the recorded run

| Corpus | Submissions | Outcome |
| --- | --- | --- |
| Core (`corpus/manifest.json`) | 16 (4 genuine, 12 attacks) | 16/16 as expected; both Lean kernels agreed on all; third check confirmed 15 and **corroborated** the Lean kernels on the kernel-bypass attack — it objected to the same declaration they rejected, and caught nothing they missed |
| Mathlib (`reference/claims_mathlib.json`) | 2 | 2/2 as expected |
| External validation (`corpus/manifest_fermat.json`) | 5 | 5/5 as expected |
| External validation, historical (`corpus/manifest_history.json`) | 11 (3 genuine, 8 attacks) | 11/11 as expected; 6 claims from three episodes whose verdicts this repository did not set |
| Counterexample search | 13 statements | 1 refuted (Fermat's claim, at n = 5, as it should be), 8 searched clean, 4 out of reach and recorded as such |
| Counterexample search, historical | 6 statements | 2 refuted unaided (Euler's polynomial at n = 40, and Mersenne's p = 67 entry — the search reproduces Cole's 1903 factorization); **1 false claim it cannot reach and says so** (Euler's sum of powers; the 1966 witness needs 144 in five variables) |
| Derivation search | the 4 out of reach | PL-BOGUS refuted — kernel-accepted, no axioms; 3 NO_DERIVATION over a stated universe |
| Triangulation | 3 claim pairs | 3 EQUIVALENT, checked against the named statements — and the method's limit proved as a theorem (A1d) |
| Tests | 370 | all pass from a clean checkout (the Mathlib and tier-3 fixtures skip below tier 3) |

Every attack is rejected **by the layer that should catch it**, not merely
rejected — `build/ablation.json` records which signal fired for each, because
a suite where one layer does all the work while the others do nothing would
look identical on a pass/fail summary.

### The external validation corpora

The corpus was written by the same hands as the harness, so it was also tested
on cases taken from the history of mathematics instead, where the verdict was
settled by someone else long before this repository existed. Four episodes,
eight claims, sixteen submissions.

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

Three more episodes were added in the same shape (`reference/claims_history.json`,
11 submissions, all landing where the manifest says):

| Episode | The false claim | Settled against it by |
| --- | --- | --- |
| Mersenne, 1644 | $2^{67}-1$ is prime (the $p=67$ entry of his list) | Cole, 1903: $2^{67}-1 = 193707721 \times 761838257287$ |
| Euler, 1769 | no fifth power is the sum of four positive fifth powers | Lander and Parkin, 1966: $27^5+84^5+110^5+133^5 = 144^5$ |
| after Euler, 1772 | $n^2+n+41$ is prime for every $n$ | $40^2+40+41 = 1681 = 41^2$ |

They were picked to land on different layers, and what they showed is worth
more than the fact that all 11 submissions came out right:

- Euler's polynomial dies to the bounded search at $n = 40$, and Mersenne's
  entry dies to it as well — the decision procedure finds the factor
  193707721 in a few minutes, so the search reproduces Cole's 1903 result on
  its own.
- Euler's sum-of-powers conjecture is **false and the search cannot reach
  it**: the 1966 witness needs 144 in five variables. It returns "no
  counterexample" on a false claim. That is what a bounded numeric search is,
  shown on a claim this repository did not choose.
- And the corpus found four defects in the harness, all the same kind of
  mistake — a derived label read from, or asserted without, the data beside
  it. The layer-attribution table identified attacks by a filename prefix, so
  **every external attack, including the four Fermat ones, had been missing
  from it since the Fermat pair was added**; a control field written
  `target_claim_is` instead of `target_claim_is_true` read correctly to a
  human and was invisible to the code; a third-check status said
  "adjudicated" beside an empty adjudication field, and the adjudications it
  meant are themselves unconfirmed; and that same status was being credited
  with catching four attacks it had caught nothing about. A fifth finding:
  `evidence/ablation.json` could not be reproduced by `verify.sh` — it has a
  thirteenth row that only tier 3 produces. All in ROADMAP 6a.

What a historical claim fixes is the verdict, not the formalization. Whether
each Lean statement says what the historical sentence says is still a
judgement, and nobody has made it: every review block in the new catalogue is
`PENDING`.

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

# tier 2 — add the second kernel
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
- **A certificate now names the kernel that issued it — but only from
  2026-10-14.** Every verdict record carries the Lean version and binary
  hash, both kernels' identities, the pins, and an advisory status, so a
  certificate can be found again after a soundness disclosure
  (`harness/reverify.py` answers "which stored verdicts would not reproduce
  today"). Two things to read carefully: a clean advisory result means "no
  advisory in one hand-maintained list, as of its review date, names this
  kernel" and **not** that the kernel is sound; and every record issued before
  that date reports NO_PROVENANCE — thirty certified claims whose kernel
  cannot be identified. ASSUMPTIONS A2b.
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

1. Replace cross-kernel agreement as the strongest claim. It is defeatable
   (Tao, 2026-10-09) and, worse, **this suite's second kernel was never an
   independent implementation** — upstream calls it "derived directly from the
   C++ kernel implementation" (ROADMAP 1.3a, corrected 2026-10-14).
   [con-leche](https://github.com/leanprover/con-leche), whose acceptance is
   *proved* to imply a set-theoretic model, accepts a genuine submission here
   in 43 seconds and is available as an optional tier
   (`scripts/check-with-conleche.sh`, [evaluation](docs/CONLECHE-EVALUATION.md)).
   It also **accepts `A06_wrong_statement`** — so a verified kernel does not
   close the fidelity gap either.
2. The third check has **five** differentially tested specification passes —
   positivity (3285 inductives), the recursor's shape and the iota rules (3410
   recursors each), `unsafe`/`partial` flags, and declaration well-formedness
   (3849 valued declarations over Init and Mathlib), 0 violations throughout.
   What remains assumed has *moved* rather than gone: the inductive passes
   check a declaration against the rules Lean would have followed, none shows
   that Lean produced it, so the provenance gate is still what catches a
   forgery. See ROADMAP 2 and 3a.

   Measured from outside against the [Lean Kernel
   Arena](https://arena.lean-lang.org/)'s 198 third-party tests: **28 → 7**
   wrongly accepted of the 72 that must be rejected
   ([docs/ARENA-RESULT.md](docs/ARENA-RESULT.md)). Still a poor score —
   con-leche and lean4lean each have 0 — and the figure is kept in the record
   rather than in prose.
3. Bind the signing key to an identity outside this repository. As of
   2026-10-13 all 13 attestations are signed by a key held by the repository
   owner rather than by the build container, which was the gap. What is left
   is that nothing ties that key to him except the record's own say-so: a
   fingerprint published elsewhere, or signed commits, would make the
   attribution checkable by a stranger.
4. Widen review beyond one reader. One confirmation is independent of the
   harness's author — the property that was missing — but it is not open
   review.

### Where the work stands, 2026-10-14

Every mechanical layer in this repository detects **falsity or
malformedness**. None of them reads English. So the remaining work splits
cleanly into what code can still do and what it cannot, and the second list is
the one that matters.

**What code can still do** — in the order they are worth doing:

| # | Item | Why it is next |
| --- | --- | --- |
| ROADMAP 3 | TC-01 and TC-02, the third check's two recorded incompleteness findings | Both are in the **rejecting** (safe) direction, and the arena confirmed they describe real mechanisms rather than convenient ones. The arena is now the external guard that makes fixing in the widening direction measurable. |
| ROADMAP 3a | The arena's seven remaining misses: five projection-typing tests on `Prop`/`imax`, two inductive well-formedness | The five are a genuine typing rule this checker does not implement — a larger job than the two declaration rules that took the count 9 → 7. The two inductive ones are the hole ASSUMPTIONS A3 describes. |
| ROADMAP 7 | The Mathlib build cache | The cheapest win on the list: it turns a 20-minute tier-3 build into a download. Blocked on `leantar` and an unreachable crates.io in the recorded environment. |
| ROADMAP 8 | Resource limits that scale with the host | A run on a busy machine already produced one spurious `DECLINED` from the OOM killer (round 9). A resource kill is not a verdict, and the record says so, but the limits should not need that defence so often. |

**What code cannot do.** Five of the reviewer's six checklist items now point
at a named object bound to the statement's hash
([ASSUMPTIONS A1e](ASSUMPTIONS.md)). The sixth, `statement_matches_text`, is
marked `machine_derivable: false` and will stay that way: it compares a formal
object to an English sentence, and `docs/CONLECHE-EVALUATION.md` measured what
that means — a checker carrying a ZFC model-theoretic consistency proof
accepts `A06_wrong_statement`. **That one item now carries the whole fidelity
gap.** Its honest next steps need people, not passes:

- **ROADMAP 5.3, back-translation.** Render each frozen statement back into
  natural language and have it compared against the original by someone who
  has not seen the Lean. The protocol is cheap; the reader is the thing this
  repository does not have.
- **ROADMAP 4, open review.** One confirmation is independent of the harness's
  author. That is the property that was missing, and it is not the same as
  review by people with no stake in the result.
- **ROADMAP 6b, submissions written by other people.** Every adversarial
  vector in this repository was written here, except the 198 arena tests and
  the four historical corpora — and those two were worth more than everything
  written in-house, because *nothing is caught by its own unit tests*. That is
  this project's most repeated finding, with roughly fifteen instances on
  record: a label-class defect needs a second record of the same event, and a
  model-class defect needs a declaration set written by someone else.
- **README item 3 above, the signing key.** Nothing ties the key to its holder
  except the record's own say-so. This one needs an action outside the
  repository rather than a commit inside it.

## Licence

Apache-2.0 — see [LICENSE](LICENSE).

The Lean toolchain and Mathlib are separate works under their own licences
(both Apache-2.0); `lean4lean` is upstream at
[digama0/lean4lean](https://github.com/digama0/lean4lean) and is fetched, not
vendored.
