# Next work

In priority order. Each item says why it matters, what "done" looks like, and
what it would cost. Items 1–3 come out of findings in this repository rather
than from a wish list.

---

## 1. Stop treating cross-kernel agreement as the strongest available evidence

**Why.** Certification currently requires two independently written kernels to
accept a submission, and the round-2 write-up presented that as the main
reduction in trusted base. External evidence weakens that claim: in 2026
several Lean kernel soundness bugs surfaced, and for one of them cross-checking
with an independent kernel **also accepted** the illicit proof, because that
kernel had an unrelated bug of its own
([Tao, 2026-10-09](https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/)).
Independence of implementations is not independence of failure.

**What to do, in increasing order of strength:**

1. **Record kernel provenance per verdict.** Each certificate should name the
   kernel binaries, their revisions and their *known-bug status as of the run*,
   so a certificate issued before a disclosure can be found and re-checked
   afterwards. Cheap, and the thing most obviously missing today.
2. **Re-verification on disclosure.** A command that re-runs every stored
   attestation against current kernels and reports which certificates no longer
   reproduce. Medium effort; needs the attestations to carry enough to replay.
3. **Add a checker that is different in kind, not just in authorship.** Both
   current kernels implement the same algorithm from the same specification. A
   *verified* kernel — one whose soundness is itself proved relative to a set
   theory — fails differently. Con-Leche and the verified fragment of lean4lean
   are the candidates to evaluate.
4. **Statement-level redundancy.** For a claim that matters, require two proofs
   by routes that share as little of the library as possible, and compare their
   axiom closures. This catches a library-level problem that any number of
   kernels would miss.

**Done when:** a certificate names its kernels and their bug status, and
`verify.sh` can answer "which stored certificates would not reproduce today".

## 2. Close the third check's inductive gap — but only in the safe direction

**Why.** `harness/kernel3` assumes every inductive declaration is a legitimate
specification. Two hand-written forgeries in `tests/forgeries/` prove `False`
through that hole. The provenance gate stops it producing a clean result, but
that is containment, not a fix, and it is why the third check corroborates the
term layer only.

**What to do.** Implement the **strict positivity check** first: of the three
unchecked properties (positivity, recursor shape, iota rules) it is the most
self-contained and the easiest to test adversarially. Then the recursor shape.

**The constraint that matters.** Adding this *widens* what the checker accepts,
which is the direction in which a mistake becomes unsoundness. So it must not
be written straight into the checker:

- implement it as a separate pass with its own tests;
- differentially test it against both Lean kernels over the whole Init and
  Mathlib declaration sets — every declaration both kernels accept must pass,
  every forgery must fail;
- keep `tests/forgeries/` as the regression floor, and add forgeries for each
  newly covered property.

**Done when:** both existing forgeries are rejected on their *specification*
rather than reported as introduced assumptions, and the differential test over
Mathlib's inductives is clean.

## 3. Fix the two recorded incompleteness findings, or document them as permanent

**Why.** TC-01 and TC-02 (`reference/third_check_adjudications.json`) are the
reason the third check cannot corroborate every declaration. They are safe —
they reject rather than accept — but each one is a hole in the corroboration.

- **TC-01**: iota reduction lacks to-constructor-when-structure. Affects three
  Lean core declarations; the fix is a known kernel rule, applicable only to
  single-constructor, index-free, non-`Prop` structures.
- **TC-02**: `level_leq` cannot decide a nested `imax` identity. The fix is to
  apply the `imax` case split recursively.

Both are in the widening direction, so item 2's differential-testing discipline
applies to them too.

**Done when:** either both are fixed with differential tests, or the
adjudication file states that they will not be fixed and why, so a reader is
not left expecting a fix that is not coming.

## 4. Independent review of the fidelity judgements

**Why.** All 13 claims are `reviewed_by` the same assistant that wrote the
harness: the party that built the checks also judged whether the statements
say what they claim, which is precisely the judgement a verification system
cannot make for itself.

**Status, 2026-10-13.** All 13 now also carry `confirmation.mode:
personally_reviewed` from the repository owner, who did not write the harness.
That reading changed the repository rather than ratifying it — five
corrections, listed in REVIEW-CHECKLIST.md — which is the evidence that it was
a reading and not a rubber stamp.

Two things in this section are therefore done and one is not:

- *done* — the misattribution (11 records had named the owner for work he had
  not done) and the delegated confirmations;
- *done* — a reviewer independent of the harness's author;
- **not done** — custody. The signature over all 13 records is a demonstration
  key generated in the build container and held by nobody, so cryptographically
  nothing is bound to anyone. The confirmations are recorded in the files and
  nowhere else.

That last gap cannot be closed from inside this repository's build: a key
generated here is a key the builder holds. `keygen --custody` and
`scripts/sign_attestations.sh` reduce the reviewer's part to generating a key
on their own machine and running one command with no Lean installed; CI
re-verifies the signatures afterwards.

**What to do.** Have someone who did not write the harness review the claims,
starting with the ones anyone relies on. The per-claim reasoning in
REVIEW-CHECKLIST.md exists so a reviewer can check the judgement rather than
redo it from nothing. Two specific things to look at first:

1. the definitions — `IsEven`, `PL.Derives`, `PL.DerivesPos`, `EL.Derives`,
   `EL.monoid`, and Mathlib's `Nat.Prime` — since fidelity lives there and not
   in the statement text;
2. the two **nontriviality guards** (PL-AXIOM-IND, FERMAT-F5), the one place
   where a guard's *relevance* is a reviewer's choice rather than a computed
   type.

Also still open: the third-check adjudications
(`reference/third_check_adjudications.json`) are
`PENDING_REVIEWER_CONFIRMATION`.

**Done when:** every claim carries `confirmation.mode: personally_reviewed`
from someone who did not author the harness — reached — **and** the signature
over those records is made with a key whose `custody` field names the person
who holds it — not reached.

## 5. Attack the statement-fidelity problem directly

**Why.** This is the largest remaining hole, and it is the one the external
validation pair demonstrated: `FermatWeaker` has no `sorry`, no extra axiom,
every line genuinely proved, and both kernels accept it — it just proves a
different statement. Freezing and signing make a human judgement auditable;
they do not make it correct, and a reviewer's attention is the scarcest
resource in the whole pipeline.

**Approaches worth trying, cheapest first:**

1. **Counterexample search against the frozen statement.** *Done,
   2026-10-13* — `harness/Counterexample.lean` and `harness/counterexample.py`.
   A statement can no longer be frozen without a search on record, the result
   is carried inside the signed attestation, and the search is bound to the
   statement hash so an edited statement cannot inherit a clean result.
   Fermat's claim is refuted at n = 5 as predicted. What it does not do is in
   ASSUMPTIONS A1b; the short version is that it is not evidence of truth, it
   says nothing about fidelity, and it contributes nothing to the four PL/EL
   claims, whose predicates are inductively defined and have no decision
   procedure.

   *Also done, 2026-10-13* — the **bounded derivation search** that closes
   the gap for those four: `harness/derivation_search.py`, with the kernel as
   the checker (`harness/CheckRefutation.lean`). PL-BOGUS, the one false-claim
   control the numeric search cannot touch, is now refuted by a derivation the
   kernel accepted with no axioms, verified to negate the frozen statement
   rather than an adjacent one; its waiver is gone. The other three come back
   NO_DERIVATION over a stated universe, which is a cross-check and not a
   proof — ASSUMPTIONS A1c says why. The equational search still cannot
   produce a witness (congruence closure here is not proof-producing), so a
   hit there would be a finding for a human rather than a refutation; that is
   the remaining piece of this item.
2. **Formalization triangulation.** *Tried, 2026-10-14, and it is much
   weaker than this item claimed.* Two renderings of one claim, proved
   equivalent in Lean — built, with three pairs on record and the equivalences
   machine-checked against the named statements
   (`harness/triangulate.py`, `reference/triangulation.json`).

   **The finding, which supersedes "the most promising idea here":**
   equivalence of propositions is vacuous between two TRUE statements. Any two
   theorems are equivalent, whatever they say, so an equivalence proof cannot
   distinguish a faithful rendering from a different true one.
   `Ampas.Triangulation.indistinguishable` proves it with "the sum of two
   evens is even" against "the product of two evens is even". Triangulation
   therefore detects only a rendering whose error makes it false — largely
   what item 1's counterexample search already does, more cheaply.

   What is left of the idea: each pair rules out a misreading of that claim
   that would have changed its truth value, and the obligation is
   kernel-checked rather than a reviewer's assurance. Worth having; not a
   fidelity check. ASSUMPTIONS A1d is the full statement.
3. **Back-translation with a stated protocol.** Render the Lean statement back
   into natural language and compare against the original, with the comparison
   done by someone who has not seen the Lean. Weak evidence, but it raises the
   cost of an unnoticed mismatch.
4. **A fidelity checklist with teeth.** The current six-item checklist is
   attested wholesale. Per-item evidence — "quantifier order checked" pointing
   at the specific binders — would make a careless attestation visible.

**Done when:** a statement cannot be frozen without a counterexample search
having run — reached — and the triangulation protocol has been tried on at
least one claim — not reached.

## 6. Scale the corpus, and stop writing it ourselves

**Why.** The corpus is adversarial but finite, and it was written by whoever
wrote the harness — the structural weakness the Fermat pair was added to
address. Thirteen attacks with recorded catching layers is evidence that those
thirteen are caught, and nothing more.

**What to do:**

- a standing invitation for third-party submissions, genuine and adversarial;
- AI-generated proofs at volume against the existing claims, since that is the
  actual intended workload — and the failure modes to expect are exactly the
  ones in the Fermat pair (`sorry`, an assumed axiom, a weakened statement);
- more claims drawn from mathematical history where the right answer is already
  known independently of this repository.

## 7. Mathlib coverage beyond one claim

Currently one claim over a 387-olean cone. Blockers: build time on small
machines, and the prebuilt cache being unusable with the pinned toolchain's
`leantar` (crates.io is unreachable in the recorded environment, so a newer
`leantar` could not be built). Fixing the cache path is the cheapest win; it
turns a 20-minute tier-3 build into a download.

## 8. Operational robustness

- **CI** over tiers 0–1 on every commit (`.github/workflows/verify.yml` does
  this); tier 2 nightly.
- **Resource limits.** `INCONCLUSIVE` now distinguishes a resource limit from a
  rejection, but the limits themselves are tuned for a two-core machine. They
  should scale with the host, and tier 3 should not need 20 minutes of a
  reviewer's patience.
- **Key custody.** The signing key is a demonstration key. Real deployment
  needs hardware-backed custody and a binding between the key and the
  reviewer's identity — the same problem as the identity track below.

## 9. The separate security track

The approval control plane (rounds 1–16: Safety Gate, claim state machine,
event log, authorization) is a **different** verification axis and is not in
this repository. Two items are open there:

- **R15-02** — event-log writer authentication/authorization: an unauthorized
  caller can still occupy a submission id.
- **R16-01** — the gate's administrative interface has no verified privilege
  isolation; if a deployment exposes the admin entry point, a caller can obtain
  the approval role.

An unfinished draft of that work exists outside this repository. It should stay
a separate track: mathematical correctness and system security fail in
different ways and should not be reported as one number.
