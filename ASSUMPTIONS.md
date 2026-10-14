# Assumptions and limits

Read this before trusting any result from this repository. Each entry says
what is assumed, why, and — where it exists — the evidence that the assumption
is load-bearing rather than theoretical.

The conclusion a clean run supports is narrower than "the mathematics is
correct". It is:

> This submission's proof type-checks in Lean's kernel under the axioms listed
> for the claim; its statement is structurally identical to the frozen
> reference statement; every definition the statement depends on is identical
> to the reference's, bodies included; and a named reviewer has attested that
> the reference statement renders the natural-language claim.

Everything below is what that sentence does *not* cover.

---

## A1. Formalization fidelity is a human judgement, not a machine result

**Assumed:** that the frozen Lean statement means what the natural-language
claim says.

Lean can decide whether a proof establishes a statement. Nothing can decide
whether the statement is the right one. What this repository does instead is
make that judgement *auditable*:

- the statement is frozen by the hash of its **elaborated** form, so
  reformatting and renaming binders do not change it but a change of meaning
  does;
- the whole dependency closure is frozen **including definition bodies**, so
  redefining `IsEven := True` while leaving the statement text byte-identical
  is detected and names the changed constant;
- guard theorems rule out two specific errors — a vacuously true statement, and
  a statement weakened by an unnecessary hypothesis — and the guards' *types*
  are computed by the auditor from the statement itself, so a guard cannot be a
  proof of something weaker;
- a **bounded counterexample search** runs against the frozen statement
  before it can be frozen at all, and its result is carried inside the signed
  record (see below);
- the record is signed (Ed25519) and re-derived on every verification run.

**What remains assumed:** guards exclude vacuity and over-strong hypotheses.
They do not exclude "this statement is about something else". That is the
boundary of Lean verification, not a gap in this implementation.

### A1b. What the counterexample search does and does not establish

`harness/counterexample.py` tries to falsify each frozen statement over a
committed box of small values before the statement can be frozen
(`reference/counterexample_bounds.json` holds the boxes, in the reference tree
rather than as a default in code, because the box is part of what a result
means). The outcome is cross-checked against the claim's own `control`
annotation, and both directions block a freeze: a statement that is refuted
but is not annotated as a false-claim control, and a statement annotated as
false that the search cannot refute without a stated reason why it cannot.

What it establishes: a statement that is **outright false** is caught cheaply,
before a reviewer's attention is spent on it. Fermat's claim dies at n = 5, in
milliseconds of evaluation — the record is
`reference/counterexample_search_fermat.json`, witness `[5]`.

What it does **not** establish, and these are the ways to misread it:

- **It is not evidence of truth.** "No counterexample" means no counterexample
  *in that box*. With the box set to n ≤ 4 — exactly the evidence Fermat
  himself had — the search reports nothing found, which is why the gate
  distrusts an unrefuted false-claim control.
- **It says nothing about fidelity.** A faithful formalization of a false
  claim and an unfaithful formalization of a true one are both refutable, and
  the search cannot tell them apart. A1 is unchanged by it.
- **It refuses to guess, and a refusal is a gap, not a pass.** Where a
  hypothesis or conclusion cannot be decided, the point is reported
  UNRESOLVED and the count is in the record; where the conclusion cannot be
  decided at all the claim comes back NOT_SEARCHABLE with the reason. Four of
  the ten core claims are in that position: `PL.Derives` and `EL.Derives` are
  inductively defined predicates with no decision procedure, so the search
  contributes **nothing** to the PL/EL claims, including to the falsity of the
  PL-BOGUS control. Refuting that one mechanically needs a bounded derivation
  search, which does not exist here (ROADMAP 5.1).
- **A one-sided test's `false` is not a `false`.** `IsEven n` is
  `∃ k, n = 2 * k`, which the search handles by hunting a witness up to a
  bound: finding one proves the hypothesis, failing to find one proves
  nothing. So EVEN's box of 625 points has 169 genuinely checked and 456
  unresolved, and the record says so rather than reporting a clean sweep.
- **A search killed by the clock has reached no verdict**, and is recorded
  INCONCLUSIVE, per A5.

**Evidence it matters:** the external validation pair. `FermatWeaker` contains
no `sorry`, no added axiom, every line genuinely proved, and both kernels
accept it — it proves the restricted statement `∀ n, n ≤ 3 → …` while filed
under the general claim. Only the statement comparator rejects it.

**Current status — read this before relying on any attestation.** All 13
fidelity judgements were *prepared* by the **same assistant that wrote the
harness** (`reviewed_by`), which is the structural weakness: the party that
built the checks also judged whether the statements say what they claim. All
13 have since been read and confirmed personally by the repository owner
(`confirmation.mode: personally_reviewed`), who did not write the harness.
That reading produced five corrections rather than a ratification — they are
listed in `REVIEW-CHECKLIST.md`, and the two false-claim controls were
restructured because of one of them.

As of 2026-10-13 all 13 are also signed by `kai-chang-2026-10`, a key
generated on the owner's own machine and never present in the container that
builds this repository, so the records are cryptographically bound to whoever
holds that key rather than to nobody. That was the largest remaining gap and
it is closed.

What is still missing, in order of how much it matters:

- **The reviewer did not re-run Lean.** He judged the definitions and
  statements as given. So the fidelity judgement and the kernel results come
  from different parties, which is the point — but it also means no single
  party has checked both.
- **The key's custody is asserted by its holder.** The public key record says
  who holds the private key; nothing outside this repository corroborates
  that. There is no certificate, no web of trust and no signed commit chain
  binding the key to a GitHub account, so a stranger cannot check the
  attribution without obtaining the fingerprint through another channel.
- **One reader is not open review.**

Until round 3 this was worse: a single `attested_by` field was filled with the
owner's name for 11 records the assistant had prepared, asserting he had
personally confirmed six checklist items per claim. He had not. The three
roles are now separate fields, `verify` checks them separately, and the
signing key was re-issued because its old id implied the owner's custody.

The third-check adjudications (`reference/third_check_adjudications.json`)
remain `PENDING_REVIEWER_CONFIRMATION`: the gate acts on the
machine-reproducible half of each finding (library code, both kernels accept,
reproduces with no submission involved), and the judgement that this is
incompleteness rather than a missed soundness problem is still outstanding.

### A1c. The bounded derivation search, and what a negative result is worth

Four claims state that certain DERIVATIONS do not exist: PL-IND, EL-IND,
PL-AXIOM-IND and PL-BOGUS. `PL.Derives`, `PL.DerivesPos` and `EL.Derives` are
inductively defined predicates with no decision procedure, so the numeric
search of A1b reports them NOT_SEARCHABLE and contributes nothing. A
counterexample to such a claim is a derivation, so
`harness/derivation_search.py` enumerates derivations instead of values:
forward chaining over modus ponens for the propositional claims, congruence
closure for the equational one.

**The searcher is not trusted.** It finds candidates. Each one is emitted as a
Lean term proving the negation of the frozen statement, compiled, replayed
through the kernel in both modes, and checked by
`harness/CheckRefutation.lean` — which verifies that the refutation's type is
`Not` applied to *the frozen statement*, that it is a theorem, that it rests
on no `sorryAx`, and that its statement mentions no constant the trusted
reference does not define. That last check matters for the same reason the
statement comparator matters: a refutation of an adjacent statement is exactly
the `FermatWeaker` failure mode pointed the other way. A bug in the searcher
can therefore lose a refutation; it cannot manufacture one.

**What it established.** PL-BOGUS is a declared-false control, and until now
nothing in this repository proved it false — only that no submission could
prove it true, which is a different and much weaker thing. The search finds
the Łukasiewicz derivation of `p1 → p1` in five steps; the kernel accepts the
refutation **with no axioms at all**, and the statement check confirms it
negates the frozen statement structurally and up to definitional equality. The
waiver that used to stand in for this is gone.

**What a NO_DERIVATION result is worth: much less.** For PL-IND,
PL-AXIOM-IND and EL-IND it means no derivation was found within a stated
universe — for the propositional ones, instantiating the axiom schemas over a
48-formula universe for three rounds, around 200,000 formulas derived; for the
equational one, congruence closure over a 238,148-term universe. The schemas
range over infinitely many formulas, so this is not a proof of independence
and must not be read as one. **Those three claims are already proved** by
kernel-checked submissions in the corpus, which is where their truth comes
from. The search's value for them is as a cross-check in the other direction:
if it ever found a derivation, either the search or a certified independence
proof would be wrong, and the kernel-checked witness would say which.

**The equational search cannot produce a witness.** Congruence closure here
does not produce a proof tree, so a derivation it found could not be handed to
the kernel. That outcome is recorded `DERIVATION_FOUND_BUT_UNVERIFIED` and is
a finding for a human, never a refutation. It has not occurred.

### A1d. Formalization triangulation, and why it is weaker than it sounds

ROADMAP 5.2 proposed rendering the same natural-language claim twice and
proving the two renderings equivalent in Lean, so that a divergence localises
a fidelity problem without anyone reading both. It called this "the most
promising idea here". **That assessment was wrong, and the reason is a
one-line theorem.**

**Equivalence of propositions is vacuous between two true statements.** Any
two theorems are equivalent, whatever they say. So an equivalence proof
cannot distinguish a faithful rendering of a claim from a *different true*
one. `Ampas.Triangulation.indistinguishable` proves this inside the
repository rather than asserting it: "the sum of two even naturals is even"
and "the **product** of two even naturals is even" are plainly different
claims, both true, and the equivalence between them is two applications.

What triangulation therefore detects: a second rendering whose error makes it
**false**. `FermatWeaker`'s restriction to `n ≤ 3` is caught precisely
because the general claim is false and the restriction is true. That overlaps
heavily with what the counterexample search (A1b) already does, from a more
expensive direction.

What it does **not** detect, and this is the part that matters: a rendering
that is weaker, or about something else, and still true. Those are exactly
the fidelity errors a reviewer is there to catch, and no amount of
machine-checked equivalence reaches them.

**What the pairs on record are still worth.** Three are checked
(`reference/triangulation.json`, results in
`reference/triangulation_results.json`):

- EVEN is informative. `IsEven n := ∃ k, n = 2 * k` against `n % 2 = 0` are
  different predicates built from different operations; their agreement is a
  theorem, and it rules out a misreading of "even" that would have changed
  the claim's truth value — a definition excluding 0, say.
- DVD is informative for the same reason: the `Dvd` class against explicit
  existentials makes "divides" a proof obligation rather than something a
  reviewer takes on trust.
- SUB is **weak and labelled weak**: the same equality with the sides
  swapped, equivalence by `Eq.symm` twice. It is kept because a suite
  containing only pairs like it would have the same shape as a suite of
  informative ones and would be evidence of nothing.

**The equivalences are checked, not assumed.**
`harness/CheckTriangulation.lean` resolves both sides from the environment by
name and verifies the theorem's type is `Iff` applied to exactly those two
statements, structurally and up to definitional equality, with no `sorryAx`
beneath it. An `Iff` between two other propositions compiles perfectly well,
which is the `FermatWeaker` failure mode pointed at equivalences.

**Provenance: both renderings in every pair were written by the same author**
— the assistant that wrote the harness — each from the claim's text. That is
not independent formalization: two renderings by one author can share a
misreading, and the equivalence proof then confirms only that they share it.
A genuinely independent second author remains open, and because of the
finding above it would buy less than ROADMAP 5.2 expected.

## A2. Kernel soundness — and cross-checking is weaker evidence than it looks

**Assumed:** that Lean's kernel is sound, or that two independent kernels do
not share a soundness failure.

Certification requires both `leanchecker` (Lean's own kernel) and
[lean4lean](https://github.com/digama0/lean4lean) (an independently written
kernel that also checks inductives) to accept the submission.

**What remains assumed, with evidence against the strong reading:** in 2026
several Lean kernel soundness bugs surfaced. One produced an illicit disproof
of the Collatz conjecture; a related one produced a short illicit proof of the
Kepler conjecture. Critically, cross-checking one of these with an independent
kernel (an outdated Nanoda) **also accepted** the illicit proof, because of
that kernel's own unrelated bug
([Tao, 2026-10-09](https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/)).

So: *independence of implementations is not independence of failure.* Two
kernels agreeing is better than one, and it is not conclusive. This repository
previously described its trusted base as "smaller but not gone"; that external
case shows the independence property itself can fail, which is a stronger
caveat than the one originally written.

### A2b. Kernel provenance, and what a clean advisory result is worth

Since 2026-10-14 every verdict record names the kernels that issued it: the
Lean version and binary hash, the primary kernel's hash, the lean4lean pin,
the Mathlib pin, the toolchain pin, and whether the auditor was compiled or
interpreted (`harness/provenance.py`). `harness/reverify.py` compares a
stored record against the live toolchain and the current advisory list.

**What this buys.** After a soundness disclosure, a certificate can be matched
back to the binaries that issued it. That is the only thing that makes the
question "which of our certificates does this affect?" answerable at all, and
A2's whole point is that the question will be asked again.

**What a clean advisory result does NOT mean.** `reference/kernel_advisories.json`
is maintained by hand, by one party, with no notification channel. A record
citing it says "no advisory in this list, as of `last_reviewed`, names this
kernel". It does not say the kernel is sound, and the wording in the record is
deliberately that shape -- a mechanism that produced "no known bugs" from a
list nobody updated would be worse than having no list. The list's hash
travels with each record, so a later edit cannot silently change what an old
record claimed.

The list's single entry is the Tao report, and its `affected` range is
**empty**: this repository has not established which revisions the reported
bugs touch, so the advisory matches no kernel and says why. A plausible
version range would have made the matcher produce confident verdicts from a
guess.

**The gap this cannot close.** Every record issued before 2026-10-14 is
reported NO_PROVENANCE -- thirty certified claims across seven records whose
kernel cannot be identified from the record. Provenance works forwards only,
and the records that would most need re-checking after a disclosure are
exactly the ones that predate it.

**A metadata match is not a reproduction.** `reverify.py` compares recorded
provenance against the live toolchain; it re-executes nothing unless `--rerun`
is passed. A SAME_KERNEL row means a record would be *expected* to reproduce.
Reporting that as having reproduced would be a claim about an execution that
never happened.

## A3. The third check corroborates the term layer only

`harness/kernel3` is a from-scratch type checker in Python that shares no code
with Lean and does not use Lean's elaborator. A clean result from it means
exactly:

> every declaration's type was re-derived independently, and every inductive
> specification it relied on matched the trusted baseline fingerprint-for-
> fingerprint.

**Assumed and NOT checked:** that an inductive declaration is a legitimate
specification. Three properties make it one — strict positivity, the shape of
the generated recursor, and its iota rules — and **one of the three is now
checked**, by a separate pass:

> `harness/kernel3/positivity.py` decides strict positivity, and classifies
> rather than judges: a shape it cannot decide comes back `UNCLASSIFIED`, not
> `OK`. Differentially tested over 3285 inductives from the trusted reference
> set and the Mathlib set — 0 violations, 45 unclassified, all 45 the nested
> shape (a recursive occurrence under another inductive's parameter)
> — in `evidence/positivity_differential.json`.
>
> It changes nothing about a verdict. The provenance gate below is unchanged,
> and an `OK` from this pass is **not** a checked specification: the recursor's
> shape and the iota rules remain assumed, so a specification that passes
> positivity can still be a forgery. `forge_large_elim` is exactly that — a
> forged *recursor*, which positivity cannot see and which only provenance
> catches.

This is the classic source of unsoundness, and it is exploitable:

| Forgery (`tests/forgeries/`) | Original behaviour |
| --- | --- |
| `Prop` large elimination: a `Prop` with two constructors plus a hand-written recursor eliminating into `Sort u`. Proof irrelevance then makes two types interchangeable | `9/9 checked, 0 errors`, **`False` proved** |
| Non-positive inductive: `Bad.mk : (Bad → MyFalse) → Bad` plus the diagonal argument | `7/7 checked, 0 errors`, **`False` proved** — now rejected on its specification by the positivity pass |
| Control: the same recursor restricted to `Prop` (legitimate small elimination) | **correctly rejected** |

The control matters: it shows the hole is in the *assumed specification layer*,
not a general collapse.

**Mitigation, not a fix.** The gate was not closed by adding reduction rules —
widening what a checker under review accepts is the direction in which a
mistake becomes unsoundness. Instead a provenance gate reports any assumed
declaration whose fingerprint is not in the trusted baseline as an
`introduced_assumption`, so neither forgery yields a clean result.

**In this pipeline the hole is unreachable**, because the export comes from an
olean the submitter compiled with Lean, and a forged inductive does not survive
Lean's own elaborator and kernel. That is to say: the assumption is discharged
by the *primary kernel*, not by nobody. Point this checker at an olean of
unknown provenance — the case where an independent checker is most valuable —
and the hole is live.

**It is also incomplete**, in the rejecting (safe) direction, on library-scale
code. Two mechanisms are recorded in
`reference/third_check_adjudications.json`:

- **TC-01** — iota reduction lacks to-constructor-when-structure, so a
  recursor applied to a neutral of structure type stays stuck. Three Lean core
  declarations are affected.
- **TC-02** — `level_leq` cannot decide a nested `imax` identity that is true
  for every universe, so `Nat.decidableBallLT.match_5` is rejected.

Both reproduce from library code with no submission involved, and both Lean
kernels accept all four declarations.

**Consequence for the gate:** the third check is corroboration, never a veto.
An *unadjudicated* disagreement blocks certification; an adjudicated one is
recorded and does not. Letting the least complete of three implementations
overrule the other two was a real defect in an earlier version of this
harness — it rejected a correct, twice-kernel-verified Mathlib proof.

## A4. The trusted computing base that remains

Still trusted, with nothing in this repository checking it:

- **Lean's elaborator.** Every tier starts from an olean that Lean produced.
  Only the kernels' re-checking of it is independent.
- **The sandbox.** An unprivileged user, read-only trusted oleans and resource
  limits — not a VM, not a container.
- **The OS, the hardware, the Python interpreter, the C toolchain.**
- **The signing key's identity.** Custody is not derivable from key material,
  so `keygen --custody` records it in the public key file at the moment the key
  is made, and defaults to a stated `UNDECLARED` rather than to silence.
  `reference/reviewer_key.json` now names the repository owner, and the key was
  generated on his machine — but that line is an assertion by the party it
  describes. Binding a key to an identity is outside what this repository can
  do for itself.

## A5. Resource limits can make a run inconclusive, and that is not a rejection

A checker killed by the CPU, wall-clock or memory limit has reached no verdict.
The driver classifies exit 124 / −24 / −9 / 137 / `TIMEOUT` as resource
exhaustion and reports the claim `INCONCLUSIVE` — never certified, but not
rejected either.

**Evidence this matters, and the residual gap.** Three such signatures were
found one at a time, each having first been misreported as a kernel rejection
on the same (largest) submission:

| Signature | How it appeared |
| --- | --- |
| `SIGXCPU` (−24) | two concurrent test sessions on two cores exceeded the CPU limit |
| `std::bad_alloc` | Lean's C++ kernel runs out of memory by throwing, exiting non-zero |
| `failed to create thread` | thread creation failed under load; `RLIMIT_NPROC` was raised from 512 to 2048 |

**The list is known incomplete.** Lean signals resource failures as thrown
exceptions with particular messages, so they have to be recognized by
signature, and the inverse rule — "treat any unrecognized crash as
inconclusive" — is not available either: lean4lean's genuine rejection of the
kernel-bypass attack is a bare stack trace with no verdict marker in it, so
that rule would misclassify a real rejection.

What actually protects a run is not the classifier: **every submission carries
a predicted verdict in the manifest**, so a resource failure on a submission
expected to certify fails the run loudly rather than passing as a rejection.
That is how the third signature was caught (`scripts/check_expectations.py`:
"ELSol: expected certified_all, got rejected"). A reviewer running a corpus
without predicted verdicts does not have that protection.

## A6. Scope of the mathematics covered

- **Mathlib: one claim**, over a 387-olean dependency cone at a pinned revision,
  built from source. Not the whole library, and nothing of the scale of real
  independence results.
- **Independence proofs** are over proof calculi deeply embedded in this
  repository (`Ampas.PL`, `Ampas.EL`), proved sound by hand. They are not
  statements about ZFC.
- **The corpus is adversarial but finite.** Thirteen attacks, each with a
  recorded layer that catches it. Absence of an attack in the corpus is not
  evidence the pipeline resists it.
- **The corpus was written by the same hands as the harness**, which is why the
  external validation pair exists — and why a reviewer's own submissions are
  more informative than any of this.

## A7. Reproducibility

- The toolchain is pinned (`lean-toolchain`, Lean 4.33.0); Mathlib and
  lean4lean are pinned by revision and checked against the pins at build time.
- The provenance baseline is **regenerated locally** by `bootstrap.sh` and
  compared against the committed one; a difference means your toolchain built
  different oleans, which you want to know before reading a verdict.
- The recorded run reproduces the committed baseline byte-for-byte on the
  pinned toolchain.
- `SHA256SUMS` covers the sources and the recorded evidence. The compiled
  auditor binary is deliberately **not** committed: it is platform-specific and
  the driver can interpret `harness/Audit.lean` instead.
