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
- the record is signed (Ed25519) and re-derived on every verification run.

**What remains assumed:** guards exclude vacuity and over-strong hypotheses.
They do not exclude "this statement is about something else". That is the
boundary of Lean verification, not a gap in this implementation.

**Evidence it matters:** the external validation pair. `FermatWeaker` contains
no `sorry`, no added axiom, every line genuinely proved, and both kernels
accept it — it proves the restricted statement `∀ n, n ≤ 3 → …` while filed
under the general claim. Only the statement comparator rejects it.

**Current status:** the sign-offs for the two Fermat statements are
`PENDING` (`reference/claims_fermat.json`), and the third-check adjudications
are `PENDING_REVIEWER_CONFIRMATION`
(`reference/third_check_adjudications.json`). Those files state this; they do
not imply a sign-off that was never given.

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

## A3. The third check corroborates the term layer only

`harness/kernel3` is a from-scratch type checker in Python that shares no code
with Lean and does not use Lean's elaborator. A clean result from it means
exactly:

> every declaration's type was re-derived independently, and every inductive
> specification it relied on matched the trusted baseline fingerprint-for-
> fingerprint.

**Assumed and NOT checked:** that an inductive declaration is a legitimate
specification — strict positivity, the shape of the generated recursor, and its
iota rules. This is the classic source of unsoundness, and it is exploitable:

| Forgery (`tests/forgeries/`) | Original behaviour |
| --- | --- |
| `Prop` large elimination: a `Prop` with two constructors plus a hand-written recursor eliminating into `Sort u`. Proof irrelevance then makes two types interchangeable | `9/9 checked, 0 errors`, **`False` proved** |
| Non-positive inductive: `Bad.mk : (Bad → MyFalse) → Bad` plus the diagonal argument | `7/7 checked, 0 errors`, **`False` proved** |
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
- **The signing key.** A demonstration key; real deployment needs custody and a
  binding to the reviewer's identity.

## A5. Resource limits can make a run inconclusive, and that is not a rejection

A checker killed by the CPU, wall-clock or memory limit has reached no verdict.
The driver classifies exit 124 / −24 / −9 / 137 / `TIMEOUT` as resource
exhaustion and reports the claim `INCONCLUSIVE` — never certified, but not
rejected either.

**Evidence this matters:** it was found while packaging. Two concurrent test
sessions on a two-core machine were enough to make lean4lean hit the CPU limit
on the largest submission, and the earlier code read that non-zero exit as a
kernel rejection — a verdict that depended on how busy the machine was, with an
error message that misdescribed the cause.

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
