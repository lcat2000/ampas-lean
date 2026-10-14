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

1. **Record kernel provenance per verdict.** *Done, 2026-10-14* --
   `harness/provenance.py`, attached to every verdict record the driver
   emits. It names the Lean version and binary hash, the primary kernel's
   hash, the lean4lean pin and its toolchain discrepancy, the Mathlib pin, the
   toolchain pin, whether the auditor was compiled or interpreted, and the
   advisory status. It goes in the VERDICT record rather than the signed
   formalization attestation, so it needs no re-signing: the attestation is
   about whether a statement says what a claim says, which no kernel version
   affects.

   `reference/kernel_advisories.json` is the advisory list. The failure mode
   it is built against is the opposite of the usual one: an empty or stale
   list would make every certificate say "no known bugs". So a record says
   "no advisory in THIS list, as of `last_reviewed`, names this kernel", the
   list's own caveats are in the file, the consulted list's hash travels with
   each record, and an entry whose affected range this repository has not
   established leaves it EMPTY and says why -- inventing a version range
   would turn a guess into a confident machine verdict. The one entry is the
   Tao report, with `affected: {}` for exactly that reason.
2. **Re-verification on disclosure.** *Done, 2026-10-14* --
   `harness/reverify.py`, run at tier 1. It classifies each stored record
   AFFECTED / KERNEL_CHANGED / NO_PROVENANCE / SAME_KERNEL, and it separates
   a metadata comparison from an execution: a SAME_KERNEL record is one that
   would be EXPECTED to reproduce, and `--rerun` is what establishes that it
   does. Both branches were made to fire before being believed -- injecting
   an advisory naming Lean 4.33.0 flipped an already-issued certificate to
   AFFECTED.

   **What it reports today, and this is the finding:** every stored record is
   NO_PROVENANCE. Thirty certified claims across seven records, whose kernel
   cannot be identified from the record, because they were all issued before
   provenance was recorded. That gap closes going forward and cannot close
   backwards -- the records that would need re-checking after a disclosure
   are precisely the ones that cannot be matched to a kernel.
3. **Add a checker that is different in kind, not just in authorship.** Both
   current kernels implement the same algorithm from the same specification. A
   *verified* kernel — one whose soundness is itself proved relative to a set
   theory — fails differently. Con-Leche and the verified fragment of lean4lean
   are the candidates to evaluate.

   ### 1.3a. The second kernel was never independent — correction, 2026-10-14

   Evaluating the candidates turned up something about the kernels this
   repository already runs. Until this date the README, ASSUMPTIONS A2 and
   several scripts called lean4lean **"an independently written kernel"**.
   Upstream says the opposite, in its own README:

   > It is derived directly from the C++ kernel implementation, and as such
   > likely shares some implementation bugs with it (it's not really an
   > independent implementation), although it also benefits from the same
   > algorithmic performance improvements existing in the C++ Lean kernel.
   >
   > — [digama0/lean4lean](https://github.com/digama0/lean4lean)

   The [Lean Kernel Arena](https://arena.lean-lang.org/checker/lean4lean/)
   repeats the characterisation. So **the premise of this repository's
   cross-check never held**: tier 2 is two implementations of one algorithm
   agreeing, one derived from the other's C++ original. A2 already said that
   independence of implementations is not independence of failure, citing the
   Tao report; the sharper point is that this pair had no independence to lose.

   It is still worth running — lean4lean has found real kernel bugs, and the
   arena records it rejecting all 19 of its bug-regression tests with the
   expected errors — but what the records show is **agreement between
   relatives**.

   Corrected in ASSUMPTIONS A2 (where the claim was made), both READMEs,
   `INSTALL.md`, `scripts/verify.sh`, `scripts/bootstrap.sh` and the CI job
   name. The record field names (`kernel_replay_independent`,
   `provenance.independent_kernel`) are **kept**, so that verdicts issued
   before today stay readable, with the correction carried inside the
   provenance block itself as `is_an_independent_implementation: false` plus
   `independence_correction` — a reader of a stored verdict may never open
   ASSUMPTIONS. `evidence/environment.json` said "Independently written kernel"
   and is annotated in `record_corrections` rather than rewritten.
   `tests/test_provenance.py` forbids the phrases, and found three more
   occurrences than this correction started with.
   ### 1.3b. con-leche evaluated — done, 2026-10-14

   [con-leche](https://github.com/leanprover/con-leche) is the candidate that
   is different in kind: an external checker written in Lean, with its own term
   representation, carrying a theorem proved in Lean that **if it accepts a
   declaration set, that set has a model in set theory** — so no accepted
   theorem's statement is false in the model, and a file declaring
   `theorem … : False` is never accepted.

   Full account, with every number:
   [`docs/CONLECHE-EVALUATION.md`](docs/CONLECHE-EVALUATION.md) and
   `reference/conleche_evaluation.json`. Reproduce with
   `scripts/check-with-conleche.sh`.

   **Built in full** — 660 Lake jobs including the proof lane, because a
   verified kernel whose verification one has not built is not evidence of
   anything — and both theorems checked against that build:
   `no_False_declaration` and `model_exists` depend on
   `propext, Classical.choice, Quot.sound` and nothing else. No `sorryAx`.
   They are, however, **conditional** on `[SetTheory V]`; the upstream bridge
   that discharges that from Mathlib's `ZFSet` under Carneiro's
   ω-many-inaccessibles hypothesis is a separate package that was **not** built
   here.

   | input | outcome | time | peak RSS |
   | --- | --- | --- | --- |
   | `AmpasRef.Guards` (the reference environment) | **declined** — `sorryAx` in a value | 33 s | 0.43 GiB |
   | `corpus/Genuine.lean` (a certified submission) | **accepted**, 58107 declarations | 43 s | 0.39 GiB |
   | `A04_native_lie` — **both Lean kernels accept it** | **declined** — non-standard axiom | 3 s | 0.42 GiB |
   | `A06_wrong_statement` | **accepted**, 58102 declarations | 40 s | 0.42 GiB |

   - A genuine submission's whole closure is accepted, in 43 seconds — the
     result this item asked for, and cheaper than tier 1.
   - The reference environment cannot be checked at all, because this suite
     states frozen claims as `theorem … := sorry`. That is about AMPAS's
     design; the thing to check is a submission.
   - **A04 must not be miscredited.** con-leche refuses it for its *axiom
     restriction*, the layer AMPAS's own axiom policy already occupies and
     which already flags it `NATIVE_EVALUATION`. The model proof did no work
     there, and "not implemented yet" is a decline rather than a rejection on
     the merits. Calling it "the verified kernel caught what the Lean kernels
     accepted" would be the same overclaim 1.3a corrects.
   - **A06 is accepted, and that is the finding that matters.** A genuine proof
     of `∀ a, a + a = a + a` filed as `add_comm_nat` is a theorem, and a
     checker whose acceptance implies a set-theoretic model accepts it. So the
     fidelity gap is **not** a weakness of unverified kernels that a verified
     one closes — it is outside what any kernel decides. Only the statement
     comparator and a human reading stand between A06 and a certificate, and
     con-leche changes that by nothing.

   **Integrated as an optional script, not a tier of `verify.sh`.** Cost, not
   doubt: a second 3 GB toolchain, a 660-job build, lean4export at this suite's
   own 4.33.0, and a ~333 MB export per submission. A default that heavy would
   make a clean checkout unverifiable on an ordinary machine. Nothing is
   claimed silently — a certificate mentions a con-leche acceptance only if one
   was run and recorded.

   **Also found while evaluating:** the
   [Lean Kernel Arena](https://arena.lean-lang.org/), a third-party adversarial
   benchmark of ~28 Lean checkers (proofs that must be rejected, proofs that
   must be accepted, 19 bug-regression tests). That is the kind of external
   corpus item 6 asks for, for the layer `harness/kernel3` occupies, and
   nothing in this repository can supply it about itself. Running `kernel3`
   against the arena suite is the obvious next item and is **not** done.

4. **Statement-level redundancy.** For a claim that matters, require two proofs
   by routes that share as little of the library as possible, and compare their
   axiom closures. This catches a library-level problem that any number of
   kernels would miss.

**Done when:** a certificate names its kernels and their bug status --
reached for records issued from 2026-10-14 -- and `verify.sh` can answer
"which stored certificates would not reproduce today" -- reached, and its
answer for every pre-existing record is "its kernel cannot be identified".
Items 3 and 4 remain.

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

### 2a. Strict positivity — done, 2026-10-14

`harness/kernel3/positivity.py`, a separate pass that classifies rather than
judges: `OK`, `VIOLATION`, or `UNCLASSIFIED` for a shape it cannot decide.
`forge_positivity.export` is now rejected on its specification —
`Bad.mk : (Bad → MyFalse) → Bad` puts the recursive occurrence left of an
arrow — and `MyFalse`, in the same export, still passes, so the pass is not
simply rejecting arrows.

Differentially tested (`harness/spec_diff.py --pass positivity`,
`evidence/positivity_differential.json`): **3285 inductives** across the
trusted reference set and the Mathlib set, **0 violations**, **45
unclassified**, all 45 of one cause — a recursive occurrence under another
inductive's parameter (`Array`, mostly), which needs that inductive's own
positivity and which this pass declines rather than approves. A violation
there would be a bug in the pass, since Lean's own kernel accepted the
declaration, so the script exits non-zero on one.

**What it does not close.** Two things, and the first corrects the "done when"
originally written here:

- **`forge_large_elim.export` is not a positivity forgery.** It forges a
  *recursor*. Positivity has nothing to say about it, it comes back clean from
  this pass, and it must still be caught by the provenance gate. The original
  wording — "both existing forgeries are rejected on their specification" —
  asked positivity to do something it cannot; only one of the two forgeries is
  in its scope.
- **Passing is still not a checked specification.** Positivity is one of three
  assumed properties. `kernel3`'s provenance gate is unchanged and
  `tests/test_positivity.py::test_positivity_does_not_relax_the_provenance_gate`
  fails if a positivity `OK` is ever wired into it.

### 2b. Recursor shape — done, 2026-10-14

`harness/kernel3/recursor.py`, same discipline: its own pass, its own tests,
`UNCLASSIFIED` rather than a guess. `forge_large_elim.export` is now rejected
on its recursor — a `Prop` with two constructors cannot be eliminated into a
large `Sort`, because the recursor would read which constructor was used and
proof irrelevance makes the two indistinguishable — while its control, the
same recursor restricted to `Prop`, passes.

What the pass checks: one motive per family member and one minor premise per
constructor; exactly one iota rule per constructor of the member being
eliminated, each with that constructor's own field count; parameter and index
counts against that member; `k` only for a single-constructor, field-free
`Prop`; and the elimination universe, where large elimination of a `Prop` is
allowed only for a subsingleton — at most one constructor, every field either
a proof or an argument the conclusion's indices already pin down. `Eq.refl`'s
`a` is the second case, `And.intro`'s fields the first.

Differentially tested (`harness/spec_diff.py --pass recursor`,
`evidence/recursor_differential.json`): **3410 recursors**, **0 violations**,
263 unclassified under two named causes — a field type needing a definition
the `--specs` export does not carry (80), and the auxiliary recursors a nested
inductive generates over the nesting type (183).

**The differential test earned its place here.** The first version of the
rules check assumed a mutual family's recursor carries iota rules for every
constructor in the family. Nineteen Mathlib recursors came back VIOLATION, all
of them legitimate: a mutual recursor carries rules for the member it
eliminates, which the pass now reads off the conclusion rather than off the
declaration's name. Without the differential test that rule would have shipped
rejecting valid code — and a rule wrong in one direction can be wrong in the
other.

### 2c. The iota rules — done, 2026-10-14

`harness/kernel3/iota.py`. The recursor pass counts the rules and checks which
constructor each belongs to; this one **re-derives each rule's right-hand side**
from the constructor and the recursor and compares it, so an `OK` means the
stored rule *is* the derived one rather than that it looks plausible:

    λ p… m… n… f…, nᶜ f₀ … f_{k-1} rec₀ … rec_{j-1}

with one recursive call per recursive field, each `λ b…, Iₖ.rec levels p… m…
n… (that field's indices) (fᵢ b…)` — the callee being the recursor of the
member the *field* is of, which is a sibling's in a mutual family.

Differentially tested (`harness/spec_diff.py --pass iota`,
`evidence/iota_differential.json`): **3410 recursors, 0 violations, 183
unclassified** — every one of the 183 the auxiliary recursors of a nested
inductive. So **3227 recursors' rules are exactly re-derivable**.

**New vectors, and they had to be Lean-generated** — unlike the other three,
which are hand-written. What needed demonstrating is that a tampered rule is
invisible in an *otherwise clean* export, so the base had to be clean;
`control_small_elim` is the vector that is supposed to be rejected, so nothing
derived from it could show this. Two pairs, each differing from its control in
one line of one `#REC`:

| pair | third check | iota pass |
| --- | --- | --- |
| `control_iota` / `forge_iota` — `Two.rec`'s two rules swapped, nothing exercising them | `8/8 checked, 0 errors` **for both** | clean / **VIOLATION** |
| `control_iota_exercised` / `forge_iota_exercised` — the same swap plus `pick_fst : pick a b Two.fst = a := rfl` | clean / **rejects `pick_fst`** | clean / **VIOLATION** |

The first pair is the hole: a swapped rule costs nothing to a checker that
does not read the rules. The second is the consequence: once a term depends on
the rule, what the kernel proves changes — `pick a b Two.fst = a` is true of
`pick` as declared and becomes unprovable, and by the swap's symmetry `rfl`
instead proves `pick a b Two.fst = b`, which is false of it.

**Neither forgery proves `False`, and neither can.** A minor premise's required
type comes from the recursor's *type*, and the forged reduction only changes
the result side, so the hard minor still blocks any `False` construction. A
wrong iota rule gives a *consistent* system that computes something other than
the declaration says — the ASSUMPTIONS A1 failure mode, where a proof passes
under the definitions actually used, not an inconsistency. That is a weaker
exploit than the other two forgeries and is recorded as such.

**Three bugs in this pass, each found only by the differential test**, which
is the whole argument for requiring it: the rule body's binder depth was used
for a field's own binder type (491 of 627 core recursors read as forged);
`let` was not descended into (6 more); and the recursive call's callee was
hardcoded to this recursor, which is right for every one of the 137 recursive
calls in Lean's own Init — it has no mutual inductive in that set — and wrong
for 25 in Mathlib. A core-only differential run would have shipped the last
one.

### What is still assumed with all three passes clean

**That the declaration set came from Lean.** The three passes check a
declaration against the rules Lean would have followed; none of them shows
that Lean produced it. A specification can satisfy all three and still be
nothing Lean would emit. That is what the provenance gate is for, and
ASSUMPTIONS A3 is written against that boundary.

So the third check still corroborates the term layer only, and the honest
summary of items 2a–2c is narrower than "the gap is closed": the three
properties `kernel3` *assumed* are now checked, and the assumption that
remains is about the export's origin rather than its shape.

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

### 6a. Historical claims — done, 2026-10-14

The third bullet. Three more episodes, each contributing the historically
FALSE claim and the TRUE refutation that settled it, in
`AmpasRef.ChallengeHistory` / `reference/claims_history.json` with eleven
submissions in `corpus/manifest_history.json`:

| episode | false claim | refuted by |
| --- | --- | --- |
| Mersenne, *Cogitata Physico-Mathematica*, 1644 | `2^67 - 1` is prime (the p = 67 entry of his list) | F. N. Cole, 1903: `2^67 - 1 = 193707721 * 761838257287` |
| Euler, 1769, sum-of-powers conjecture at n = 5 | no fifth power is the sum of four positive fifth powers | Lander and Parkin, 1966: `27^5 + 84^5 + 110^5 + 133^5 = 144^5` |
| after Euler, 1772 | `n^2 + n + 41` is prime for every n | `40^2 + 40 + 41 = 1681 = 41 * 41` |

All 11 submissions land where the manifest says (3 certified, 8 rejected), and
every one of the 8 attacks compiles and is rejected by a named layer rather
than by failing to build.

**Chosen to stress different layers, not for variety.** This is what the three
episodes actually showed:

- **EULER-POLY** is refuted by the bounded numeric search on its own, at
  n = 40, inside a box of 64 — the same shape as Fermat's claim dying at n = 5.
- **MERSENNE-67** is refuted by the search too, which was a surprise: the box
  is a single point, and `Nat.Prime`'s decision procedure finds the factor
  193707721 by trial division in a few minutes. So the search independently
  reproduces Cole's 1903 result. The bounds file had said it could not;
  that sentence is corrected in place, with a note that the run contradicted it.
- **EULER-SUM-5** is false and the search **cannot** reach it: Lander and
  Parkin's witness needs 144 in five variables, about 6.2e10 points. It comes
  back NO_COUNTEREXAMPLE on a false claim — a recorded limit of the search
  layer, demonstrated on a claim this repository did not choose.

**Four defects this corpus found in the harness**, all of the same kind — a
derived label computed from, or asserted without, the data beside it:

- `harness/ablation.py` identified attacks by an `A` naming prefix, which is
  how the core corpus happens to name them. The history submissions are named
  after mathematicians, so all eight of its attacks fell out of the
  layer-attribution table and the table reported "0 attacks, all rejected:
  True". **The four Fermat attacks had been missing the same way since the
  Fermat pair was added** — the corpus added precisely to answer "the corpus
  was written by whoever wrote the harness" had no layer attribution anywhere.
  Attacks are now read from each record's own `expected` field, and
  `build/ablation_external.json` covers both external corpora.
- the first draft of this catalogue wrote the control field as
  `target_claim_is: "false"` instead of `target_claim_is_true: false`. It reads
  correctly to a human and is invisible to the code; the search reported
  `REFUTED_BUT_NOT_DECLARED_FALSE` against MERSENNE-67 and that is how it was
  found. A test now pins the field the harness actually reads.
- the third check's status read `DISAGREEMENT (adjudicated: checker
  incompleteness)` beside an `adjudication` field of `null`. Four history
  attacks carry it, all for `Nat.decidableBallLT.match_5` — TC-02, which
  `decide` over a bounded quantifier pulls in. The record now names the
  declaration and the finding, and carries the adjudications file's sign-off
  state, because that file is `PENDING_REVIEWER_CONFIRMATION` with
  `confirmed_by: null`: **"adjudicated" means an unconfirmed adjudication
  exists, not that a reviewer agreed**, and the record used to let the word
  stand unqualified.
- and `harness/ablation.py` credited the third check with catching those four
  attacks. It had objected only to library code it cannot decide; a genuine
  submission using `decide` the same way trips it too. That named a layer
  that caught nothing, in the one table the README cites as evidence that each
  attack is stopped by the right layer. Only an *unadjudicated* disagreement
  now counts, and an adjudicated one is kept on the row as a note rather than
  dropped.

**And one record that could not be reproduced**, found while checking the
above: `evidence/ablation.json` has thirteen rows — the twelve core attacks
and `A13_mathlib_redefine`, which only runs at tier 3 — while `verify.sh` built
the table from the core results alone, giving twelve. A reader diffing their
run against the record found a missing row and no explanation of it. Tier 3
now rebuilds the table over both result files, and a test pins that the
committed record is what those two files produce.

**One addition to the harness, not a waiver.** A claim recorded as false has
to be backed by something — this search, the derivation search, or a stated
reason why neither can. EULER-SUM-5 is backed by none of those and is
nonetheless refuted *in this repository*, by LANDER-PARKIN, proved from the
1966 witness and checked by the kernel. `harness/counterexample.py` now
recognises that third case by recomputing it: `control.refuted_by` must name a
claim of the same catalogue that is not itself declared false and that a
results record shows certified. It fails closed, and when no results record is
to hand it records that the backing was checked structurally and not by
execution.

**What this does not fix.** The formalizations are still the assistant's. A
historical claim fixes the *verdict* — that is the point of using one — but
whether each Lean statement says what the historical sentence says is a
judgement, and nobody has made it: every `review` block in
`reference/claims_history.json` is PENDING in both `reviewed_by` and
`confirmed_by`. The narrowing of "Mersenne's 1644 list" to its p = 67 entry,
and of Euler's general conjecture to its n = 5 case, are exactly the kind of
step a reader has to accept or reject.

### 6b. Third-party submissions and volume — not done

The first two bullets. Neither is something this repository can do to itself:
an invitation needs someone to accept it, and "AI-generated proofs at volume"
means a workload generated by something other than the party being tested.
Both remain open, and the corpus remains self-written in its *formalizations*
even where the claims are not.
### 6c. kernel3 measured from outside — done, 2026-10-14

The third check's own corpus had the same weakness as the submission corpus:
four adversarial vectors, all written here. The
[Lean Kernel Arena](https://arena.lean-lang.org/) publishes 198 tests for
exactly the layer `kernel3` occupies — 72 that must be rejected, 19 of them
regressions for real Lean kernel bugs, and 126 that must be accepted.

Full account: [`docs/ARENA-RESULT.md`](docs/ARENA-RESULT.md) and
`evidence/arena_run.json`. Reproduce with `harness/arena_run.py`.

| configuration | wrongly accepted | wrongly rejected | correct | declined |
| --- | --- | --- | --- | --- |
| `term_only` (what the third check does today) | **28** | 9 | 151 | 10 |
| `with_spec_passes` (plus 2a–2c) | **23** | 12 | 153 | 10 |

**23 of 72 wrongly accepted.** By the arena's ranking that is a poor score, and
the honest comparison is that con-leche and lean4lean each have 0. It is not a
surprise in kind — A3 has always said the specification layer is assumed, and
that "point this checker at an olean of unknown provenance and the hole is
live". The arena is that case, so the sentence is now a measurement with 23
named tests rather than an argument.

**The passes earned their place and cost something.** They reject 5 of the 28
the term layer takes — `large-elim-prop-bool` (recursor), `nat-rec-rules`
(iota), `054_indNeg`, `057_indNegReducible`, `117_reflOccLeft` (positivity) —
which is the first external evidence they do anything. They also cause **3
false rejections**, all from the iota pass and all one bug: it decides whether
a constructor field is recursive **syntactically**, where Lean decides it after
δ-reduction. A field typed `constType (I α) (I α)` is headed by a definition
that unfolds to expose the family, so Lean generates a recursive call and the
pass derives a rule without one. **Neither Init nor Mathlib contains that
shape**, so the 3410-recursor differential could not have found it; the arena
has three such tests and names them after the behaviour. The pair `055` (good)
and `056` (bad) is the sharpest form: the pass rejects the valid one and
accepts the invalid one.

**The 9 term-layer false rejections confirm the adjudication list from
outside.** `Nat.decidableBallLT.match_5` appears by name (TC-02), and the unit
eta and singleton-recursor tests are TC-01's area. Safe direction, and the
first external evidence that those adjudications describe real mechanisms.

**Four of the 23 are bugs in work just finished, not scope:**
`large-elim-param` (the recursor pass treats a level *parameter* as "not a
`Prop`", but `u := 0` is legal, so a two-constructor inductive gets a large
eliminator — wrong in the **accepting** direction); `orphan-rec` (a recursor
with an empty family is declined where it could be decided); and
`140_falseFromUnsafe` / `141_falseFromPartial` (the `isUnsafe` and `safety`
flags the NDJSON frontend reads and throws away).

Those four and the iota bug are the next round. **The measurement is recorded
before any of them is touched**, so the improvement is measured against a
number written down before it was known how to improve it.


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
