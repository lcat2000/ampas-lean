# The formalization-fidelity process

**繁體中文（原始版本）：[review-formalization.zh-TW.md](review-formalization.zh-TW.md)**

A Lean kernel can answer "does this proof type-check under these axioms and
definitions". It **cannot** answer "is this Lean statement a faithful rendering
of the original natural-language claim". Only a person can judge that.

The purpose of this process is not to automate that judgement. It is to make it
an **auditable artifact**: bound to a definite mathematical object, supported by
machine-checked guarantees, attributable to a key, and unable to drift silently
afterwards.

## Four parts

### 1. Content-addressed freezing (not source text)

Each reference statement freezes two hashes
(`reference/attestations/<CLAIM>.json`):

| Field | Content | Why |
| --- | --- | --- |
| `statement_sha256` | structural serialization of the **elaborated** statement | reformatting, comments and binder renaming do not change it; a change of meaning always does |
| `closure_sha256` | serialization of every constant the statement transitively depends on, **including definition bodies** | quietly redefining `IsEven` leaves the statement text untouched — this hash moves |

The serialization is produced by `harness/Audit.lean` (`freeze` mode) walking
every `Expr` constructor itself. It does not use the pretty printer and does not
depend on any Lean version's `ToString`. A theorem's **proof is not frozen**
(proof irrelevance): what is frozen is the statement, not one particular proof
of it.

`closure_entries` records each constant separately, so drift detection can name
which constant changed.

### 2. Machine-checked guarantees (guards)

The human judgement is supported by two kinds of Lean theorem, kernel-checked
like any other (`reference/AmpasRef/Guards.lean`):

- **Non-vacuity** — the hypotheses can hold simultaneously, so the statement is
  not vacuously true.
- **Hypothesis necessity** — dropping **any** hypothesis makes the statement
  **false**. This blocks "quietly weaken the claim by adding a hypothesis".

The point is that these guards' *types* are **not written by a person**: the
auditor computes them from the reference statement itself (`sanity` mode) and
compares by the kernel's definitional equality. A guard therefore cannot be a
proof of something weaker. For `SUB`:

```
expected_witness:    ∃ a b, b ≤ a
expected_necessity:  ¬∀ (a b : Nat), a - b + b = a
```

The second is the Lean-convention trap made mechanical: `Nat` subtraction
truncates, `0 - 1 + 1 = 1 ≠ 0`, so the hypothesis `b ≤ a` **must** be there.
`DIV` is the same (`0 / 0 = 0 ≠ 1`).

Claims with guards: `SUB`, `DIV`, `EVEN`, `DVD` (6 necessity, 4 non-vacuity,
all satisfied). Claims without hypotheses are recorded as `NO_HYPOTHESES`.

**Refutations are different.** A claim of the form `¬P` is `P → False`, so the
hypothesis machinery would demand a non-vacuity proof of `P` — the very thing
the theorem refutes. This surfaced as a real design flaw when axiom
independence was added. A claim whose conclusion is `False` is marked
`REFUTATION`: non-vacuity and necessity do not apply, and a **nontriviality**
guard is required instead, ruling out the degenerate reading. Stated honestly:
a nontriviality guard's statement is chosen by the reviewer rather than
computed from the claim, so it is kernel-checked but its *relevance* is a human
judgement.

### 3. Attributable sign-off

For each claim three roles are recorded **separately**, because collapsing
them is how a record comes to assert a judgement nobody made:

| Field | Who | What it covers |
| --- | --- | --- |
| `prepared_by` | the harness | the machine-derived parts: hashes, closure list, guard types |
| `reviewed_by` | whoever formed the fidelity judgement | the checklist below |
| `confirmation` | the accountable owner | `confirmed_by`, `mode` (`personally_reviewed` or `delegated`) and the recorded `basis`; null until given |

The reviewer's part records identity, date, the `faithful` judgement, a note,
and a checklist:

| Check | The question |
| --- | --- |
| `statement_matches_text` | the Lean statement says what the text says |
| `no_unintended_convention` | `Nat` truncation, division by zero, coercions all considered |
| `quantifier_order_checked` | quantifier order is right |
| `hypotheses_necessary_and_satisfiable` | backed by the guards above |
| `definitions_reviewed` | every definition in the closure has been read |
| `conclusion_not_weakened` | the conclusion has not been weakened |

#### Per-item evidence: what each tick points at

Until 2026-10-14 those six answers were booleans and nothing else. All
thirteen signed attestations answer all six `true`, so a reviewer who worked
through a statement carefully and one who ticked six boxes left
**byte-identical records** — the checklist could not distinguish them, and
neither could anyone reading it afterwards.

`harness/checklist_evidence.py write` derives, from the frozen statement, the
object each mechanisable tick is a claim about, and records it in
`reference/checklist-evidence*.json` bound to that statement's hash:

| Check | What the record now points at |
| --- | --- |
| `statement_matches_text` | **nothing — `machine_derivable: false`** |
| `no_unintended_convention` | the convention-bearing constants the statement uses, those one of this repository's definitions brings in a level down, and the constants the convention list has no rule for |
| `quantifier_order_checked` | the binder sequence in order, split into data and hypotheses, hashed over the **order** so a permutation is detected |
| `hypotheses_necessary_and_satisfiable` | each hypothesis binder against the guard that covers it; a statement with two hypotheses and one necessity guard fails |
| `definitions_reviewed` | this repository's own definitions in the closure, each with its own hash |
| `conclusion_not_weakened` | the conclusion, pretty and serialized, hashed over the serialization |

`verify` re-derives all of it and fails on `EVIDENCE DRIFT` if the statement
it was derived from is not the statement in the reference now.

**Three things this does not do**, each of which it would be easy to read it
as doing:

1. **It does not decide fidelity.** `statement_matches_text` is the item that
   matters most and the only one with nothing behind it. A layer that quietly
   supplied *something* there would be worse than none, so
   `tests/test_checklist_evidence.py` fails if a sixth item ever acquires
   machine evidence. `docs/CONLECHE-EVALUATION.md` is why: a checker with a
   ZFC model-theoretic consistency proof accepts `A06_wrong_statement`.
2. **It does not record that anyone read it.** All thirteen attestations were
   signed before it existed, which `verify` reports by name in
   `attestations_signed_before_the_evidence_existed`. The evidence shows what
   the ticks were *about*; a tick made with it in hand would be a stronger
   claim and none here is one.
3. **The convention list is a judgement.**
   `reference/fidelity_conventions.json` holds the traps this repository
   thought of. A statement whose trap is absent reports no convention at all,
   so `last_reviewed` and the `unmatched_statement_constants` channel are what
   make an empty result mean anything — that channel is how the `Nat.Prime`
   and `^`-associativity rules came to exist.

The whole record is signed with a **detached Ed25519 signature**
(`reference/reviewer_key.json` is the public key; the private key is **not** in
this repository). The signature covers every field except itself, so even
editing the `text` field invalidates it.

**What the signature does and does not do.** Since 2026-10-13 the key is
`kai-chang-2026-10`, generated on the repository owner's own machine and never
present in the container that builds this repository; `custody` in the public
key record states that. So a signature establishes that the record was signed
by the holder of that key and has not been altered since freezing. It does
**not** establish that the holder is the person named: no certificate, web of
trust or signed commit chain binds the key to an identity, and `custody` is an
assertion by the party it describes. Who reviewed and who confirmed remain the
separate fields above; the signature does not merge them.

Two earlier states are worth knowing, because both were wrong in instructive
ways. The key was a demonstration key held by nobody, which attributed
nothing to anyone — honest, but it made the whole sign-off decorative. Before
that its id was `kai-chang-morris-2026-10` while the private key sat in a
build container, which implied custody that did not exist. A key's name is not
evidence of who holds it, which is why `keygen` now records custody explicitly
and defaults to a stated `UNDECLARED`.

### 4. Drift detection

`harness/ampas_review.py verify` re-derives everything from the **current**
reference and compares; any difference fails:

| Scenario | Detection (measured) |
| --- | --- |
| reference statement changed (`SUB` loses its hypothesis) | `STATEMENT DRIFT` |
| a definition in the closure changed (`IsEven := True`, statement text untouched) | `CLOSURE DRIFT — changed: Ampas.IsEven` |
| sign-off record tampered with (prose quietly drops a hypothesis) | `SIGNATURE INVALID` |
| sign-off record deleted | `no attestation (statement is not signed off)` |
| a guard no longer holds | `guards no longer satisfied` |
| checklist incomplete / `faithful` not attested | fails, naming what is missing |

The second row is the whole design in one line: **the statement text did not
change, the meaning did, and the process still stops it.** A side effect is
that `IsEven := True` also breaks the guards (`¬IsEven 1` becomes unprovable),
giving a second independent signal.

## Operating it

```bash
# 1. ask the auditor what guards it requires (before writing any)
harness/audit sanity_req.json        # prints expected_witness / expected_necessity

# 2. prove them in reference/AmpasRef/Guards.lean and build

# 3. freeze (refused if the guards do not hold)
python3 harness/ampas_review.py freeze

# 4. the reviewer signs (private key stays with the reviewer)
python3 harness/ampas_review.py sign --key <private.pem> --key-id <id>

# 5. derive the per-item checklist evidence (after any statement change)
python3 harness/checklist_evidence.py write

# 6. verify on every run (CI): re-derives the evidence too, and fails if it
#    was derived from a statement other than the one in the reference now
python3 harness/checklist_evidence.py check
python3 harness/ampas_review.py verify --out build/review_verification.json
```

`freeze` **refuses** when a guard is unsatisfied, unless `--allow-guard-failure`
is passed explicitly, which records the failure in the record itself.

## What this process does not solve

- **It does not prove fidelity.** A statement that is frozen, signed and
  guarded is still only a statement that *somebody judged* faithful. The guards
  exclude two specific errors (vacuity, over-strong hypotheses) and a
  degenerate calculus. They do not exclude "this statement is about something
  else". The external validation pair demonstrates the residue: a submission
  with no `sorry`, no added axiom and both kernels satisfied, which proves the
  restricted statement under the general claim's name.
- **The quality of the reviewer's judgement is out of scope.** The process
  guarantees the judgement is attributed, dated and drift-resistant. It does
  not guarantee it is correct. Since 2026-10-14 the per-item evidence makes a
  *careless* judgement visible — a tick now points at a named binder sequence,
  a named definition list, a named set of conventions — which is a different
  and much smaller thing than making a judgement correct.
- **The natural language may itself be ambiguous.** If the text is imprecise,
  what is frozen is a commitment to one reading of it.
- **Key management is out of the model.** This repository uses a demonstration
  key; real deployment needs custody and a binding to the reviewer's identity.

`ROADMAP.md` §5 lists the approaches worth trying against the fidelity problem
itself, the most promising being **formalization triangulation**: have several
parties formalize the same claim independently and then prove the statements
equivalent in Lean, so a disagreement localizes a fidelity problem without
anyone having to read both.
