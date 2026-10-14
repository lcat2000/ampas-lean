# A checker different in kind: con-leche, evaluated

**ROADMAP 1.3.** The two kernels this suite runs implement the same algorithm
from the same specification — and, as [ROADMAP 1.3a](../ROADMAP.md) records,
one of them is derived from the other's C++ original. So "two kernels agreed"
is agreement between relatives. This is the evaluation of a candidate that is
different in *kind*.

Machine-readable record, with every number below:
[`reference/conleche_evaluation.json`](../reference/conleche_evaluation.json).
Reproduce with [`scripts/check-with-conleche.sh`](../scripts/check-with-conleche.sh).

## What con-leche is

[con-leche](https://github.com/leanprover/con-leche) is an external Lean proof
checker, written in Lean, with its own term representation — it does not use
`Lean.Expr`, so it does not inherit the unverified C++ routines for that type.
Its distinguishing property is a theorem, proved in Lean:

```lean
theorem model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration) (env : Env)
    (accepted : checkDecls .verified pins ds = .ok env) :
    Nonempty (Model V env)
```

If it accepts a declaration set, that set has a **model in set theory**; in
particular `False` denotes the empty set, so no accepted theorem's statement is
false in the model. A corollary, `no_False_declaration`, states that a file
declaring a `theorem … : False` is never accepted.

That is a different kind of evidence from "a second implementation agrees". It
is also, upstream states, a checker and a proof written by Claude under
supervision by Joachim Breitner at the Lean FRO. Recorded because this
repository is about AI-assisted proof work, and because it cuts the way this
repository argues about its own artefacts: what makes the checker worth
trusting is a machine-checked theorem, not who or what typed it.

## What was actually verified here, and what was not

The build was the **full** one — 660 Lake jobs, including the proof lane. A
verified kernel whose verification you have not built is not evidence of
anything.

Both theorems were then checked for what they rest on, against that build:

```
'ConLeche.no_False_declaration' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConLeche.model_exists'         depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. The proof is complete, for the three standard axioms.

**But the theorems are conditional.** Both are parameterised over
`(V : Type w) [SetTheory V]` — an interface for ZF without infinity and choice
plus an ω-chain of Grothendieck universes. Upstream discharges that hypothesis
from Mathlib's `ZFSet` under Carneiro's ω-many-inaccessibles hypothesis, in a
separate `bridge/lean4lean-model` package. **That package was not built here.**
So what this machine verified is the conditional statement, not the
instantiation of its hypothesis.

## The four runs

| input | outcome | time | peak RSS |
| --- | --- | --- | --- |
| `AmpasRef.Guards` — the trusted reference environment | **declined** (`sorryAx` in a value) | 33 s | 0.43 GiB |
| `corpus/Genuine.lean` — a genuine submission AMPAS certifies | **accepted**, 58107 declarations | 43 s | 0.39 GiB |
| `corpus/attacks/A04_native_lie.lean` — `native_decide`; **both Lean kernels accept it** | **declined** (non-standard axiom) | 3 s | 0.42 GiB |
| `corpus/attacks/A06_wrong_statement.lean` — a real proof of `∀ a, a + a = a + a` filed as `add_comm_nat` | **accepted**, 58102 declarations | 40 s | 0.42 GiB |

Each read in turn.

### The reference environment cannot be checked, and that is about AMPAS

AMPAS states every frozen claim as `theorem … := sorry`: the reference module
is a statement of what is claimed, not a proof of it. So the environment
contains `sorryAx` in a value by construction, and con-leche refuses it. The
thing to check is a **submission's** closure, which is what the other three
runs are.

### A genuine submission is accepted — this is the result 1.3 asked for

58107 declarations, the proof plus all of Init/Lean/Std it depends on, accepted
by a checker whose acceptance is proved to imply a set-theoretic model. 43
seconds and 0.39 GiB on two cores, which is cheaper than this suite's own
tier-1 run.

Against the Tao finding — that two implementations can share a failure — and
against 1.3a — that this suite's second kernel is a relative of the first — a
third acceptance of this kind is genuinely different evidence.

### A04: read the reason before crediting the checker

Both Lean kernels accept `A04_native_lie`
(`kernel_replay: true`, `kernel_replay_independent: true`, in
`evidence/corpus_results_threechecks.json`). con-leche does not. So a checker
different in kind does refuse something the Lean kernels take.

**But it refuses it for its axiom restriction** — it accepts only the three
standard axioms — which is the layer AMPAS's own axiom policy already occupies,
and which already flags this submission as `NATIVE_EVALUATION`. The
model-theoretic proof did no work here. Calling this "the verified kernel
caught an attack the Lean kernels accepted" would be exactly the overclaim
1.3a corrects about lean4lean.

Note also that con-leche's message is "not implemented yet": a **decline**, not
a rejection on the merits. A decline is not evidence that a proof is wrong.

### A06 is accepted, and that is the finding that matters

`A06_wrong_statement` proves `∀ a : Nat, a + a = a + a` and files it under the
name of `add_comm_nat`. It is a real proof. It is a theorem. It is not the
claim it is filed under — and con-leche accepts it, together with its 58102
supporting declarations.

So **the fidelity gap is not a weakness of unverified kernels that a verified
one closes.** It is outside what any kernel decides, however strong its
soundness proof: a kernel answers "is this a proof of that statement", and the
question AMPAS exists for is "is that statement the claim". In this suite only
the statement comparator and a human reading stand between A06 and a
certificate, and adding con-leche would not change that by one step.
[ASSUMPTIONS A1](../ASSUMPTIONS.md).

## Third-party evidence this repository did not produce

The [Lean Kernel Arena](https://arena.lean-lang.org/) benchmarks about 28 Lean
checkers against shared suites: proofs that must be rejected, proofs that must
be accepted, 19 bug-regression tests, corner cases, performance. It is
third-party and adversarial, which is what [ROADMAP 6](../ROADMAP.md) asks for
and what nothing in this repository can supply about itself.

Read on 2026-10-14, with a round in progress, it reported con-leche with 0
wrongly accepted and 0 wrongly rejected (3 soundness and 6 completeness
declines) and mathlib in ~24.7 min / 7.1 GB; and lean4lean with 0 wrongly
accepted, 0 wrongly rejected, mathlib in ~38.8 min / 11.6 GB. **Those are the
arena's numbers, not this repository's.**

## Verdict

**Different in kind: yes.** **Would strengthen a certificate: yes** — it adds
an acceptance whose meaning is "this declaration set has a model in set
theory", not "another implementation agrees".

**What it does not add:** anything about formalization fidelity (A06); anything
the axiom policy does not already catch on the attack corpus (A04); an
unconditional guarantee (the `[SetTheory V]` hypothesis was not instantiated
here); and any check of the reference environment, which contains `sorry` by
design.

**Integration: an optional tier, not a default.** `scripts/check-with-conleche.sh`
does the whole thing reproducibly and is not wired into `scripts/verify.sh`.
The reasons are cost, not doubt: a second 3 GB toolchain (Lean 4.35.0-rc3
against this suite's 4.33.0), a 660-job build of the checker and its proofs, a
build of lean4export at 4.33.0 to read this suite's oleans, and a ~333 MB
NDJSON export per submission. Making that the default would make a clean
checkout unverifiable on an ordinary machine.

And nothing is claimed silently: a certificate does not mention a con-leche
acceptance unless one was run and recorded.
