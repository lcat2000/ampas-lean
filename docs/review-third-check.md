# Line-by-line review of the third check

**繁體中文（原始版本）：[review-third-check.zh-TW.md](review-third-check.zh-TW.md)**

## Provenance

`harness/kernel3` (`terms.py`, `parse.py`, `check.py`, ~1,370 lines, with
`harness/Export.lean`) was **not written by the author of the rest of this
suite**. It appeared in `harness/` mid-session, already wired into the verdict
path, unreviewed. It was moved out of the trusted path first (see
`unreviewed/README.md`); this document is the review that followed.

- **Original implementation:** provenance not established.
- **This review, the findings below, and the fixes in §4:** by this round's
  author.
- `unreviewed/kernel/` keeps the **unmodified** original for comparison
  (`diff -ru unreviewed/kernel harness/kernel3`).

## 1. What it gets right

Worth recording, because several of the easiest things to get wrong are
correct here.

| Item | Assessment |
| --- | --- |
| K-like reduction (`_to_ctor_when_k`) | **Correct.** It verifies that the constructor application really has the major premise's type before substituting. Without that check, the existence of any equality proof would make arbitrary terms definitionally equal — the code even carries a comment saying so. |
| Definitional proof irrelevance (`_proof_irrel`) | **Correct.** Checks that the type of `a`'s type is `Sort 0` *and* that `ta ≡ tb`. |
| `level_leq` | Standard algorithm (strip `succ`, distribute `max`, split `imax` arguments into 0 and `succ`). Where incomplete it returns `False` — i.e. **it errs toward rejection**, the safe direction for a checker. |
| `Nat` literal arithmetic | `n/0 = 0`, `n%0 = n`, truncated subtraction all match Lean. |
| `Quot.lift` / `Quot.ind` argument positions | Match the real signatures (5/3 and 4/3). |
| `infer` on a loose de Bruijn variable | **Raises**, rather than silently substituting — fail-closed, and it is what makes F-3 unreachable. |
| Projection inference (`_infer_proj`) | Requires the value's type head to be the named structure, then replaces earlier fields by projections. Correct. |

It also catches real problems rather than idling: it independently rejected the
kernel-bypass attack (`declared False, inferred True`), and perturbing theorem
types in an export produced 24 errors.

## 2. Findings

### F-1 (high, fixed) — a statement-mode export reported "all checked"

`Export.lean --statement` emits theorems as `#THMTYPE`: type, no proof.
`check_decl` had **no branch** for `thmtype` — it verified the type was a type
and counted it as checked. `env.mode` was parsed and **never examined anywhere**.

Measured: on a statement-mode export the original reported
`checked 27/27, errors 0`, where the only theorem present was an unproved
assumption. A caller reading that as "independently verified" is misled. The
pipeline happened to call in proof mode, but nothing guaranteed or checked it.

### F-2 (high, contained rather than fixed) — inductive specifications are assumed

The code's own docstring says it assumes inductive declarations are legitimate.
Line by line, what is and is not checked:

| Declaration | Checked | **Not** checked |
| --- | --- | --- |
| `ind` | the type is a valid type | strict positivity; constructor universe bounds |
| `ctor` | type valid; after stripping `nparams+nfields` Pis the head is the inductive | that the inductive occurs only in strictly positive positions |
| `rec` | each rule's constructor exists, field count matches, rhs is closed and **well-typed** | that the recursor type is the one the inductive generates; **the `Prop` large-elimination restriction**; that each rule's rhs is what iota should give |

**This is exactly where the classic unsoundness lives.** Two forged exports
demonstrate it (`tests/forgeries/`):

1. **`Prop` large elimination** — a `Prop` with two constructors plus a forged
   recursor eliminating into `Sort u`. Proof irrelevance makes `P.a ≡ P.b`, so
   `P.rec m X Y t ≡ P.rec m X Y u` (argument-wise comparison plus proof
   irrelevance), making `MyTrue` and `MyFalse` interchangeable *as types*.
   Result: **`checked 9/9, errors 0`, `False` proved.**
2. **Non-positive inductive** — `Bad.mk : (Bad → MyFalse) → Bad` with the
   matching recursor and the standard diagonal argument. Result:
   **`checked 7/7, errors 0`, `False` proved.**

A control confirms the hole is in the *assumed specification* rather than a
general collapse: restricting the same recursor to `Prop` (legitimate small
elimination) is correctly rejected
(`expected P → Sort 0, got P → Sort 1`).

Closing it properly means deriving the recursor type and rules the inductive
should generate and implementing a positivity check — roughly the work of
Lean's `inductive.cpp`. More importantly, **getting that check wrong in the
permissive direction is worse than declaring the area an assumption.** So it
was not attempted; the scope is bounded instead (§4).

### F-3 (low, currently unreachable) — `instantiate` does not lift loose indices

`terms.py`'s `instantiate` inserts `vals[i]` without raising its loose de
Bruijn indices by the number of binders crossed, which is correct only when the
substituted term is bvar-closed. In practice the checker is locally nameless
(local variables are `fvar`s) and `infer` raises on a loose bvar, so every call
path satisfies the precondition. But it is an **implicit, unasserted
invariant** and easy to break. Suggested (not implemented): assert it on entry.

### F-4 (low) — `_reduce_proj` does not check the projected structure

`proj Foo i (Bar.mk ...)` reduces to `Bar.mk`'s *i*-th field even when
`Foo ≠ Bar`. `_infer_proj` does check, so well-typed terms are unaffected, but
`whnf` can be called before inference completes. No exploitable path found;
recorded.

### F-5 (low, availability) — `Nat.pow` is unbounded

`a ** b` is evaluated directly, so a huge exponent in an export can exhaust
memory. A denial-of-service issue, not soundness; the sandbox's memory and time
limits cover it.

### F-6 (medium, contained and adjudicated) — iota lacks to-constructor-when-structure

This one was not found by reading; it was found by **pointing the checker at
Mathlib**. It rejects three declarations that both Lean kernels accept:

```
Prod.instLawfulBEq
Nat.Internal.Linear.Poly.denote_reverse
Nat.Internal.Linear.ExprCnstr.denote_toNormPoly
```

All three are **Lean core library declarations, not submission code**:
exporting them from the reference environment with no submission involved
reproduces exactly these three failures (520/523 checked).

The mechanism is pinned to one step. For `Prod.instLawfulBEq`, checking
requires

```
BEq.beq (α × β) (instBEqProd α β instA instB) p q  ≡  (p.1 == q.1) && (p.2 == q.2)
```

Unfolding the instance makes the right side a match on the pair, compiled to
`Prod.rec`, whose major premise is the neutral `p`. **Lean's kernel eta-expands
a neutral of structure type into a constructor application** (`p` ⟶
`Prod.mk p.1 p.2`) so iota can fire; `check.py`'s `_reduce_rec` applies only
`_nat_to_ctor` and `_to_ctor_when_k` (the latter requires a field-free
constructor), so `Prod.rec … p` stays stuck, both sides are neutral, and the
comparison fails.

**Direction: incomplete, not unsound** — it fails to reduce, so it rejects. It
cannot make the checker accept anything false.

**This finding also overturned the gate design.** "Third check reports an error
⇒ certification fails" looked fine on the core corpus (16/16 correct), but the
moment Mathlib was added it vetoed a correct proof that **both Lean kernels
accept** (the Euclid claim). Letting the least complete of three
implementations overrule the other two is wrong.

A fourth instance, **TC-02**, turned up later during the external validation
run: `level_leq` cannot decide the nested `imax` identity in
`Nat.decidableBallLT.match_5` (true for every universe). Same category, same
direction. Both are recorded with mechanism and reproduction in
`reference/third_check_adjudications.json`.

## 3. What was fixed

Rather than closing F-2's hole, the checker was made to **vouch only for what
it actually checks**.

1. **Refuse statement mode** (fixes F-1). `check_env` reports an error for
   `mode != "proof"` and lists every `#THMTYPE` declaration as unproved.
   `thmtype` no longer counts toward `checked`.
2. **Provenance gate.** `decl_fingerprint(d)` serializes, for every inductive,
   constructor, recursor and quotient constant, its type and its whole
   specification — including each recursor rule's rhs, so a forged recursor
   cannot pass as a baseline declaration of the same name.
   `check_env(..., baseline=...)` splits the assumed declarations into
   `baseline_assumptions` (fingerprint matches the trusted core) and
   `introduced_assumptions`, the latter **reported explicitly as not covered**.
3. **The baseline's definition**, which the first attempt got wrong. It must be
   **every assumed declaration of the trusted core**, not only those reachable
   from the reference statements. The first version used the statement closure
   (213), and three **correct** submissions were reported as introducing
   `Subtype`, `Ordering`, `Ord`, `Std.TransCmp`, `Ampas.PL.Derives.rec` — all
   legitimate declarations of Init and the trusted reference that the
   statements simply do not mention. Safe in direction, wrong in substance:
   that noise would drown a real introduction. Fixed by adding
   `Export.lean --specs`, which walks the whole environment and emits only the
   assumed declarations with no dependency closure, reproducibly via
   `harness/make_baseline.py`:

   | Baseline | Source modules | Assumed declarations |
   | --- | --- | --- |
   | `reference/kernel_baseline.json` | `AmpasRef.Guards` + `AmpasRef.Challenge` (incl. Init) | 2,157 |
   | `reference/kernel_baseline_mathlib.json` | `AmpasRef.ChallengeMathlib` (incl. the Mathlib cone) | 9,638 |

   The files store the **SHA-256 of each fingerprint**, not the fingerprint:
   set membership is all the gate needs, and the serialized types run to 12 MB
   for the Mathlib cone.

Measured after the fixes:

| Case | Result |
| --- | --- |
| Genuine proofs | `errors=0`, `introduced=0` → **CONFIRMED** |
| Kernel-bypass attack | `errors=1` → NOT CONFIRMED (caught independently) |
| Forged large elimination | `errors=0` but `introduced=7` → **NOT CONFIRMED** |
| Forged non-positive inductive | `errors=0` but `introduced=4` → **NOT CONFIRMED** |
| Statement-mode export | refused outright |

This does **not** give it the ability to verify inductive specifications. It
makes it refuse to vouch for what it cannot verify, so the forgery routes can
no longer produce a clean result.

## 4. Verdict: usable as a third check, with its scope enforced in code

**Yes**, under these conditions.

1. **A clean result from it means exactly:** every declaration's type was
   re-checked, and every inductive specification relied upon matched the
   trusted baseline field for field. That sentence is the content of the
   `covers` field and it goes into the evidence record.
2. **It must never be the sole or decisive kernel evidence.** On the inductive
   layer it is the weakest of the three: Lean's own kernel and lean4lean both
   check inductives; it does not.
3. **Gate (as revised after F-6):** certification rests on the two Lean kernels
   plus the auditor. The third check is **corroboration, not a veto**.
   - no errors → `CONFIRMED`, recorded in the claim's `corroboration`;
   - errors on an **unadjudicated** declaration → `DISAGREEMENT (unadjudicated)`,
     **blocks certification**. This keeps its value: when it rejects something
     unexpected, stop and let a human look;
   - errors on a declaration with an adjudication record (reviewer, date,
     mechanism, reproduction) → does not block; status and adjudication are
     recorded;
   - `introduced_assumptions` non-empty → does not block (that layer is covered
     by the other two kernels), but the limitation is recorded.
4. **In this pipeline F-2's hole is unreachable**: the export comes from an
   olean the submitter compiled, and a forged inductive or recursor does not
   survive Lean's own elaborator and kernel. That is to say — the assumption is
   discharged by the **primary kernel**, not by nobody. Point the checker at an
   olean of unknown provenance, which is the case where an independent checker
   is most valuable, and the hole is live.

**What it genuinely adds:** an independent opinion on the term layer — a
different language, a different author, no shared code with Lean and no use of
Lean's elaborator. It objected to the kernel-bypass attack's bad declaration,
which the Lean kernels also rejected -- so it CORROBORATED them there rather
than catching something they missed; the suite reported that as a
"DISAGREEMENT" until 2026-10-14, which inverted what happened. That is
not a small thing. **What it does not add** is an independent opinion on the
inductive layer; and per F-6 it is not complete on library-scale code either.

## 5. In one sentence

It earns a place as a third check, but only as the **third**:

- the core corpus — all 16 re-checked, 0 errors, 0 uncovered assumptions, and
  it caught the kernel bypass on its own;
- at Mathlib scale, four adjudicated incompleteness cases (F-6 / TC-02) on top
  of the inductive specification layer it never checks (F-2);
- so it **corroborates** the term layer and **establishes** nothing. Any
  conclusion resting on it alone is overstated.
