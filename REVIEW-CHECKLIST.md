# Formalization review — all 13 claims

**繁體中文摘要在最後一節。**

## Who did what

| Role | Who | What it means |
| --- | --- | --- |
| `prepared_by` | the AMPAS harness | statement and closure hashes, the closure list, and the guard *types* — all machine-derived from the elaborated statement, none of it a judgement |
| `reviewed_by` | Claude (Anthropic assistant), round 3 | the fidelity judgement recorded below: each statement read against its text, its closure definitions read, the six checklist items checked |
| `confirmed_by` | lcat2000 (repository owner), **mode: delegated** | the owner delegated the approval decision ("如果你覺得要 approve 就 approve", 2026-10-13) and has **not** personally read the statements |

This replaces the earlier arrangement, where a single `attested_by` field was
filled with the owner's name for 11 records the assistant had prepared,
asserting that he had personally confirmed six checklist items per claim. He
had not. The three roles are now separate fields and
`harness/ampas_review.py verify` checks them separately, so a record cannot
pass by naming someone for work they did not do.

**The signature attributes nothing to a person.** `reference/reviewer_key.json`
is a demonstration key generated inside the container that produced this
repository and held by nobody. It authenticates that an attestation has not
been altered since freezing — no more. Its previous id,
`kai-chang-morris-2026-10`, wrongly implied the owner's custody and was
replaced for that reason.

**What a reader should do with this document.** It is the reasoning, not an
authority. Every machine-derived figure in it is reproducible
(`harness/ampas_review.py freeze`), and the judgements are stated so they can
be disagreed with. If you are relying on any of these claims, review the ones
you rely on yourself.

---

## Two findings from doing the review

Both were found by reading the reference module rather than by running
anything, and both are fixed in this commit.

### The reference module declared two statements that no catalogue knew about

`AmpasRef.Challenge` declared **12** theorems; `reference/claims.json`
catalogued **10**. The two extras were modal-logic independence statements
(`ml_T_independent_of_K`, `ml_4_independent_of_KT`), added in round 2 and
never catalogued. They were therefore never frozen, never attested, never
guarded and never checked by anything — while the module's own header says
every theorem in it is the frozen statement of a claim in `claims.json`. A
submission could have declared either name and the driver would have ignored
it.

Fixed: moved to `reference/future/ModalLogic.lean`, compiled by nothing and
trusted by nothing, and `tests/test_math_verification.py` now checks that the
module's theorem set and the catalogue's claim set are equal. That test runs
in tier 0, with no Lean.

### The `Ampas.ML` namespace was dead code inside the trusted reference

The modal system K / K+T definitions sat in `reference/AmpasRef/Defs.lean`,
the trusted reference, used by nothing that any claim depends on (no attested
closure mentions a single `Ampas.ML` constant). Unused definitions inside the
trusted reference are a liability: a reader has to establish for themselves
that they are inert. Moved out with the statements above. This shrank the
trusted provenance baseline from 2,157 assumed declarations to 2,133.

---

## The claims

Notation: **statement** is the frozen Lean statement; **closure** counts the
constants the statement transitively depends on, bodies included; **guards**
are the kernel-checked theorems whose *types the auditor computes* from the
statement, so a guard cannot be a proof of something weaker.

### ADD — `Ampas.Claims.add_comm_nat`

- **Text:** Addition of natural numbers is commutative.
- **Statement:** `∀ a b : Nat, a + b = b + a`
- **Closure:** 31 constants, none AMPAS-defined. **Guards:** none (no hypotheses).
- **Review:** direct rendering. No convention trap: `Nat` addition is total and
  the claim needs no hypothesis. Quantifier order irrelevant (both universal).
- **Verdict: faithful.**

### SUB — `Ampas.Claims.sub_add_cancel_nat`

- **Text:** For natural numbers a and b with b ≤ a, (a − b) + b = a.
- **Statement:** `∀ a b : Nat, b ≤ a → a - b + b = a`
- **Closure:** 62 constants, none AMPAS-defined.
- **Guards:** non-vacuity `∃ a b, b ≤ a` — OK; necessity `¬∀ (a b : Nat), a - b + b = a` — OK.
- **Convention trap (the point of this claim):** Lean's `Nat` subtraction
  truncates at 0, so `0 - 1 + 1 = 1 ≠ 0`. Without `b ≤ a` the statement is a
  *different and false* claim. The necessity guard is exactly that fact,
  machine-checked. Note `a - b + b` parses as `(a - b) + b`, matching the
  text's parentheses.
- **Verdict: faithful.**

### EVEN — `Ampas.Claims.even_add_even`

- **Text:** The sum of two even natural numbers is even.
- **Statement:** `∀ a b : Nat, IsEven a → IsEven b → IsEven (a + b)`
- **Closure:** 53 constants, including `Ampas.IsEven`.
- **Definition reviewed:** `IsEven n := ∃ k, n = 2 * k`. This is the intended
  meaning of "even", and it makes 0 even (k = 0), which is correct and
  standard.
- **Guards:** non-vacuity `∃ a b, IsEven a ∧ IsEven b` — OK; necessity, both
  directions — OK (dropping either hypothesis is false: 1 + 2 = 3).
- **Verdict: faithful.**

### DVD — `Ampas.Claims.dvd_trans_nat`

- **Text:** Divisibility of natural numbers is transitive.
- **Statement:** `∀ a b c : Nat, a ∣ b → b ∣ c → a ∣ c`
- **Closure:** 47 constants, none AMPAS-defined — it uses Lean's standard
  `Dvd` instance for `Nat` (`a ∣ b ↔ ∃ c, b = a * c`).
- **Guards:** non-vacuity `∃ a b c, a ∣ b ∧ b ∣ c` — OK; necessity, both — OK.
- **Convention note:** under Lean's definition `a ∣ 0` holds for every `a`, and
  `0 ∣ 0`. Neither breaks transitivity, and the claim is about transitivity
  only.
- **Verdict: faithful.**

### GREATER — `Ampas.Claims.exists_greater`

- **Text:** Every natural number has a strictly greater natural number.
- **Statement:** `∀ n : Nat, ∃ m, n < m`
- **Closure:** 17 constants. **Policy:** `axioms: []` — constructive, so a
  witness must be given without `Classical.choice`.
- **Review:** **quantifier order is the thing to check here** and it is right:
  `∀ n, ∃ m` ("every n has some greater m"), not `∃ m, ∀ n` (which would be
  false). Strict `<`, matching "strictly greater".
- **Verdict: faithful.**

### DIV — `Ampas.Claims.div_self_pos`

- **Text:** For every positive natural number n, n / n = 1.
- **Statement:** `∀ n : Nat, 0 < n → n / n = 1`
- **Closure:** 126 constants, none AMPAS-defined.
- **Guards:** non-vacuity `∃ n, 0 < n` — OK; necessity `¬∀ (n : Nat), n / n = 1` — OK.
- **Convention trap:** Lean defines `n / 0 = 0`, so at `n = 0` the unguarded
  statement is false. The hypothesis is required, and the necessity guard is
  that fact.
- **Verdict: faithful.**

### PL-IND — `Ampas.Claims.pl_independent`

- **Text:** In classical propositional logic (Hilbert system A1–A3 + modus
  ponens), the theory {p0 → p1} neither proves nor refutes p1.
- **Statement:** `PL.Independent PL.T_imp (PL.Fm.var 1)`
- **Closure:** 32 constants, 14 AMPAS-defined — the proof system is *part of
  the trusted reference*, so an independence proof for a different or weaker
  calculus is a different statement and the closure check rejects it.
- **Definitions reviewed:**
  - `Fm` — `var | imp | neg`: the language with → and ¬. ✓
  - `Derives T` — `hyp` (hypotheses as a predicate), `a1 : φ → (ψ → φ)`,
    `a2 : (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`,
    `a3 : (¬φ → ¬ψ) → (ψ → φ)`, `mp`. These are the **Łukasiewicz axioms**,
    the standard Hilbert presentation of classical propositional logic in
    {→, ¬}. The text's "classical propositional logic (A1–A3 + modus ponens)"
    is accurate. ✓
  - `Independent T φ := ¬Derives T φ ∧ ¬Derives T (neg φ)` — "neither proves
    nor refutes". ✓
  - `T_imp := fun φ => φ = imp (var 0) (var 1)` — the theory {p0 → p1},
    one formula, not a schema. ✓ matches "the theory {p0 → p1}".
- **Is the claim true?** Yes: p0 = ⊥, p1 = ⊥ satisfies p0 → p1 and falsifies
  p1; p0 = ⊥, p1 = ⊤ satisfies p0 → p1 and falsifies ¬p1.
- **Verdict: faithful.**

### EL-IND — `Ampas.Claims.el_comm_independent`

- **Text:** The monoid axioms do not derive commutativity in equational logic,
  and adding commutativity does not make the theory inconsistent (x = y stays
  underivable).
- **Statement:** `EL.Independent EL.monoid EL.comm`
- **Closure:** 60 constants, 30 AMPAS-defined.
- **Definitions reviewed:**
  - `Term` — `var | one | mul`. ✓
  - `Derives E` — `ax` (an axiom instance under any substitution σ applied to
    both sides), `refl`, `symm`, `trans`, `congr` (for `mul`). That is exactly
    the derivation system of equational logic; `one` is a constant so needs no
    congruence rule. ✓
  - `monoid` — `(xy)z = x(yz)`, `1·x = x`, `x·1 = x`: the usual presentation. ✓
    With `ax` applying substitutions, these act as schemas, which is the
    correct encoding. ✓
  - `comm` — `xy = yx`. ✓
  - `Independent E e := ¬Derives E e.lhs e.rhs ∧ ¬Derives (E ∪ {e}) x y`. The
    second conjunct is the important one: an equational theory cannot *refute*
    an equation, so "independent" has to rule out the degenerate case where
    adding the equation collapses everything. It does, and the text says so. ✓
- **Is the claim true?** Yes: the free monoid on two generators is
  non-commutative; the free commutative monoid does not identify distinct
  variables.
- **Verdict: faithful.**

### PL-AXIOM-IND — `Ampas.Claims.pl_a3_independent`

- **Text (tightened in this commit):** In the Hilbert system of
  `AmpasRef.Defs`, the A3 instance for p0 and p1 ((¬p0 → ¬p1) → (p1 → p0)) is
  not derivable from axioms A1 and A2 by modus ponens alone. Since a derivable
  schema would give every instance, this shows A3 is an independent axiom of
  the calculus.
- **Statement:** `¬ PL.DerivesPos PL.Empty PL.a3_instance`
- **Closure:** 25 constants, 13 AMPAS-defined.
- **Definitions reviewed:**
  - `DerivesPos` — `hyp`, `a1`, `a2`, `mp`; **A3 absent**. The same language,
    a strictly weaker calculus. ✓
  - `Empty := fun _ => False` — the empty theory, so what is derivable is
    exactly what the axioms and modus ponens give. ✓
  - `a3_instance := (¬p0 → ¬p1) → (p1 → p0)` — the A3 schema at p0, p1. ✓
- **Why I changed the text.** It previously said "axiom A3 … is not
  derivable", while the statement is about one instance. One instance being
  underivable *implies* the schema is underivable (a derivable schema gives
  every instance), so the statement was never weaker than the text — but the
  text read as if the statement quantified over instances, and it does not.
  The new wording states what is proved and then the inference.
- **Guard — and the honest caveat.** This is a **refutation** (conclusion
  `False`), so non-vacuity and necessity do not apply; demanding non-vacuity
  would mean demanding a proof of the very thing refuted. The auditor requires
  a *nontriviality* guard instead: `Ampas.Guards.pos_nontrivial`, which proves
  `DerivesPos Empty (p0 → p0)` — the A1+A2 fragment still derives something,
  so the independence is not "this calculus proves nothing".
  **The caveat:** unlike witness and necessity, a nontriviality guard's
  statement is *chosen by the reviewer*, not computed from the claim. It is
  kernel-checked, but its relevance is my judgement. I judge it the right
  degenerate reading to exclude. A reader who wants a different nontriviality
  property should say so.
- **Is the claim true?** Yes, by the standard separation: interpret ¬ as the
  identity. A1 and A2 do not mention ¬ and remain implicational tautologies;
  modus ponens preserves truth; A3 becomes (p0 → p1) → (p1 → p0), false at
  p0 = ⊥, p1 = ⊤.
- **Verdict: faithful.**

### PL-BOGUS — `Ampas.Claims.pl_bogus_independent`

- **Text:** FALSE CLAIM, kept as a control: {p0 → p1} does not prove p1 → p1.
  This is false (p1 → p1 is a theorem of pure logic), and must never be
  certified.
- **Statement:** `PL.Independent PL.T_imp (PL.Fm.imp (PL.Fm.var 1) (PL.Fm.var 1))`
- **Review:** the statement is a faithful rendering of the *false* claim the
  text states. Its first conjunct (`¬Derives T_imp (p1 → p1)`) is false, since
  p1 → p1 is derivable from A1 and A2 by modus ponens, so the conjunction is
  false and no sound submission can certify it.
- **What `faithful: true` means here**, since it is easy to misread: the Lean
  statement says what the text says. The text says the claim is false. Both
  are consistent; the record is not asserting that p1 → p1 is underivable.
- **Verdict: faithful as a control.**

### PRIMES — `Ampas.Claims.infinitude_of_primes` (Mathlib tier)

- **Text:** There are arbitrarily large prime numbers: for every natural
  number n there is a prime p with n ≤ p (Euclid's theorem).
- **Statement:** `∀ n : Nat, ∃ p, n ≤ p ∧ Nat.Prime p`
- **Closure:** 345 constants, stated over **Mathlib's** `Nat.Prime`, which
  therefore enters the trusted set and this claim's freeze: if Mathlib's
  `Nat.Prime` ever meant something else, the attestation breaks even with the
  statement text unchanged. That is the point of freezing the closure with
  bodies.
- **Review:** quantifier order `∀ n, ∃ p` is right. `n ≤ p` rather than
  `n < p` is adequate for "arbitrarily large", since it holds for every n.
  Mathlib's `Nat.Prime` is the standard notion (irreducibility in `Nat`;
  2 ≤ p with no nontrivial divisors).
- **Verdict: faithful.**

### FERMAT-CLAIM — `Ampas.Claims.fermat_all_prime` (external validation)

- **Text:** FALSE CLAIM, kept as a control (Fermat, c. 1640): every Fermat
  number 2^(2^n)+1 is prime. Euler refuted it in 1732 with F5 = 641 × 6700417.
- **Statement:** `∀ n : Nat, Nat.Prime (2 ^ (2 ^ n) + 1)`
- **Review:** `2 ^ (2 ^ n) + 1` is F_n. The statement is a faithful rendering
  of Fermat's assertion, which is false at n = 5. Kept so that the pipeline is
  shown to reject proofs of a *historically real* false claim, not only ones
  invented for this suite.
- **Verdict: faithful as a control.**

### FERMAT-F5 — `Ampas.Claims.fermat_f5_not_prime` (external validation)

- **Text (tightened in this commit):** TRUE (Euler, 1732): the fifth Fermat
  number 2^(2^5)+1 is not prime. (It equals 4294967297 = 641 × 6700417; the
  factorization is the evidence, and the statement asserts only
  compositeness.)
- **Statement:** `¬ Nat.Prime (2 ^ (2 ^ 5) + 1)`
- **Why I changed the text.** It previously read as though the factorization
  were part of the claim. The statement asserts only `¬ Nat.Prime`; the
  factorization is how it is proved. Making that explicit stops the text from
  promising more than the statement delivers.
- **Arithmetic checked:** 2^32 + 1 = 4294967297, and 641 × 6700417 =
  4294967297. Both confirmed by the kernel (`rfl`) in the submission, and by
  hand.
- **Guard:** a refutation again, so nontriviality:
  `Ampas.Guards.fermat_nontrivial` proves `Nat.Prime (2^(2^3)+1)` — F3 = 257
  is prime, so `Nat.Prime` is not degenerate on Fermat numbers and Euler's
  result is specifically about F5. Same reviewer-chosen caveat as
  PL-AXIOM-IND. F4 = 65537 would be the sharper guard — the last case Fermat
  checked — but `decide` on it does not finish inside the kernel limits, since
  the decidability instance tries every divisor.
- **Source:** K. Conrad, *Fermat numbers and factors* (U. Connecticut);
  Euler, *Observationes de theoremate quodam Fermatiano*, Novi Commentarii
  1732/33.
- **Verdict: faithful.**

---

## Summary

| Claim | Guards | Verdict |
| --- | --- | --- |
| ADD | none needed | faithful |
| SUB | witness + necessity, OK | faithful |
| EVEN | witness + 2 necessity, OK | faithful |
| DVD | witness + 2 necessity, OK | faithful |
| GREATER | none needed | faithful |
| DIV | witness + necessity, OK | faithful |
| PL-IND | none needed | faithful |
| EL-IND | none needed | faithful |
| PL-AXIOM-IND | nontriviality (reviewer-chosen) | faithful, text tightened |
| PL-BOGUS | none needed | faithful **as a false-claim control** |
| PRIMES | none needed | faithful |
| FERMAT-CLAIM | none needed | faithful **as a false-claim control** |
| FERMAT-F5 | nontriviality (reviewer-chosen) | faithful, text tightened |

**13 of 13 judged faithful.** Two texts were tightened rather than approved as
written. Nothing was approved that I was not able to check: the one class of
judgement I cannot discharge mechanically is the *relevance* of the two
nontriviality guards, and that is flagged at both claims.

**What would change these verdicts:** a reader who reads `IsEven`, `Derives`,
`DerivesPos`, `monoid` or Mathlib's `Nat.Prime` and disagrees that they are
the intended notions. That is the whole substance of a fidelity review, and it
is why the definitions are listed here rather than summarized.

---

## 繁體中文摘要

13 條主張全部審過，判定**全部忠實**，但有三件事要講清楚：

1. **署名已經改對了。** 原本 11 份簽核紀錄寫 `attested_by: Kai Chang (Morris)`
   並聲稱你逐條確認了六項檢查——那是我準備的，你沒看過。現在拆成三個欄位：
   `prepared_by`（機器可重現的部分）、`reviewed_by`（我，含上面每條的推理）、
   `confirmed_by`（你，**mode: delegated**，並逐字記錄你的授權，明寫你沒有親自
   讀過）。`verify` 會分別檢查這三者。

2. **金鑰換掉了。** 原本 key_id 是 `kai-chang-morris-2026-10`，暗示在你保管中，
   但私鑰是我在這個 container 裡生的、沒有人保管。新的 id 是
   `ampas-harness-demo-2026-10`，並在 `reviewer_key.json` 寫明：它只證明紀錄
   未被篡改，**不歸屬任何人**。

3. **審查過程中抓到兩個問題，都已修。** 參考模組宣告了 12 條定理，但目錄只有
   10 條——兩條模態邏輯陳述從來沒被凍結、簽核、加 guard 或驗證過，而模組自己
   的檔頭說「每條定理都是目錄中某條主張」。另外 `Ampas.ML` 整個命名空間是受信任
   參考裡的死碼。兩者都移到 `reference/future/`，並加了一項 tier 0 測試確保目錄
   與模組不會再悄悄不一致。

兩條主張的 `text` 我改得更精確（PL-AXIOM-IND 講的是 p0,p1 的實例；FERMAT-F5
的因數分解是證據不是主張本身），沒有照原文批准。

唯一我無法用機器擔保的判斷，是兩條 **nontriviality guard 的「相關性」**——
guard 本身過核心檢查，但「要排除哪一種退化讀法」是人選的，兩處都標註了。
