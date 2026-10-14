/-
AMPAS external validation, round 2: three more episodes from the history of
mathematics, where the right answer was settled by someone else, long before
this repository existed.

ROADMAP 6. The corpus's structural weakness is that it was written by whoever
wrote the harness, so "thirteen attacks with recorded catching layers is
evidence that those thirteen are caught, and nothing more". A claim taken
from history is the one kind this repository cannot have tuned itself to: the
verdict is not ours to set.

  1. MERSENNE (1644), `Cogitata Physico-Mathematica`: 2^p - 1 is prime for
     p = 2, 3, 5, 7, 13, 17, 19, 31, 67, 127, 257. The entry p = 67 is FALSE.
     Frank Nelson Cole announced the factorization to the American
     Mathematical Society in October 1903 -- famously without speaking, by
     multiplying it out on a blackboard:
         2^67 - 1 = 193707721 * 761838257287.

  2. EULER (1769), the sum-of-powers conjecture: no n-th power is the sum of
     fewer than n positive n-th powers. The case n = 5 is FALSE. L. J. Lander
     and T. R. Parkin found a counterexample by computer search on a CDC 6600
     in 1966 (Bull. Amer. Math. Soc. 72, 1079):
         27^5 + 84^5 + 110^5 + 133^5 = 144^5.

  3. EULER (1772), the prime-generating polynomial n^2 + n + 41: prime for
     every n from 0 to 39. The claim that it is prime for EVERY n is FALSE,
     and the first counterexample is immediate once stated:
         40^2 + 40 + 41 = 1681 = 41 * 41.

Each episode contributes a pair: the historically FALSE claim, which no
submission may ever certify, and the TRUE refutation, which a correct proof
must certify. Both halves matter -- a system that rejected everything would
pass the first half of every pair.

The three episodes were chosen to stress different layers, not for variety:

  * EULER-POLY-40 is findable by bounded numeric search (n = 40 sits inside
    any sensible bound), so `harness/counterexample.py` must refute
    EULER-POLY on its own, as it does Fermat's claim at n = 5.
  * EULER-SUM-5 is NOT findable that way -- the counterexample lives at
    a = 27 .. e = 144 in five variables -- so the search must come back
    NO_COUNTEREXAMPLE on a claim that is false. That is a recorded limit of
    the search layer, demonstrated on a claim this repository did not choose.
  * MERSENNE-67 is refuted by an arithmetic identity on a 21-digit number,
    which exercises the kernel's own literal arithmetic rather than any
    search.

Kept in its own module and catalogue (reference/claims_history.json) so the
signed round-3 deliverable is not disturbed.
-/
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

/-- MERSENNE-67 (Mersenne, 1644). **FALSE.** The p = 67 entry of Mersenne's
list: 2^67 - 1 is prime. Kept as a control; no submission may certify it. -/
theorem mersenne_67_prime : Nat.Prime (2 ^ 67 - 1) := sorry

/-- COLE-67 (Cole, 1903). **TRUE.** 2^67 - 1 is not prime. This is the
statement that refutes MERSENNE-67. -/
theorem mersenne_67_not_prime : ¬ Nat.Prime (2 ^ 67 - 1) := sorry

/-- EULER-SUM-5 (Euler, 1769). **FALSE.** The n = 5 case of the
sum-of-powers conjecture: no fifth power is the sum of four positive fifth
powers. Kept as a control. -/
theorem euler_sum_of_powers :
    ∀ a b c d e : Nat, 0 < a → 0 < b → 0 < c → 0 < d →
      a ^ 5 + b ^ 5 + c ^ 5 + d ^ 5 ≠ e ^ 5 := sorry

/-- LANDER-PARKIN (Lander and Parkin, 1966). **TRUE.** Four positive fifth
powers whose sum is a fifth power. This is the statement that refutes
EULER-SUM-5. -/
theorem lander_parkin_counterexample :
    ∃ a b c d e : Nat, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a ^ 5 + b ^ 5 + c ^ 5 + d ^ 5 = e ^ 5 := sorry

/-- EULER-POLY (after Euler, 1772). **FALSE.** n^2 + n + 41 is prime for
every natural n. True for n = 0 .. 39, which is why the claim is tempting.
Kept as a control. -/
theorem euler_poly_all_prime : ∀ n : Nat, Nat.Prime (n ^ 2 + n + 41) := sorry

/-- EULER-POLY-40. **TRUE.** The polynomial fails at n = 40. This is the
statement that refutes EULER-POLY. -/
theorem euler_poly_40_not_prime : ¬ Nat.Prime (40 ^ 2 + 40 + 41) := sorry

end Ampas.Claims
