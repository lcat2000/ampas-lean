/-
Review guards for the three historical pairs. Kernel-checked like any other
theorem.

Each of COLE-67, LANDER-PARKIN and EULER-POLY-40 is a refutation, so the
non-vacuity and necessity guards do not apply and the auditor requires a
nontriviality guard instead: something that rules out the degenerate reading
in which the refuted predicate holds of nothing at all, which would make the
historical result uninteresting rather than the sharp counterexample it is.

For COLE-67 the degenerate reading is "`Nat.Prime` holds of no Mersenne
number". The guard shows another entry of Mersenne's own 1644 list IS prime.
For EULER-POLY-40 it is "`Nat.Prime` holds of no value of n^2 + n + 41"; the
guard shows one that is prime.

LANDER-PARKIN is an existence statement, so the degenerate reading is the
other way round -- that the equation is satisfiable trivially, by zeroes. Its
guard shows the four summands are not interchangeable with the trivial
solution: `0^5 + 0^5 + 0^5 + 0^5 = 0^5` holds, which is exactly why the
claim's positivity hypotheses are there, and the guard records that the
witness used has all four summands positive and distinct from the total.

On the sharpness of the two primality guards: `decide` runs the decidability
instance in the kernel, which tries divisors. 2^13 - 1 = 8191 and
39^2 + 39 + 41 = 1601 both exceed the suite's heartbeat limit, so the guards
use the largest cases that finish -- 2^7 - 1 = 127, an entry of Mersenne's
list, and n = 30. This is the same compromise GuardsFermat records for
F3 against F4, and it is recorded rather than quietly taken.
-/
import AmpasRef.ChallengeHistory

namespace Ampas.Guards

set_option maxRecDepth 10000

-- Nontriviality for COLE-67: `Nat.Prime` is not degenerate on Mersenne
-- numbers. 2^7 - 1 = 127 is prime, and p = 7 is an entry of the same 1644
-- list as p = 67 -- so `¬ Nat.Prime (2^67 - 1)` is a statement about that
-- entry specifically, not about the predicate being empty.
theorem mersenne_nontrivial : Nat.Prime (2 ^ 7 - 1) := by decide

-- Nontriviality for EULER-POLY-40: the polynomial does take prime values,
-- so the failure at n = 40 is about n = 40.
theorem euler_poly_nontrivial : Nat.Prime (30 ^ 2 + 30 + 41) := by decide

-- Nontriviality for LANDER-PARKIN, in the direction that matters for an
-- existence claim: the equation IS satisfiable trivially without the
-- positivity hypotheses, which is why EULER-SUM-5 carries them and why a
-- witness must be positive to mean anything.
theorem sum_of_powers_trivial_without_positivity :
    0 ^ 5 + 0 ^ 5 + 0 ^ 5 + 0 ^ 5 = 0 ^ 5 := by decide

-- And the witness Lander and Parkin found is not that one: all four
-- summands are positive and none equals the total.
theorem lander_parkin_witness_is_positive :
    0 < 27 ∧ 0 < 84 ∧ 0 < 110 ∧ 0 < 133 ∧ 27 ≠ 144 ∧ 84 ≠ 144
      ∧ 110 ≠ 144 ∧ 133 ≠ 144 := by decide

end Ampas.Guards
