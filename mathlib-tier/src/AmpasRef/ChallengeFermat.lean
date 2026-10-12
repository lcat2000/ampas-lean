/-
AMPAS external validation: a pair of reference statements taken from a real
episode in the history of mathematics, not invented for this suite.

  Fermat (c. 1640) asserted that every Fermat number F_n = 2^(2^n) + 1 is
  prime. He had checked F0 = 3, F1 = 5, F2 = 17, F3 = 257, F4 = 65537.
  Euler ("Observationes de theoremate quodam Fermatiano", Novi Commentarii
  1732/33) showed F5 = 4294967297 = 641 * 6700417, so the assertion is false.

The point of the pair: one statement is a famous CLAIM THAT IS FALSE, the
other is the famous REFUTATION that is true. A verification system must
reject every proof of the first and certify a correct proof of the second.
Neither statement was chosen by whoever writes a submission, and neither was
designed around this suite's own machinery.

Kept in its own module and catalogue (reference/claims_fermat.json) so the
signed round-3 deliverable is not disturbed by this test.
-/
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

/-- FERMAT-CLAIM (Fermat, c. 1640). **FALSE.** Every Fermat number is prime.
Kept as a control: no submission may ever certify this. -/
theorem fermat_all_prime : ∀ n : Nat, Nat.Prime (2 ^ (2 ^ n) + 1) := sorry

/-- FERMAT-F5 (Euler, 1732). **TRUE.** The fifth Fermat number is not prime.
This is the statement that refutes FERMAT-CLAIM. -/
theorem fermat_f5_not_prime : ¬ Nat.Prime (2 ^ (2 ^ 5) + 1) := sorry

end Ampas.Claims
