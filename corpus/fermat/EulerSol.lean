/-
Euler, 1732: the fifth Fermat number is not prime.
F5 = 2^(2^5) + 1 = 4294967297 = 641 * 6700417.

Expected verdict: CERTIFIED.
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

theorem fermat_f5_not_prime : ¬ Nat.Prime (2 ^ (2 ^ 5) + 1) := by
  have h : (2 ^ (2 ^ 5) + 1 : Nat) = 641 * 6700417 := by rfl
  rw [h]
  exact Nat.not_prime_mul (by decide) (by decide)

end Ampas.Claims
