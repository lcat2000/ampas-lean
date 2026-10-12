/-
A submission that targets Euler's TRUE statement but proves something else:
it shows F5 is not prime by exhibiting a factor of a DIFFERENT number
(2^32 instead of 2^32 + 1), then states the reference claim.

Expected verdict: REJECTED (the statement comparator / closure check).
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

theorem fermat_f5_not_prime : ¬ Nat.Prime (2 ^ (2 ^ 5)) := by
  have h : (2 ^ (2 ^ 5) : Nat) = 2 * 2147483648 := by rfl
  rw [h]
  exact Nat.not_prime_mul (by decide) (by decide)

end Ampas.Claims
