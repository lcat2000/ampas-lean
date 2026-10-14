/-
Euler's polynomial n^2 + n + 41 fails at n = 40:

    40^2 + 40 + 41 = 1681 = 41 * 41

Expected verdict: CERTIFIED.
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

theorem euler_poly_40_not_prime : ¬ Nat.Prime (40 ^ 2 + 40 + 41) := by
  have h : (40 ^ 2 + 40 + 41 : Nat) = 41 * 41 := by rfl
  rw [h]
  exact Nat.not_prime_mul (by decide) (by decide)

end Ampas.Claims
