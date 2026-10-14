/-
Cole, 1903: 2^67 - 1 is not prime, by the factorization he multiplied out on
a blackboard at the American Mathematical Society.

    2^67 - 1 = 147573952589676412927 = 193707721 * 761838257287

Expected verdict: CERTIFIED.
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

set_option maxRecDepth 10000 in
theorem mersenne_67_not_prime : ¬ Nat.Prime (2 ^ 67 - 1) := by
  have h : (2 ^ 67 - 1 : Nat) = 193707721 * 761838257287 := by rfl
  rw [h]
  exact Nat.not_prime_mul (by decide) (by decide)

end Ampas.Claims
