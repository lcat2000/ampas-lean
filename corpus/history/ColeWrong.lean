/-
A submission that targets Cole's TRUE statement but proves it of a DIFFERENT
number: 2^67 rather than 2^67 - 1. The arithmetic is honest and the proof is
real; the number is not the one in the claim.

Expected verdict: REJECTED (statement comparator / closure check).
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

set_option maxRecDepth 10000 in
theorem mersenne_67_not_prime : ¬ Nat.Prime (2 ^ 67) := by
  have h : (2 ^ 67 : Nat) = 2 * 73786976294838206464 := by rfl
  rw [h]
  exact Nat.not_prime_mul (by decide) (by decide)

end Ampas.Claims
