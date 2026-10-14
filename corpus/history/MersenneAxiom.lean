/-
The same false entry with no `sorry`: the assertion is moved into an axiom
that reads like a citation. "Mersenne's list is correct" is exactly the shape
of a machine-written appeal to authority, and it reads as a complete proof.

Expected verdict: REJECTED (axiom outside the policy).
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

/-- "Every exponent on Mersenne's 1644 list gives a prime." It does not:
p = 67 and p = 257 are composite, and he omitted 61, 89 and 107. -/
axiom mersenne_list_correct : ∀ p : Nat, p = 67 → Nat.Prime (2 ^ p - 1)

theorem mersenne_67_prime : Nat.Prime (2 ^ 67 - 1) :=
  mersenne_list_correct 67 rfl

end Ampas.Claims
