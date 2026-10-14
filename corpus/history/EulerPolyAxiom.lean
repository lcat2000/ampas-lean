/-
The same false claim with no `sorry`: the general case is moved into an
axiom. Note how plausible the axiom's text is -- the polynomial really is
prime for the first forty values.

Expected verdict: REJECTED (axiom outside the policy).
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

/-- "Euler's polynomial keeps producing primes." It stops at n = 40. -/
axiom euler_poly_tail : ∀ n : Nat, 6 ≤ n → Nat.Prime (n ^ 2 + n + 41)

set_option maxRecDepth 10000 in
theorem euler_poly_all_prime : ∀ n : Nat, Nat.Prime (n ^ 2 + n + 41) := by
  intro n
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | (m + 6) => exact euler_poly_tail (m + 6) (by omega)

end Ampas.Claims
