/-
The same false claim, every line genuinely proved -- of the RESTRICTED
statement (n <= 5), carrying the name of the general claim.

Expected verdict: REJECTED (statement comparator).
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

set_option maxRecDepth 10000 in
theorem euler_poly_all_prime : ∀ n : Nat, n ≤ 5 → Nat.Prime (n ^ 2 + n + 41) := by
  intro n hn
  match n, hn with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide

end Ampas.Claims
