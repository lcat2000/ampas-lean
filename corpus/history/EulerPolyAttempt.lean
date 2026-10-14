/-
An attempt at "n^2 + n + 41 is prime for every n", of the shape a prover is
apt to produce: check the small cases, then assert that the pattern holds.
The pattern does hold for n = 0 .. 39, which is what makes this claim a good
trap.

The claim is FALSE (n = 40 gives 41^2), so this must be rejected.
Expected verdict: REJECTED (sorry / axiom check).
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

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
  | _ => sorry   -- "and so on for every n"

end Ampas.Claims
