/-
A second attempt at Fermat's FALSE claim, with no `sorry` anywhere: the gap
is moved into an axiom instead ("assume the step holds in general"). This is
a common shape for a machine-written proof, and it reads as complete.

Expected verdict: REJECTED (axiom outside the policy).
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

/-- "The computation continues for every n." It does not: F5 is composite. -/
axiom fermat_step : ∀ n : Nat, 4 ≤ n → Nat.Prime (2 ^ (2 ^ n) + 1)

set_option maxRecDepth 10000 in
theorem fermat_all_prime : ∀ n : Nat, Nat.Prime (2 ^ (2 ^ n) + 1) := by
  intro n
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | (m + 4) => exact fermat_step (m + 4) (by omega)

end Ampas.Claims
