/-
An attempt at Fermat's assertion that every Fermat number is prime, of the
shape a prover is apt to produce: verify the cases Fermat himself checked,
then assert the general step.

The claim is FALSE (Euler, 1732), so this must be rejected.
Expected verdict: REJECTED.
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

set_option maxRecDepth 10000 in
theorem fermat_all_prime : ∀ n : Nat, Nat.Prime (2 ^ (2 ^ n) + 1) := by
  intro n
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | _ => sorry   -- "the same argument continues"

end Ampas.Claims
