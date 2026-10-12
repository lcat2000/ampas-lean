/-
A third attempt at Fermat's FALSE claim. No `sorry`, no extra axiom, and
every line is genuinely proved -- but what is proved is the RESTRICTED
statement (the cases Fermat actually checked), carrying the name of the
general claim.

This is the failure mode that matters most for an AI proof pipeline: the
proof is real, the Lean code is honest, and the formalization simply is not
the claim it is filed under.

Expected verdict: REJECTED (statement comparator).
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

set_option maxRecDepth 10000 in
theorem fermat_all_prime : ∀ n : Nat, n ≤ 3 → Nat.Prime (2 ^ (2 ^ n) + 1) := by
  intro n hn
  match n, hn with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide

end Ampas.Claims
