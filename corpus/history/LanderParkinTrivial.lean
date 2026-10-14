/-
A submission that targets Lander and Parkin's TRUE statement but drops the
positivity hypotheses, and then satisfies the equation with zeroes.

`Ampas.Guards.sum_of_powers_trivial_without_positivity` exists precisely to
record that this reading is available, so the guard anticipates the attack
rather than the attack revealing the guard.

Expected verdict: REJECTED (statement comparator).
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

theorem lander_parkin_counterexample :
    ∃ a b c d e : Nat, a ^ 5 + b ^ 5 + c ^ 5 + d ^ 5 = e ^ 5 :=
  ⟨0, 0, 0, 0, 0, by decide⟩

end Ampas.Claims
