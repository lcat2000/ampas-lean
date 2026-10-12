-- Attack: prove GREATER (constructive policy, no Classical.choice) using
-- choice. The proof is sound, but the axiom policy forbids choice.
import AmpasRef.Defs
namespace Ampas.Claims
open Classical
theorem exists_greater : ∀ n : Nat, ∃ m, n < m := by
  intro n
  by_cases h : ∃ m, n < m
  · exact h
  · exact absurd ⟨n + 1, Nat.lt_succ_self n⟩ h
end Ampas.Claims
