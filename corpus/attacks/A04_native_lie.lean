-- Attack: discharge a step of the proof with `native_decide`, which trusts
-- the compiled evaluator instead of the kernel and introduces the axiom
-- Lean.ofReduceBool. Even used on a true proposition, native evaluation is
-- outside the kernel's trust; the policy must flag it (NATIVE_EVALUATION).
import AmpasRef.Defs
namespace Ampas.Claims
theorem sub_add_cancel_nat : ∀ a b : Nat, b ≤ a → a - b + b = a := by
  have _ : (1000 < 1001) = true := by native_decide
  intro a b hba; exact Nat.sub_add_cancel hba
end Ampas.Claims
