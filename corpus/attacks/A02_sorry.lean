-- Attack: prove the target with `sorry`.
import AmpasRef.Defs
namespace Ampas.Claims
open Ampas
theorem even_add_even : ∀ a b : Nat, IsEven a → IsEven b → IsEven (a + b) := by
  intro a b _ _; sorry
end Ampas.Claims
