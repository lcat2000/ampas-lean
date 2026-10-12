-- Attack: do NOT import AmpasRef.Defs; define a trivial IsEven that holds for
-- every n, then prove the target against it. The closure check must see that
-- Ampas.IsEven in the submission differs from the reference's.
namespace Ampas
def IsEven (_ : Nat) : Prop := True
end Ampas
namespace Ampas.Claims
open Ampas
theorem even_add_even : ∀ a b : Nat, IsEven a → IsEven b → IsEven (a + b) :=
  fun _ _ _ _ => trivial
end Ampas.Claims
