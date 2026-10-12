-- Attack: prove a weaker statement under the target name (only a = a, i.e.
-- b fixed to a). Same name, different type: statement mismatch.
import AmpasRef.Defs
namespace Ampas.Claims
theorem add_comm_nat : ∀ a : Nat, a + a = a + a := fun _ => rfl
end Ampas.Claims
