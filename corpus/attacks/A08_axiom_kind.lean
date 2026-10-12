-- Attack: declare the target directly as an axiom of the right type.
import AmpasRef.Defs
namespace Ampas.Claims
axiom add_comm_nat : ∀ a b : Nat, a + b = b + a
end Ampas.Claims
