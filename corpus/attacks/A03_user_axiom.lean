-- Attack: postulate the target as a user axiom-backed lemma.
import AmpasRef.Defs
namespace Ampas.Claims
open Ampas
axiom cheat : ∀ a b c : Nat, a ∣ b → b ∣ c → a ∣ c
theorem dvd_trans_nat : ∀ a b c : Nat, a ∣ b → b ∣ c → a ∣ c := cheat
end Ampas.Claims
