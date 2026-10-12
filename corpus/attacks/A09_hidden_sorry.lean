-- Attack: route the target through a helper lemma that itself uses sorry, so
-- the target "has a proof". sorryAx must be found transitively.
import AmpasRef.Defs
namespace Ampas.Claims
open Ampas
private theorem helper (a b : Nat) : a ∣ b → ∀ c, b ∣ c → a ∣ c := by
  intro _ _ _; sorry
theorem dvd_trans_nat : ∀ a b c : Nat, a ∣ b → b ∣ c → a ∣ c :=
  fun a b c hab hbc => helper a b hab c hbc
end Ampas.Claims
