import AmpasRef.Defs
namespace Ampas.Claims
theorem div_self_pos : ∀ n : Nat, 1 ≤ n → n / n = 1 := fun _ h => Nat.div_self h
end Ampas.Claims
