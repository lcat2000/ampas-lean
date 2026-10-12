-- Attack: add a false extra hypothesis so the body is vacuously provable.
-- The statement now has an extra binder: type differs from the reference.
import AmpasRef.Defs
namespace Ampas.Claims
theorem div_self_pos : ∀ n : Nat, 0 < n → n = n + 1 → n / n = 1 := by
  intro n _ hbad; omega
end Ampas.Claims
