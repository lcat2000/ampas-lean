import Mathlib.Data.Nat.Prime.Infinite

namespace Ampas.Claims

theorem infinitude_of_primes : ∀ n : Nat, ∃ p, n ≤ p ∧ Nat.Prime p :=
  Nat.exists_infinite_primes

end Ampas.Claims
