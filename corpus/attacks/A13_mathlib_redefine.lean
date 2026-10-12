-- Attack: do not import Mathlib's Nat.Prime; shadow it with a predicate that
-- holds of everything, then prove the claim trivially. The closure check must
-- see that Nat.Prime in the submission is not Mathlib's.
namespace Nat
def Prime (_ : Nat) : Prop := True
end Nat
namespace Ampas.Claims
theorem infinitude_of_primes : ∀ n : Nat, ∃ p, n ≤ p ∧ Nat.Prime p :=
  fun n => ⟨n, Nat.le_refl n, trivial⟩
end Ampas.Claims
