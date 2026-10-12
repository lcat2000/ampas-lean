import AmpasRef.Defs

namespace Ampas.Claims
open Ampas

theorem add_comm_nat : ∀ a b : Nat, a + b = b + a := Nat.add_comm

theorem sub_add_cancel_nat : ∀ a b : Nat, b ≤ a → a - b + b = a :=
  fun _ _ h => Nat.sub_add_cancel h

theorem even_add_even : ∀ a b : Nat, IsEven a → IsEven b → IsEven (a + b) := by
  rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
  exact ⟨i + j, (Nat.mul_add 2 i j).symm⟩

theorem dvd_trans_nat : ∀ a b c : Nat, a ∣ b → b ∣ c → a ∣ c :=
  fun _ _ _ hab hbc => Nat.dvd_trans hab hbc

theorem exists_greater : ∀ n : Nat, ∃ m, n < m := fun n => ⟨n + 1, Nat.lt_succ_self n⟩

theorem div_self_pos : ∀ n : Nat, 0 < n → n / n = 1 := fun _ h => Nat.div_self h

end Ampas.Claims
