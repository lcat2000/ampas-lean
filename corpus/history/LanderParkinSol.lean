/-
Lander and Parkin, 1966: four positive fifth powers summing to a fifth
power, found by direct search on a CDC 6600.

    27^5 + 84^5 + 110^5 + 133^5 = 61917364224 = 144^5

Expected verdict: CERTIFIED.
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

theorem lander_parkin_counterexample :
    ∃ a b c d e : Nat, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a ^ 5 + b ^ 5 + c ^ 5 + d ^ 5 = e ^ 5 :=
  ⟨27, 84, 110, 133, 144, by decide, by decide, by decide, by decide, by rfl⟩

end Ampas.Claims
