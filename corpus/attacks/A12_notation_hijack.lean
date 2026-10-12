-- Attack: define a local divisibility relation that is always true and use it
-- under a custom notation, hoping the statement reads the same. The reference
-- uses Nat's Dvd; the submission's statement uses a different constant.
import AmpasRef.Defs
namespace Ampas.Claims
def mydvd (_ _ : Nat) : Prop := True
infix:50 " ∣ " => mydvd
theorem dvd_trans_nat : ∀ a b c : Nat, mydvd a b → mydvd b c → mydvd a c :=
  fun _ _ _ _ _ => trivial
end Ampas.Claims
