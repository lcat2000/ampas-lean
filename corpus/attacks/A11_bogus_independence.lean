-- Positive control: the FALSE independence claim PL-BOGUS. No sound proof
-- exists (p1 -> p1 is derivable), so any "proof" must cheat. Here it uses
-- sorry; the pipeline must reject it (SORRY), never certify a false claim.
import AmpasRef.Defs
namespace Ampas.Claims
theorem pl_bogus_independent :
    Ampas.PL.Independent Ampas.PL.T_imp (Ampas.PL.Fm.imp (Ampas.PL.Fm.var 1) (Ampas.PL.Fm.var 1)) :=
  by sorry
end Ampas.Claims
