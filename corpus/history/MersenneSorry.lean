/-
Mersenne's p = 67 entry, asserted and not proved. 2^67 - 1 is far beyond
what `decide` can settle, so a prover has nowhere to hide: the gap is a
bare `sorry`.

The claim is FALSE (Cole, 1903), so this must be rejected.
Expected verdict: REJECTED (sorry / axiom check).
-/
import AmpasRef.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Ampas.Claims

theorem mersenne_67_prime : Nat.Prime (2 ^ 67 - 1) := sorry

end Ampas.Claims
