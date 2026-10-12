/-
AMPAS math-verification: reference statements that rest on Mathlib.

Kept apart from AmpasRef.Challenge on purpose: the core claims must not
acquire a dependency on Mathlib. A claim here is stated over Mathlib's own
definitions (here `Nat.Prime`), so Mathlib's definitions enter the trusted
set and the freeze: if Mathlib's `Nat.Prime` ever meant something else, the
attestation for this claim breaks even though the statement text is
unchanged.

Mathlib is pinned by commit (reference/mathlib_pin.json), built from source
with the same toolchain, and its oleans are hashed into the environment
record. Nothing here is taken from a prebuilt cache.
-/
import Mathlib.Data.Nat.Prime.Infinite

namespace Ampas.Claims

/-- PRIMES: there are arbitrarily large primes (Euclid). Stated with
Mathlib's `Nat.Prime`. -/
theorem infinitude_of_primes : ∀ n : Nat, ∃ p, n ≤ p ∧ Nat.Prime p := sorry

end Ampas.Claims
