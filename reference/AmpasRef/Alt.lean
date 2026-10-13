/-
AMPAS: SECOND formalizations of claims already frozen in AmpasRef.Challenge.

Why a second rendering at all. Lean can decide whether a proof establishes a
statement. Nothing can decide whether the statement is the right one -- that
is the gap the whole repository is organised around, and the one the
counterexample and derivation searches explicitly do not touch. Triangulation
attacks it differently: render the same natural-language claim twice, then ask
the KERNEL whether the two renderings say the same thing. A divergence
localises a fidelity problem without anyone having to read both and judge.

What makes a rendering worth having here. A paraphrase that is definitionally
the same statement tests nothing: `b + a = a + b` against `a + b = b + a` is
the same proposition with the variables renamed, and proving them equivalent
is `Iff.rfl`. The informative pairs are the ones that reach the claim through
DIFFERENT machinery, so that an equivalence proof has to do real work:

  * EVEN -- "the sum of two even numbers is even". The frozen statement uses
    `Ampas.IsEven n := ∃ k, n = 2 * k`. This one uses `n % 2 = 0`. Those are
    different predicates built from different operations; that they agree is a
    theorem, not a definition.
  * DVD -- "divisibility is transitive". The frozen statement uses the `Dvd`
    class. This one spells the existentials out. Whether `a ∣ b` means what
    the claim's "divides" means is exactly the kind of question a reviewer is
    asked to take on trust, so making it a proof obligation is the point.

What this does NOT establish is in ASSUMPTIONS A1d. The short version: an
equivalence proof is kernel-checked whoever wrote the two statements, so the
machinery is sound -- but two renderings by the same author can share a
misreading of the claim, and then the proof only confirms that they share it.
Independence is what makes a successful equivalence worth something, and the
provenance of each pair is recorded in reference/triangulation.json rather
than assumed.
-/
import AmpasRef.Defs

namespace Ampas.Alt
open Ampas

/-- EVEN, rendered with remainders instead of an existential witness. -/
def IsEvenMod (n : Nat) : Prop := n % 2 = 0

/-- EVEN (second rendering): the sum of two even naturals is even, where
"even" is `n % 2 = 0`. -/
theorem even_add_even_mod : ∀ a b : Nat, IsEvenMod a → IsEvenMod b → IsEvenMod (a + b) :=
  fun _ _ ha hb => by
    simp only [IsEvenMod] at *
    omega

/-- DVD (second rendering): transitivity of divisibility, with the
existentials spelled out instead of the `Dvd` class. -/
theorem dvd_trans_explicit :
    ∀ a b c : Nat, (∃ k, b = a * k) → (∃ j, c = b * j) → (∃ i, c = a * i) :=
  fun _ _ _ ⟨k, hk⟩ ⟨j, hj⟩ => ⟨k * j, by rw [hj, hk, Nat.mul_assoc]⟩

/-- SUB (second rendering): the equality the other way round, and with the
hypothesis as `b ≤ a` spelled through `Nat.le`. Kept as a deliberately WEAK
case: it is the same proposition up to orientation, so its equivalence proof
is near-trivial and it is recorded as testing little. A triangulation suite
that contained only cases like this one would look like evidence and be
none. -/
theorem sub_add_cancel_flipped : ∀ a b : Nat, b ≤ a → a = a - b + b :=
  fun _ _ h => (Nat.sub_add_cancel h).symm

end Ampas.Alt
