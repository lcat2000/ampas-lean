/-
AMPAS: equivalence of the two formalizations of each claim.

Each theorem here says that a frozen statement of AmpasRef.Challenge and the
second rendering in AmpasRef.Alt are the SAME proposition. That is the whole
content of triangulation: if two renderings of one natural-language claim are
provably equivalent, a reviewer who checks either one has checked both; if
they are not, there is a fidelity problem and the pair localises it without
anyone reading both and forming a judgement.

Two things to be precise about, because the value of this file rests on them:

  * **An `Iff` between the wrong two things proves nothing.**
    `harness/CheckTriangulation.lean` resolves both sides from the
    environment BY NAME and checks the theorem's type is `Iff` applied to
    exactly those two statements. Without that, an equivalence between two
    other propositions would pass -- the `FermatWeaker` failure mode, pointed
    at equivalences instead of proofs.
  * **A near-trivial equivalence is not evidence.** SUB's pair differs only
    in the orientation of an equality, so its proof is almost `Iff.rfl`, and
    reference/triangulation.json records it as testing little. The pairs worth
    having are the ones where the two renderings reach the claim through
    different machinery, so that the kernel has to do real work to reconcile
    them -- EVEN (an existential witness against a remainder) and DVD (the
    `Dvd` class against explicit existentials).
-/
import AmpasRef.Challenge
import AmpasRef.Alt

namespace Ampas.Triangulation
open Ampas

/-- The bridge EVEN's equivalence rests on: being `2 * k` for some `k` and
having remainder 0 on division by 2 are the same property of a natural
number. Different operations, so this is a theorem rather than unfolding. -/
theorem isEven_iff_mod (n : Nat) : IsEven n ↔ Ampas.Alt.IsEvenMod n := by
  constructor
  · intro ⟨k, hk⟩
    simp only [Alt.IsEvenMod, hk]
    omega
  · intro h
    simp only [Alt.IsEvenMod] at h
    exact ⟨n / 2, by omega⟩

/-- EVEN: the two renderings of "the sum of two even naturals is even" are
the same statement. -/
theorem even_equiv :
    (∀ a b : Nat, IsEven a → IsEven b → IsEven (a + b))
      ↔ (∀ a b : Nat, Alt.IsEvenMod a → Alt.IsEvenMod b → Alt.IsEvenMod (a + b)) := by
  constructor
  · intro h a b ha hb
    exact (isEven_iff_mod _).mp (h a b ((isEven_iff_mod a).mpr ha) ((isEven_iff_mod b).mpr hb))
  · intro h a b ha hb
    exact (isEven_iff_mod _).mpr (h a b ((isEven_iff_mod a).mp ha) ((isEven_iff_mod b).mp hb))

/-- DVD: transitivity stated with the `Dvd` class and stated with explicit
existentials are the same statement. The bridge is that `a ∣ b` unfolds to
`∃ c, b = a * c`, which is a fact about the instance and not a definition
anyone restated. -/
theorem dvd_equiv :
    (∀ a b c : Nat, a ∣ b → b ∣ c → a ∣ c)
      ↔ (∀ a b c : Nat, (∃ k, b = a * k) → (∃ j, c = b * j) → (∃ i, c = a * i)) := by
  constructor
  · intro h a b c hab hbc
    exact h a b c hab hbc
  · intro h a b c hab hbc
    exact h a b c hab hbc

/-- SUB: the same equality written the other way round. Deliberately weak,
and recorded as such -- it is here so the suite contains a case whose
equivalence proof does nothing, as a reminder that the shape of this file is
not itself evidence. -/
theorem sub_equiv :
    (∀ a b : Nat, b ≤ a → a - b + b = a) ↔ (∀ a b : Nat, b ≤ a → a = a - b + b) := by
  constructor
  · intro h a b hb; exact (h a b hb).symm
  · intro h a b hb; exact (h a b hb).symm

/-! ## The limit of the method, proved rather than asserted

ROADMAP 5.2 called triangulation "the most promising idea here". The
theorems below are why that assessment was wrong, and they are stated as
theorems so the limit is kernel-checked rather than a caveat a reader has to
take on trust.

Equivalence of PROPOSITIONS is vacuous between two provable statements. Any
two theorems are equivalent, whatever they say. So triangulation can only
detect a second rendering that differs from the first in TRUTH VALUE -- not
one that is a different true statement. The pair below makes that concrete:
"the sum of two even numbers is even" and "the PRODUCT of two even numbers is
even" are plainly different claims, and `indistinguishable` proves them
equivalent in two applications.

What this leaves triangulation good for: catching a rendering whose error
makes it false -- `FermatWeaker`'s restriction to `n ≤ 3` is detectable
precisely because the general claim is FALSE and the restriction is true.
That overlaps heavily with what the counterexample search already does, and
it is much less than "two independent formalizations agreeing means the
formalization is faithful", which is what the idea sounded like.
-/

/-- The product of two even naturals is even. A different claim from EVEN,
and also true. -/
theorem prod_is_even : ∀ a b : Nat, IsEven a → IsEven b → IsEven (a * b) :=
  fun _ _ ⟨i, hi⟩ ⟨j, hj⟩ => ⟨2 * i * j, by
    subst hi; subst hj
    simp [Nat.mul_left_comm, Nat.mul_comm]⟩

/-- The sum of two even naturals is even: EVEN's own content, proved here so
the equivalence below needs nothing from outside this file. -/
theorem sum_is_even : ∀ a b : Nat, IsEven a → IsEven b → IsEven (a + b) :=
  fun _ _ ⟨i, hi⟩ ⟨j, hj⟩ => ⟨i + j, by omega⟩

/-- **The method's limit.** Two different claims, both true, therefore
provably equivalent. A triangulation check that compares renderings as
propositions cannot tell them apart, so agreement between two renderings is
not evidence that either one says what the claim says. -/
theorem indistinguishable :
    (∀ a b : Nat, IsEven a → IsEven b → IsEven (a + b))
      ↔ (∀ a b : Nat, IsEven a → IsEven b → IsEven (a * b)) :=
  ⟨fun _ => prod_is_even, fun _ => sum_is_even⟩

end Ampas.Triangulation
