/-
Independence of the axiom A3 from A1 and A2.

Method (a standard axiom-independence argument): give a semantics in which
A1, A2 and modus ponens are all sound, but A3 is not valid. Here negation is
interpreted as the IDENTITY rather than as complement. A1 and A2 never
mention negation, so they stay tautologies of the implicational fragment and
modus ponens still preserves truth; so everything DerivesPos proves is valid
in this semantics. But under this reading A3's instance
(¬p0 → ¬p1) → (p1 → p0) becomes (p0 → p1) → (p1 → p0), which is false at
p0 = false, p1 = true. Hence A3 is not derivable from A1 and A2.

This is a claim about the calculus, not about a theory inside it: it says the
third axiom carries content the other two do not.
-/
import AmpasRef.Defs

namespace Ampas.PL
open Fm

/-- Truth values with negation read as the identity. A1 and A2 do not
mention `neg`, so they are unaffected; A3 is exactly what this breaks. -/
def evalId (v : Nat → Bool) : Fm → Bool
  | var i => v i
  | imp a b => !evalId v a || evalId v b
  | neg a => evalId v a          -- negation as identity: the separating choice

/-- Soundness of the positive fragment for this semantics. -/
theorem soundPos {T : Fm → Prop} {v : Nat → Bool}
    (hT : ∀ ψ, T ψ → evalId v ψ = true) :
    ∀ {φ : Fm}, DerivesPos T φ → evalId v φ = true := by
  intro φ h
  induction h with
  | hyp h => exact hT _ h
  | @a1 φ ψ => simp only [evalId]; cases evalId v φ <;> cases evalId v ψ <;> rfl
  | @a2 φ ψ χ =>
    simp only [evalId]; cases evalId v φ <;> cases evalId v ψ <;> cases evalId v χ <;> rfl
  | @mp φ ψ _ _ ih1 ih2 =>
    simp only [evalId, ih2, Bool.not_true, Bool.false_or] at ih1
    exact ih1

end Ampas.PL

namespace Ampas.Claims
open Ampas.PL

theorem pl_a3_independent : ¬ PL.DerivesPos PL.Empty PL.a3_instance := by
  intro h
  -- the empty theory has no hypotheses to satisfy, vacuously
  have hv := soundPos (T := PL.Empty) (v := fun i => i == 1)
    (fun _ hψ => absurd hψ (by intro c; exact c)) h
  -- at p0 = false, p1 = true the A3 instance evaluates to false
  simp [PL.a3_instance, PL.evalId] at hv

end Ampas.Claims
