import AmpasRef.Defs

namespace Ampas.PL
open Fm

/-- Truth-table semantics. -/
def eval (v : Nat → Bool) : Fm → Bool
  | var i => v i
  | imp a b => !eval v a || eval v b
  | neg a => !eval v a

/-- Soundness of the Hilbert system: what T derives holds in every
valuation that satisfies T. -/
theorem sound {T : Fm → Prop} {v : Nat → Bool} (hT : ∀ ψ, T ψ → eval v ψ = true) :
    ∀ {φ : Fm}, Derives T φ → eval v φ = true := by
  intro φ h
  induction h with
  | hyp h => exact hT _ h
  | @a1 φ ψ => simp only [eval]; cases eval v φ <;> cases eval v ψ <;> rfl
  | @a2 φ ψ χ =>
    simp only [eval]; cases eval v φ <;> cases eval v ψ <;> cases eval v χ <;> rfl
  | @a3 φ ψ => simp only [eval]; cases eval v φ <;> cases eval v ψ <;> rfl
  | @mp φ ψ _ _ ih1 ih2 =>
    simp only [eval, ih2, Bool.not_true, Bool.false_or] at ih1
    exact ih1

end Ampas.PL

namespace Ampas.Claims
open Ampas.PL Ampas.PL.Fm

theorem pl_independent : PL.Independent PL.T_imp (PL.Fm.var 1) := by
  constructor
  · intro h
    have := sound (v := fun _ => false) (fun ψ (hψ : ψ = _) => by subst hψ; rfl) h
    exact absurd this (by decide)
  · intro h
    have := sound (v := fun _ => true) (fun ψ (hψ : ψ = _) => by subst hψ; rfl) h
    exact absurd this (by decide)

end Ampas.Claims
