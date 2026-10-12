/-
AMPAS math-verification: review guards.

Part of the trusted reference, not of any submission. For every reference
statement with hypotheses, these theorems discharge the two mechanical
guards the review process requires (see reference/REVIEW.md):

  * non-vacuity: the hypotheses can all hold at once, so the statement is
    not vacuously true and does not quietly say nothing;
  * necessity: dropping any single hypothesis makes the statement FALSE, so
    no hypothesis was added to weaken the claim past what the
    natural-language text says.

The auditor (mode "sanity") computes the type each guard must have from the
reference statement itself and checks these against it by the kernel's
definitional equality, so a guard cannot be a proof of something weaker.
These are kernel-checked like any other theorem; a human attestation that
cites them is backed by machine-checked facts rather than by opinion alone.
-/
import AmpasRef.Challenge

namespace Ampas.Guards
open Ampas

/-! ### SUB: ∀ a b, b ≤ a → a - b + b = a -/

theorem sub_witness : ∃ a b : Nat, b ≤ a := ⟨0, 0, Nat.le_refl 0⟩

/-- Without `b ≤ a` the claim is false: Nat subtraction truncates, so
`0 - 1 + 1 = 1 ≠ 0`. This is the Lean-convention trap SUB guards against. -/
theorem sub_necessity : ¬∀ (a b : Nat), a - b + b = a := by
  intro h; have := h 0 1; omega

/-! ### DIV: ∀ n, 0 < n → n / n = 1 -/

theorem div_witness : ∃ n : Nat, 0 < n := ⟨1, Nat.zero_lt_one⟩

/-- Without `0 < n` the claim is false: Lean defines `0 / 0 = 0 ≠ 1`. -/
theorem div_necessity : ¬∀ (n : Nat), n / n = 1 := by
  intro h; have := h 0; simp at this

/-! ### EVEN: ∀ a b, IsEven a → IsEven b → IsEven (a + b) -/

theorem even_witness : ∃ a b : Nat, IsEven a ∧ IsEven b :=
  ⟨0, 0, ⟨0, rfl⟩, ⟨0, rfl⟩⟩

private theorem not_even_one : ¬ IsEven 1 := by
  rintro ⟨k, hk⟩; omega

/-- Dropping `IsEven a` makes it false: `a = 1`, `b = 0`. -/
theorem even_necessity_1 : ¬∀ (a b : Nat), IsEven b → IsEven (a + b) := by
  intro h; exact not_even_one (h 1 0 ⟨0, rfl⟩)

/-- Dropping `IsEven b` makes it false: `a = 0`, `b = 1`. -/
theorem even_necessity_2 : ¬∀ (a b : Nat), IsEven a → IsEven (a + b) := by
  intro h; exact not_even_one (h 0 1 ⟨0, rfl⟩)

/-! ### DVD: ∀ a b c, a ∣ b → b ∣ c → a ∣ c -/

theorem dvd_witness : ∃ a b c : Nat, a ∣ b ∧ b ∣ c :=
  ⟨1, 1, 1, ⟨1, rfl⟩, ⟨1, rfl⟩⟩

private theorem not_two_dvd_one : ¬ (2 ∣ 1) := by
  rintro ⟨c, hc⟩; omega

/-- Dropping `a ∣ b` makes it false: `a = 2`, `b = c = 1`. -/
theorem dvd_necessity_1 : ¬∀ (a b c : Nat), b ∣ c → a ∣ c := by
  intro h; exact not_two_dvd_one (h 2 1 1 ⟨1, rfl⟩)

/-- Dropping `b ∣ c` makes it false: `a = b = 2`, `c = 1`. -/
theorem dvd_necessity_2 : ¬∀ (a b c : Nat), a ∣ b → a ∣ c := by
  intro h; exact not_two_dvd_one (h 2 2 1 ⟨1, rfl⟩)

/-! ### PL-AXIOM-IND: ¬ DerivesPos Empty a3_instance

A refutation claim: its conclusion is `False`, so the non-vacuity and
necessity guards do not apply (see `isRefutation` in harness/Audit.lean).
The degenerate way to make an independence claim true is for the calculus to
prove nothing at all, so the guard here is NONTRIVIALITY: the positive
fragment, without A3, still derives theorems. Unlike the witness and
necessity guards, this one's statement is chosen by the reviewer rather than
computed from the claim, so it is kernel-checked but its relevance is a
reviewer judgement. -/

/-- `p0 → p0` is derivable from A1 and A2 alone, so DerivesPos is not the
empty calculus: A3's underivability is not an artefact of a broken system. -/
theorem pos_nontrivial :
    PL.DerivesPos PL.Empty (PL.Fm.imp (PL.Fm.var 0) (PL.Fm.var 0)) := by
  have a2 := PL.DerivesPos.a2 (T := PL.Empty) (φ := PL.Fm.var 0)
    (ψ := PL.Fm.imp (PL.Fm.var 0) (PL.Fm.var 0)) (χ := PL.Fm.var 0)
  have a1 := PL.DerivesPos.a1 (T := PL.Empty) (φ := PL.Fm.var 0)
    (ψ := PL.Fm.imp (PL.Fm.var 0) (PL.Fm.var 0))
  have a1' := PL.DerivesPos.a1 (T := PL.Empty) (φ := PL.Fm.var 0) (ψ := PL.Fm.var 0)
  exact PL.DerivesPos.mp (PL.DerivesPos.mp a2 a1) a1'

end Ampas.Guards
