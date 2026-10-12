/-
NOT part of the trusted reference, and not used by any claim.

This is scaffolding for a planned larger independence case (see ROADMAP.md):
the modal system K and K+T, where separating the systems needs Kripke frames
rather than a single valuation, and where the proof system has a rule
(necessitation) that is not a tautology-preserving rule of classical logic.

It was written during round 2 and never used. It sat in
reference/AmpasRef/Defs.lean -- inside the trusted reference -- until round
3's review, where it was found to be dead: no attested claim's closure
mentions any constant of it. Unused definitions inside the trusted reference
are a liability, because a reader has to establish for themselves that they
are inert, and their presence suggests a claim that does not exist. So it was
moved here, where it is compiled by nothing and trusted by nothing.

To use it, move the namespace back into AmpasRef/Defs.lean, add the claim to
reference/claims.json, write its guards, and re-freeze -- at which point it
becomes part of the trusted reference and needs review on its own terms.
-/

namespace Ampas

/-! ## Normal modal logic: the system K, and K together with a scheme

A larger independence case than the propositional and equational ones: the
proof system has a rule (necessitation) that is not a tautology-preserving
rule of classical logic, and separating the systems needs Kripke frames
rather than single valuations.
-/
namespace ML

/-- Modal formulas over propositional variables, with →, ¬ and □. -/
inductive Fm where
  | var : Nat → Fm
  | imp : Fm → Fm → Fm
  | neg : Fm → Fm
  | box : Fm → Fm
  deriving DecidableEq, Repr

open Fm

/-- `Derives T φ`: φ is derivable from the theory T in the normal modal
system K -- the classical propositional axioms A1-A3, the distribution
axiom K, modus ponens, and necessitation. T is read as a set of extra
axioms, so necessitation applies to anything derived from it. -/
inductive Derives (T : Fm → Prop) : Fm → Prop where
  | hyp {φ : Fm} : T φ → Derives T φ
  | a1 {φ ψ : Fm} : Derives T (imp φ (imp ψ φ))
  | a2 {φ ψ χ : Fm} : Derives T (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  | a3 {φ ψ : Fm} : Derives T (imp (imp (neg φ) (neg ψ)) (imp ψ φ))
  | k {φ ψ : Fm} : Derives T (imp (box (imp φ ψ)) (imp (box φ) (box ψ)))
  | mp {φ ψ : Fm} : Derives T (imp φ ψ) → Derives T φ → Derives T ψ
  | nec {φ : Fm} : Derives T φ → Derives T (box φ)

/-- T neither proves nor refutes φ. -/
def Independent (T : Fm → Prop) (φ : Fm) : Prop :=
  ¬ Derives T φ ∧ ¬ Derives T (neg φ)

/-- The empty theory: the system K itself. -/
def K : Fm → Prop := fun _ => False

/-- The reflexivity scheme □φ → φ, every instance of it. -/
def scheme_T : Fm → Prop := fun ψ => ∃ φ, ψ = imp (box φ) φ

/-- The system K together with the T scheme. -/
def KT : Fm → Prop := scheme_T

end ML


/-! ## The statements that were to use it

These two were declared in reference/AmpasRef/Challenge.lean -- the frozen
reference -- but appear in NO claim catalogue, so they were never frozen,
never attested, never guarded and never verified by anything. The module's
own header says every theorem in it is the frozen statement of a claim in
claims.json; that was false for these two. A submission could have declared
either name and the driver would simply have ignored it.

They are kept here as the statements a future modal independence case would
use. tests/test_math_verification.py now checks that the reference module and
the catalogue agree, so this cannot recur silently.
-/

namespace Claims
open Ampas

/-- ML-T-IND: the T axiom (□p → p) is independent of the modal system K:
K neither proves it nor refutes it. -/
theorem ml_T_independent_of_K :
    ML.Independent ML.K (ML.Fm.imp (ML.Fm.box (ML.Fm.var 0)) (ML.Fm.var 0)) := sorry

/-- ML-4-IND: the 4 axiom (□p → □□p) is independent of K together with the
T scheme, so transitivity is not forced by reflexivity. -/
theorem ml_4_independent_of_KT :
    ML.Independent ML.KT
      (ML.Fm.imp (ML.Fm.box (ML.Fm.var 0)) (ML.Fm.box (ML.Fm.box (ML.Fm.var 0)))) := sorry

end Claims

end Ampas
