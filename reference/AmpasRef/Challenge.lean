/-
AMPAS math-verification round 1: reference statements.

Each theorem below is the frozen Lean statement of one claim of
reference/claims.json; its proof here is `sorry` on purpose. A submission
must prove a theorem of the same name whose statement is this one (the
auditor compares the elaborated statements, not their text). Whether a
statement says what the claim's natural-language text says is a separate,
human-reviewed attestation (claims.json, "review").
-/
import AmpasRef.Defs

namespace Ampas.Claims
open Ampas

/-- ADD: addition of natural numbers is commutative. -/
theorem add_comm_nat : ∀ a b : Nat, a + b = b + a := sorry

/-- SUB: for natural numbers with b ≤ a, (a - b) + b = a. Lean's natural
number subtraction truncates at 0, so the hypothesis b ≤ a is required. -/
theorem sub_add_cancel_nat : ∀ a b : Nat, b ≤ a → a - b + b = a := sorry

/-- EVEN: the sum of two even natural numbers is even. -/
theorem even_add_even : ∀ a b : Nat, IsEven a → IsEven b → IsEven (a + b) := sorry

/-- DVD: divisibility of natural numbers is transitive. -/
theorem dvd_trans_nat : ∀ a b c : Nat, a ∣ b → b ∣ c → a ∣ c := sorry

/-- GREATER: every natural number has a strictly greater one. Constructive
axiom policy: no Classical.choice. -/
theorem exists_greater : ∀ n : Nat, ∃ m, n < m := sorry

/-- DIV: n / n = 1 for every positive natural number n. Lean defines
n / 0 = 0, so the hypothesis 0 < n is required. -/
theorem div_self_pos : ∀ n : Nat, 0 < n → n / n = 1 := sorry

/-- PL-IND: in classical propositional logic, the theory {p0 → p1} neither
proves nor refutes p1. -/
theorem pl_independent : PL.Independent PL.T_imp (PL.Fm.var 1) := sorry

/-- EL-IND: the monoid axioms do not derive commutativity, and adding it
leaves x = y underivable. -/
theorem el_comm_independent : EL.Independent EL.monoid EL.comm := sorry

/-- PL-AXIOM-IND: axiom independence. A3 is not derivable from A1 and A2 by
modus ponens alone, so A3 is an independent axiom of the Hilbert system -
not a consequence of the other two. This is a statement about the calculus
itself, not about a theory within it. -/
theorem pl_a3_independent : ¬ PL.DerivesPos PL.Empty PL.a3_instance := sorry

/-- PL-BOGUS: a false independence claim, kept as a reference that must
never be certified: p1 → p1 is derivable from any theory. -/
theorem pl_bogus_independent :
    PL.Independent PL.T_imp (PL.Fm.imp (PL.Fm.var 1) (PL.Fm.var 1)) := sorry

/-- ML-T-IND: the T axiom (□p → p) is independent of the modal system K:
K neither proves it nor refutes it. -/
theorem ml_T_independent_of_K :
    ML.Independent ML.K (ML.Fm.imp (ML.Fm.box (ML.Fm.var 0)) (ML.Fm.var 0)) := sorry

/-- ML-4-IND: the 4 axiom (□p → □□p) is independent of K together with the
T scheme, so transitivity is not forced by reflexivity. -/
theorem ml_4_independent_of_KT :
    ML.Independent ML.KT
      (ML.Fm.imp (ML.Fm.box (ML.Fm.var 0)) (ML.Fm.box (ML.Fm.box (ML.Fm.var 0)))) := sorry

end Ampas.Claims
