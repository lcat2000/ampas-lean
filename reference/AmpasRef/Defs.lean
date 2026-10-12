/-
AMPAS math-verification round 1: trusted reference definitions.

Every reference statement (AmpasRef.Challenge) is stated over Lean 4 core
(Init) and the definitions in this file only. A submission must import this
module and may not redefine anything in it; the auditor checks that every
constant a reference statement mentions means the same in the submission's
environment as in the reference's (closure check).

The two deep embeddings below make "independence" a statement Lean can
check: a theory T does not decide a formula φ when neither φ nor its
refutation is derivable from T in the stated proof system. The proof system
is part of the trusted reference, so an "independence proof" for a weaker
system written by a submission is a different statement and is not accepted.
-/

namespace Ampas

/-- n is even: n = 2k for some natural number k. -/
def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k

/-! ## Classical propositional logic: a Hilbert system (Łukasiewicz axioms) -/
namespace PL

/-- Formulas over propositional variables `var i`, with → and ¬. -/
inductive Fm where
  | var : Nat → Fm
  | imp : Fm → Fm → Fm
  | neg : Fm → Fm
  deriving DecidableEq, Repr

open Fm

/-- `Derives T φ`: φ is derivable from the hypotheses T (a set of formulas,
given as a predicate) with axiom schemes A1-A3 and modus ponens. -/
inductive Derives (T : Fm → Prop) : Fm → Prop where
  | hyp {φ : Fm} : T φ → Derives T φ
  | a1 {φ ψ : Fm} : Derives T (imp φ (imp ψ φ))
  | a2 {φ ψ χ : Fm} : Derives T (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  | a3 {φ ψ : Fm} : Derives T (imp (imp (neg φ) (neg ψ)) (imp ψ φ))
  | mp {φ ψ : Fm} : Derives T (imp φ ψ) → Derives T φ → Derives T ψ

/-- T neither proves nor refutes φ. -/
def Independent (T : Fm → Prop) (φ : Fm) : Prop :=
  ¬ Derives T φ ∧ ¬ Derives T (neg φ)

/-- The theory {p0 → p1}. -/
def T_imp : Fm → Prop := fun φ => φ = imp (var 0) (var 1)

/-- The positive fragment of the same Hilbert system: A1, A2 and modus
ponens, WITHOUT A3. A3 is what makes the system classical, so this is a
strictly weaker calculus over the same language. -/
inductive DerivesPos (T : Fm → Prop) : Fm → Prop where
  | hyp {φ : Fm} : T φ → DerivesPos T φ
  | a1 {φ ψ : Fm} : DerivesPos T (imp φ (imp ψ φ))
  | a2 {φ ψ χ : Fm} : DerivesPos T (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  | mp {φ ψ : Fm} : DerivesPos T (imp φ ψ) → DerivesPos T φ → DerivesPos T ψ

/-- The empty theory: no hypotheses, so what is derivable is exactly what the
axioms and modus ponens give. -/
def Empty : Fm → Prop := fun _ => False

/-- The A3 instance for p0 and p1: (¬p0 → ¬p1) → (p1 → p0). -/
def a3_instance : Fm := imp (imp (neg (var 0)) (neg (var 1))) (imp (var 1) (var 0))

end PL

/-! ## Equational logic over one binary operation and a constant -/
namespace EL

/-- Terms: variables, the constant `one`, and `mul`. -/
inductive Term where
  | var : Nat → Term
  | one : Term
  | mul : Term → Term → Term
  deriving DecidableEq, Repr

open Term

/-- Simultaneous substitution of terms for variables. -/
def Term.subst (σ : Nat → Term) : Term → Term
  | var i => σ i
  | one => one
  | mul s t => mul (s.subst σ) (t.subst σ)

/-- An equation l = r. -/
structure Eqn where
  lhs : Term
  rhs : Term
  deriving DecidableEq, Repr

/-- `Derives E l r`: l = r follows from the equations E (a set, as a
predicate) in equational logic: instances of the axioms under any
substitution, reflexivity, symmetry, transitivity and congruence. -/
inductive Derives (E : Eqn → Prop) : Term → Term → Prop where
  | ax {e : Eqn} (σ : Nat → Term) : E e → Derives E (e.lhs.subst σ) (e.rhs.subst σ)
  | refl (t : Term) : Derives E t t
  | symm {s t : Term} : Derives E s t → Derives E t s
  | trans {s t u : Term} : Derives E s t → Derives E t u → Derives E s u
  | congr {s s' t t' : Term} : Derives E s s' → Derives E t t' → Derives E (mul s t) (mul s' t')

def x : Term := var 0
def y : Term := var 1
def z : Term := var 2

/-- The monoid axioms: associativity and a two-sided unit. -/
def monoid : Eqn → Prop := fun e =>
  e = ⟨mul (mul x y) z, mul x (mul y z)⟩ ∨ e = ⟨mul one x, x⟩ ∨ e = ⟨mul x one, x⟩

/-- Commutativity. -/
def comm : Eqn := ⟨mul x y, mul y x⟩

/-- An equational theory cannot refute an equation; independence of e from
E means: E does not derive e, and adding e to E does not collapse every
model to one element (x = y is still not derivable). -/
def Independent (E : Eqn → Prop) (e : Eqn) : Prop :=
  ¬ Derives E e.lhs e.rhs ∧ ¬ Derives (fun f => E f ∨ f = e) x y

end EL

end Ampas
