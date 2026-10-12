import AmpasRef.Defs

namespace Ampas.EL
open Term

/-- Value of a term in a structure (mul, one) under an assignment ρ. -/
def eval {α : Type} (mul : α → α → α) (one : α) (ρ : Nat → α) : Term → α
  | var i => ρ i
  | Term.one => one
  | Term.mul s t => mul (eval mul one ρ s) (eval mul one ρ t)

theorem eval_subst {α : Type} (mul : α → α → α) (one : α) (ρ : Nat → α) (σ : Nat → Term) :
    ∀ t : Term, eval mul one ρ (t.subst σ) = eval mul one (fun i => eval mul one ρ (σ i)) t
  | var _ => rfl
  | Term.one => rfl
  | Term.mul s t => by
    simp only [Term.subst, eval, eval_subst mul one ρ σ s, eval_subst mul one ρ σ t]

/-- Soundness of equational logic: what E derives holds in every
structure that satisfies E. -/
theorem sound {α : Type} {mul : α → α → α} {one : α} {E : Eqn → Prop}
    (hE : ∀ e, E e → ∀ ρ, eval mul one ρ e.lhs = eval mul one ρ e.rhs) :
    ∀ {s t : Term}, Derives E s t → ∀ ρ, eval mul one ρ s = eval mul one ρ t := by
  intro s t h
  induction h with
  | ax σ he => intro ρ; rw [eval_subst, eval_subst]; exact hE _ he _
  | refl => intro ρ; rfl
  | symm _ ih => intro ρ; exact (ih ρ).symm
  | trans _ _ ih1 ih2 => intro ρ; exact (ih1 ρ).trans (ih2 ρ)
  | congr _ _ ih1 ih2 => intro ρ; simp only [eval, ih1 ρ, ih2 ρ]

/-- A non-commutative monoid: functions Bool → Bool under composition. -/
theorem fun_monoid : ∀ e, monoid e → ∀ ρ : Nat → (Bool → Bool),
    eval (fun f g => f ∘ g) id ρ e.lhs = eval (fun f g => f ∘ g) id ρ e.rhs := by
  intro e he ρ
  rcases he with rfl | rfl | rfl <;> rfl

/-- A commutative monoid with two elements: Bool under exclusive or. -/
theorem xor_comm_monoid : ∀ e, (monoid e ∨ e = comm) → ∀ ρ : Nat → Bool,
    eval xor false ρ e.lhs = eval xor false ρ e.rhs := by
  intro e he ρ
  rcases he with (rfl | rfl | rfl) | rfl <;> simp only [comm, eval, x, y, z] <;>
    (cases ρ 0 <;> cases ρ 1 <;> cases ρ 2 <;> rfl)

end Ampas.EL

namespace Ampas.Claims
open Ampas.EL

theorem el_comm_independent : EL.Independent EL.monoid EL.comm := by
  constructor
  · intro h
    have := sound fun_monoid h (fun i => if i = 0 then (fun _ => true) else not)
    have := congrFun this false
    simp [comm, eval, x, y] at this
  · intro h
    have := sound xor_comm_monoid h (fun i => i == 0)
    simp [eval, x, y] at this

end Ampas.Claims
