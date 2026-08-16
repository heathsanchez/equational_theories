import equational_theories.MagmaLaw

open FreeMagma
open Law

namespace FreeMagma

/-- Structural substitution that asks only for values of variables together with evidence that the
variable occurs in the term. No value is requested off support and no equality test is needed. -/
def supportSubst {α β : Type} :
    (t : FreeMagma α) → ((a : α) → t.Mem a → FreeMagma β) → FreeMagma β
  | Lf a, σ => σ a rfl
  | l ⋆ r, σ =>
      supportSubst l (fun a h => σ a (.inl h)) ⋆
      supportSubst r (fun a h => σ a (.inr h))

/-- Ordinary total substitution is a special case of support-local substitution. -/
theorem supportSubst_of_total {α β : Type} (t : FreeMagma α) (σ : α → FreeMagma β) :
    supportSubst t (fun a _ => σ a) = t ⬝ σ := by
  induction t with
  | Leaf a => rfl
  | Fork l r ihl ihr =>
      simp only [supportSubst, evalInMagma]
      rw [ihl, ihr]

end FreeMagma

namespace Law.MagmaLaw

/-- Support-local substitution for a law. The assignment is requested only for variables carrying
proof that they occur on at least one side of the law. -/
def supportSubst {α β : Type} (E : MagmaLaw α)
    (σ : (a : α) → E.Mem a → FreeMagma β) : MagmaLaw β :=
  FreeMagma.supportSubst E.lhs (fun a h => σ a (.inl h)) ≃
    FreeMagma.supportSubst E.rhs (fun a h => σ a (.inr h))

/-- A total law substitution compiles into the support-local representation exactly. -/
theorem supportSubst_of_total {α β : Type} (E : MagmaLaw α) (σ : α → FreeMagma β) :
    E.supportSubst (fun a _ => σ a) = (E.lhs ⬝ σ ≃ E.rhs ⬝ σ) := by
  apply MagmaLaw.ext
  · exact FreeMagma.supportSubst_of_total E.lhs σ
  · exact FreeMagma.supportSubst_of_total E.rhs σ

end Law.MagmaLaw

/-- Variant of `derive'` whose axiom-substitution constructor asks only for the support of that
particular axiom. This is a representation experiment, not yet a replacement for `derive'`. -/
inductive deriveSupport'.{u, v} {α : Type u} {β : Type v} (Γ : Ctx α) : MagmaLaw β → Type (max u v) where
  | SubstAxSupport {E} (h : E ∈ Γ)
      (σ : (a : α) → E.Mem a → FreeMagma β) :
      deriveSupport' Γ (E.supportSubst σ)
  | Ref {t} : deriveSupport' Γ (t ≃ t)
  | Sym {t u} : deriveSupport' Γ (t ≃ u) → deriveSupport' Γ (u ≃ t)
  | Trans {t u v} : deriveSupport' Γ (t ≃ u) → deriveSupport' Γ (u ≃ v) →
      deriveSupport' Γ (t ≃ v)
  | Cong {t₁ t₂ u₁ u₂} : deriveSupport' Γ (t₁ ≃ t₂) → deriveSupport' Γ (u₁ ≃ u₂) →
      deriveSupport' Γ (t₁ ⋆ u₁ ≃ t₂ ⋆ u₂)

/-- Every existing `derive'` proof translates into the support-local calculus. Thus the new
constructor is at least representation-wise strong enough to express all ordinary derivations. -/
def deriveSupport'_of_derive' {α β : Type} {Γ : Ctx α} {E : MagmaLaw β} :
    derive' Γ E → deriveSupport' Γ E
  | .SubstAx (E := A) h σ => by
      rw [← A.supportSubst_of_total σ]
      exact deriveSupport'.SubstAxSupport h (fun a _ => σ a)
  | .Ref => .Ref
  | .Sym h => .Sym (deriveSupport'_of_derive' h)
  | .Trans h₁ h₂ => .Trans (deriveSupport'_of_derive' h₁) (deriveSupport'_of_derive' h₂)
  | .Cong h₁ h₂ => .Cong (deriveSupport'_of_derive' h₁) (deriveSupport'_of_derive' h₂)
