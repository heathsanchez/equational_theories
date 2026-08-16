import equational_theories.MagmaLaw

open FreeMagma
open Law

namespace FreeMagma

def supportSubst {α β : Type*} :
    (t : FreeMagma α) → ((a : α) → t.Mem a → FreeMagma β) → FreeMagma β
  | Lf a, σ => σ a rfl
  | l ⋆ r, σ =>
      supportSubst l (fun a h => σ a (.inl h)) ⋆
      supportSubst r (fun a h => σ a (.inr h))

theorem supportSubst_eq_eval_of_agree {α β : Type*} (t : FreeMagma α)
    (σ : (a : α) → t.Mem a → FreeMagma β) (τ : α → FreeMagma β)
    (h : ∀ a ha, σ a ha = τ a) : supportSubst t σ = t ⬝ τ := by
  induction t with
  | Leaf a => simpa [supportSubst, evalInMagma] using h a rfl
  | Fork l r ihl ihr =>
      simp only [supportSubst, evalInMagma]
      rw [ihl (fun a ha => σ a (.inl ha)) (fun a ha => h a (.inl ha))]
      rw [ihr (fun a ha => σ a (.inr ha)) (fun a ha => h a (.inr ha))]
      rfl

theorem supportSubst_of_total {α β : Type*} (t : FreeMagma α) (σ : α → FreeMagma β) :
    supportSubst t (fun a _ => σ a) = t ⬝ σ :=
  supportSubst_eq_eval_of_agree t (fun a _ => σ a) σ (fun _ _ => rfl)

end FreeMagma

namespace Law.MagmaLaw

def supportSubst {α β : Type*} (E : MagmaLaw α)
    (σ : (a : α) → E.Mem a → FreeMagma β) : MagmaLaw β :=
  FreeMagma.supportSubst E.lhs (fun a h => σ a (.inl h)) ≃
    FreeMagma.supportSubst E.rhs (fun a h => σ a (.inr h))

theorem supportAssignment_proof_irrel {α β : Type*} {E : MagmaLaw α}
    (σ : (a : α) → E.Mem a → FreeMagma β) (a : α) (h₁ h₂ : E.Mem a) :
    σ a h₁ = σ a h₂ := by
  rw [Subsingleton.elim h₁ h₂]

theorem supportSubst_of_total {α β : Type*} (E : MagmaLaw α) (σ : α → FreeMagma β) :
    E.supportSubst (fun a _ => σ a) = (E.lhs ⬝ σ ≃ E.rhs ⬝ σ) := by
  apply MagmaLaw.ext
  · exact FreeMagma.supportSubst_of_total E.lhs σ
  · exact FreeMagma.supportSubst_of_total E.rhs σ

end Law.MagmaLaw

inductive deriveSupport'.{u, v} {α : Type u} {β : Type v} (Γ : Ctx α) : MagmaLaw β → Type (max u v) where
  | SubstAxSupport {E} (h : E ∈ Γ)
      (σ : (a : α) → E.Mem a → FreeMagma β) :
      deriveSupport' Γ (E.supportSubst σ)
  | Ref {t} : deriveSupport' Γ (t ≃ t)
  | Sym {t u} : deriveSupport' Γ (t ≃ u) → deriveSupport' Γ (u ≃ t)
  | Trans {t u v} : deriveSupport' Γ (t ≃ u) → deriveSupport' Γ (u ≃ v) → deriveSupport' Γ (t ≃ v)
  | Cong {t₁ t₂ u₁ u₂} : deriveSupport' Γ (t₁ ≃ t₂) → deriveSupport' Γ (u₁ ≃ u₂) →
      deriveSupport' Γ (t₁ ⋆ u₁ ≃ t₂ ⋆ u₂)

def deriveSupport'_of_derive' {α β : Type*} {Γ : Ctx α} {E : MagmaLaw β} :
    derive' Γ E → deriveSupport' Γ E
  | .SubstAx (E := A) h σ => by
      rw [← A.supportSubst_of_total σ]
      exact deriveSupport'.SubstAxSupport h (fun a _ => σ a)
  | .Ref => .Ref
  | .Sym h => .Sym (deriveSupport'_of_derive' h)
  | .Trans h₁ h₂ => .Trans (deriveSupport'_of_derive' h₁) (deriveSupport'_of_derive' h₂)
  | .Cong h₁ h₂ => .Cong (deriveSupport'_of_derive' h₁) (deriveSupport'_of_derive' h₂)

def derive'_of_deriveSupport'_decidable {α β : Type*} [DecidableEq α]
    {Γ : Ctx α} {E : MagmaLaw β} : deriveSupport' Γ E → derive' Γ E
  | .SubstAxSupport (E := A) h σ => by
      let d : FreeMagma β := σ A.lhs.first (.inl A.lhs.first_mem)
      let τ : α → FreeMagma β := fun a => if ha : A.Mem a then σ a ha else d
      have hagree : ∀ a (ha : A.Mem a), σ a ha = τ a := by
        intro a ha
        simp [τ, ha]
      have hl : FreeMagma.supportSubst A.lhs (fun a ha => σ a (.inl ha)) = A.lhs ⬝ τ :=
        FreeMagma.supportSubst_eq_eval_of_agree A.lhs _ τ (fun a ha => hagree a (.inl ha))
      have hr : FreeMagma.supportSubst A.rhs (fun a ha => σ a (.inr ha)) = A.rhs ⬝ τ :=
        FreeMagma.supportSubst_eq_eval_of_agree A.rhs _ τ (fun a ha => hagree a (.inr ha))
      rw [Law.MagmaLaw.supportSubst, hl, hr]
      exact derive'.SubstAx h τ
  | .Ref => .Ref
  | .Sym h => .Sym (derive'_of_deriveSupport'_decidable h)
  | .Trans h₁ h₂ => .Trans (derive'_of_deriveSupport'_decidable h₁)
      (derive'_of_deriveSupport'_decidable h₂)
  | .Cong h₁ h₂ => .Cong (derive'_of_deriveSupport'_decidable h₁)
      (derive'_of_deriveSupport'_decidable h₂)
