import equational_theories.SupportLocalDerivation
import equational_theories.Completeness

open FreeMagma
open Law

namespace O46

/-- Evaluate a term using values supplied only for variables that actually occur in it. -/
def supportEval {α G : Type*} [Magma G] :
    (t : FreeMagma α) → ((a : α) → t.Mem a → G) → G
  | .Lf a, φ => φ a rfl
  | l ⋆ r, φ =>
      supportEval l (fun a h => φ a (.inl h)) ◇
      supportEval r (fun a h => φ a (.inr h))

/-- Support-local satisfaction of one law. -/
def satisfiesSupport {α G : Type*} [Magma G] (E : MagmaLaw α) : Prop :=
  ∀ φ : (a : α) → E.Mem a → G,
    supportEval E.lhs (fun a h => φ a (.inl h)) =
    supportEval E.rhs (fun a h => φ a (.inr h))

/-- Support-local satisfaction of a context. -/
def satisfiesSupportSet {α G : Type*} [Magma G] (Γ : Ctx α) : Prop :=
  ∀ E ∈ Γ, satisfiesSupport E

/-- Support-local entailment. -/
def modelsSupport {α β : Type*} (Γ : Ctx α) (E : MagmaLaw β) : Prop :=
  ∀ (G : Type) [Magma G], satisfiesSupportSet G Γ → satisfiesSupport E

/-- Evaluating a support substitution under an ordinary target valuation is the same as
support-evaluating the source term with the substituted terms evaluated under that valuation. -/
theorem eval_supportSubst {α β G : Type*} [Magma G]
    (t : FreeMagma α) (σ : (a : α) → t.Mem a → FreeMagma β) (φ : β → G) :
    (FreeMagma.supportSubst t σ) ⬝ φ =
      supportEval t (fun a h => (σ a h) ⬝ φ) := by
  induction t with
  | Leaf a => rfl
  | Fork l r ihl ihr =>
      simp only [FreeMagma.supportSubst, evalInMagma, supportEval]
      rw [ihl, ihr]

/-- Soundness of the support-local calculus for support-local semantics. -/
theorem SoundnessSupport'_u {α β G : Type*} [Magma G]
    {Γ : Ctx α} {E : MagmaLaw β} (h : deriveSupport' Γ E) :
    satisfiesSupportSet G Γ → satisfiesSupport E := by
  induction h with
  | @SubstAxSupport A mem σ =>
      intro H φ
      have hA := H A mem (fun a ha => (σ a ha) ⬝ φ)
      simp only [Law.MagmaLaw.supportSubst]
      rw [eval_supportSubst, eval_supportSubst]
      exact hA
  | Ref =>
      intro _ φ
      rfl
  | @Sym t u _ ih =>
      intro H φ
      exact (ih H φ).symm
  | Trans h₁ h₂ ih₁ ih₂ =>
      intro H φ
      exact (ih₁ H φ).trans (ih₂ H φ)
  | Cong h₁ h₂ ih₁ ih₂ =>
      intro H φ
      simp only [supportEval]
      rw [ih₁ H, ih₂ H]

/-- Support-local derivations are sound for support-local entailment. -/
theorem SoundnessSupport' {α β : Type*} {Γ : Ctx α} {E : MagmaLaw β}
    (h : deriveSupport' Γ E) : modelsSupport Γ E :=
  fun _ _ => SoundnessSupport'_u h

end O46
