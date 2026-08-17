import equational_theories.SetoidOrdinaryBridge

open FreeMagma
open Law

namespace O49

open O47 O48

/-- The exact original representative-lifting resource needed to make the term quotient a model,
restricted to the source variable type of Γ. -/
def TermQuotientSourceLift {α β : Type} (Γ : Ctx α) : Prop :=
  ∀ φ : α → FreeMagmaWithLaws β Γ,
    ∃ σ : α → FreeMagma β, ∀ a, φ a = embed Γ (σ a)

/-- The setoid term model quotient is definitionally the same quotient used by
`FreeMagmaWithLaws`; its source-valuation lift is therefore just the original representative
family lift in different packaging. -/
theorem sourceValuationLift_termSetoid_iff {α β : Type} (Γ : Ctx α) :
    SourceValuationLift (α := α) (TermSetoidMagma (β := β) Γ) ↔
      TermQuotientSourceLift (β := β) Γ := by
  rfl

/-- The original `PhiAsSubst_aux` proves the term-setoid source-lift using Classical.choice. -/
theorem termSetoid_sourceLift_of_PhiAsSubst {α β : Type} (Γ : Ctx α) :
    SourceValuationLift (α := α) (TermSetoidMagma (β := β) Γ) := by
  rw [sourceValuationLift_termSetoid_iff]
  intro φ
  exact PhiAsSubst_aux Γ φ

/-- Conversely, a term-setoid source lift supplies exactly the source-specialized
`PhiAsSubst_aux` conclusion, without any additional representative selection. -/
theorem phiAsSubstSource_of_termSetoid_sourceLift {α β : Type} (Γ : Ctx α)
    (h : SourceValuationLift (α := α) (TermSetoidMagma (β := β) Γ))
    (φ : α → FreeMagmaWithLaws β Γ) :
    ∃ σ : α → FreeMagma β, ∀ a, φ a = embed Γ (σ a) := by
  exact (sourceValuationLift_termSetoid_iff Γ).1 h φ

end O49
