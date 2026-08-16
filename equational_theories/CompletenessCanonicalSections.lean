import equational_theories.CanonicalQuotientSection
import equational_theories.CompletenessSupportResources

open FreeMagma
open Law

def ContextQuotientSections {δ : Type} (Γ : Ctx δ) : Prop :=
  ∀ β : Type, QuotientRepresentativeSection (β := β) Γ

theorem supportQuotientLift_of_contextSections {δ α : Type}
    (Γ : Ctx δ) (hsec : ContextQuotientSections Γ) (E : MagmaLaw α) :
    SupportQuotientLift Γ E :=
  supportQuotientLift_of_globalSections Γ E hsec

theorem Completeness'_canonicalSections {δ β : Type}
    {Γ : Ctx δ} {E : MagmaLaw β}
    (hret : ∀ A, A ∈ Γ → SupportRetract A)
    (hsec : ContextQuotientSections Γ)
    (h : Γ ⊧ E) :
    Nonempty (Γ ⊢' E) := by
  exact Completeness'_supportResources
    hret
    (fun A _ => supportQuotientLift_of_contextSections Γ hsec A)
    h

theorem contextQuotientSections_empty {δ : Type} :
    ContextQuotientSections (∅ : Ctx δ) := by
  intro β
  exact quotientRepresentativeSection_empty
