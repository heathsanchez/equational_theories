import equational_theories.CanonicalQuotientSection
import equational_theories.CompletenessSupportResources

open FreeMagma
open Law

/-- A context-level quotient-normalization resource: every codomain quotient admits a constructive
representative section, stated propositionally so it can be consumed by proposition-level
completeness without extracting global data into an unrelated Type-valued target. -/
def ContextQuotientSections {δ : Type} (Γ : Ctx δ) : Prop :=
  ∀ β : Type, QuotientRepresentativeSection (β := β) Γ

/-- Canonical quotient sections discharge the representative-selection half of O10 uniformly.
Only per-axiom support retraction remains as an independent resource. -/
theorem supportQuotientLift_of_contextSections {δ α : Type}
    (Γ : Ctx δ) (hsec : ContextQuotientSections Γ) (E : MagmaLaw α) :
    SupportQuotientLift Γ E :=
  supportQuotientLift_of_globalSections Γ E hsec

/-- Choice-free completeness from two orthogonal context resources:
(1) every axiom support retracts into the ambient variable type;
(2) the quotient itself has canonical representatives in every codomain.
No support indexing or ambient decidable equality is required by this theorem. -/
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

/-- The empty context is the base instance: its quotient is definitionally recoverable via O23. -/
theorem contextQuotientSections_empty {δ : Type} :
    ContextQuotientSections (∅ : Ctx δ) := by
  intro β
  exact quotientRepresentativeSection_empty
