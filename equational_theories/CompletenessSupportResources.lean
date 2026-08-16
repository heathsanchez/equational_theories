import equational_theories.CompletenessFiniteSupport
import equational_theories.SupportLocalDerivation
import equational_theories.SupportSemanticBoundary

open FreeMagma
open Law

/-- Exact representative-selection resource needed on the support of one law. This is deliberately
weaker than a global representative function on the whole ambient variable type. -/
def SupportQuotientLift {δ α : Type} (Γ : Ctx δ) (E : MagmaLaw α) : Prop :=
  ∀ (β : Type) (φ : α → FreeMagmaWithLaws β Γ),
    ∃ σ : (a : α) → E.Mem a → FreeMagma β,
      ∀ a h, φ a = embed Γ (σ a h)

/-- A support-local representative assignment plus a support retraction can be compiled into the
total substitution expected by the current `derive'.SubstAx` interface, while preserving the
representatives on all variables visible to the law. -/
theorem totalSubst_of_supportResources {δ α β : Type}
    (Γ : Ctx δ) (E : MagmaLaw α) (φ : α → FreeMagmaWithLaws β Γ)
    (hret : SupportRetract E)
    (hlift : SupportQuotientLift Γ E) :
    ∃ τ : α → FreeMagma β, ∀ a, E.Mem a → φ a = embed Γ (τ a) := by
  obtain ⟨σ, hσ⟩ := hlift β φ
  obtain ⟨r, hr⟩ := hret
  let τ : α → FreeMagma β := fun a => σ (r a).1 (r a).2
  refine ⟨τ, ?_⟩
  intro a ha
  have hra : r a = ⟨a, ha⟩ := hr ⟨a, ha⟩
  have hval : σ a ha = τ a := by
    simp only [τ]
    rw [hra]
  rw [← hval]
  exact hσ a ha

/-- Model construction parameterized by the two exact per-law resources exposed by O8/O9:
representative selection *on support* and retraction *onto support*. No global `DecidableEq` or
`Classical.choice` is used by this theorem. -/
theorem FreeMagmaWithLaws.isModel_supportResources {α : Type}
    (β : Type) (Γ : Ctx α)
    (hret : ∀ E, E ∈ Γ → SupportRetract E)
    (hlift : ∀ E, E ∈ Γ → SupportQuotientLift Γ E) :
    FreeMagmaWithLaws β Γ ⊧ Γ := by
  intro E hE φ
  simp only [satisfiesPhi]
  obtain ⟨τ, hτ⟩ := totalSubst_of_supportResources Γ E φ (hret E hE) (hlift E hE)
  calc
    E.lhs ⬝ φ = E.lhs ⬝ (embed Γ ∘ τ) := by
      apply FreeMagma.evalInMagma_congr
      intro x hx
      exact hτ x (.inl hx)
    _ = embed Γ (E.lhs ⬝ τ) := FreeMagmaWithLaws.evalInMagmaIsQuot Γ E.lhs τ
    _ = embed Γ (E.rhs ⬝ τ) := Quotient.sound ⟨derive'.SubstAx hE τ⟩
    _ = E.rhs ⬝ (embed Γ ∘ τ) := (FreeMagmaWithLaws.evalInMagmaIsQuot Γ E.rhs τ).symm
    _ = E.rhs ⬝ φ := by
      symm
      apply FreeMagma.evalInMagma_congr
      intro x hx
      exact hτ x (.inr hx)

/-- Type-0 completeness under explicit support resources rather than a global decidable-equality
assumption. -/
theorem Completeness'_supportResources {α β : Type}
    {Γ : Ctx α} {E : MagmaLaw β}
    (hret : ∀ A, A ∈ Γ → SupportRetract A)
    (hlift : ∀ A, A ∈ Γ → SupportQuotientLift Γ A)
    (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) := by
  apply FreeMagmaWithLaws.isDerives
  exact h _ (FreeMagmaWithLaws.isModel_supportResources β Γ hret hlift)

/-- O4's decidable-variable construction supplies the support-quotient-lift resource without
requiring the contaminated `MagmaLaw.finEquiv` route. -/
theorem supportQuotientLift_of_decidableEq {δ α : Type} [DecidableEq α]
    (Γ : Ctx δ) (E : MagmaLaw α) : SupportQuotientLift Γ E := by
  intro β φ
  obtain ⟨τ, hL, hR⟩ := PhiAsSubst_onLawSupport Γ E φ
  refine ⟨fun a _ => τ a, ?_⟩
  intro a ha
  rcases ha with ha | ha
  · exact hL a ha
  · exact hR a ha

/-- The original O4 decidable-equality scope is recovered as one sufficient resource provider.
This factors its role into support retraction plus support representative selection. -/
theorem FreeMagmaWithLaws.isModel_decidableVars_via_resources {α : Type} [DecidableEq α]
    (β : Type) (Γ : Ctx α) : FreeMagmaWithLaws β Γ ⊧ Γ := by
  apply FreeMagmaWithLaws.isModel_supportResources β Γ
  · intro E hE
    exact supportRetract_of_decidableEq E
  · intro E hE
    exact supportQuotientLift_of_decidableEq Γ E
