import equational_theories.CompletenessSupportResources

open FreeMagma
open Law

/-- Normal form of `SupportQuotientLift`: choose a representative only for each actual support
variable, expressed directly as a function on the support subtype. -/
def SupportIndexedQuotientSection {δ α : Type} (Γ : Ctx δ) (E : MagmaLaw α) : Prop :=
  ∀ (β : Type) (φ : α → FreeMagmaWithLaws β Γ),
    ∃ ρ : {a : α // E.Mem a} → FreeMagma β,
      ∀ s, φ s.1 = embed Γ (ρ s)

/-- The dependent-proof presentation used by O10 is exactly the support-subtype section principle. -/
theorem supportQuotientLift_iff_supportIndexedSection {δ α : Type}
    (Γ : Ctx δ) (E : MagmaLaw α) :
    SupportQuotientLift Γ E ↔ SupportIndexedQuotientSection Γ E := by
  constructor
  · intro h β φ
    obtain ⟨σ, hσ⟩ := h β φ
    refine ⟨fun s => σ s.1 s.2, ?_⟩
    intro s
    exact hσ s.1 s.2
  · intro h β φ
    obtain ⟨ρ, hρ⟩ := h β φ
    refine ⟨fun a ha => ρ ⟨a, ha⟩, ?_⟩
    intro a ha
    exact hρ ⟨a, ha⟩

/-- O10 can be restated using the normal-form support-indexed quotient section. -/
theorem totalSubst_of_supportSection {δ α β : Type}
    (Γ : Ctx δ) (E : MagmaLaw α) (φ : α → FreeMagmaWithLaws β Γ)
    (hret : SupportRetract E)
    (hsec : SupportIndexedQuotientSection Γ E) :
    ∃ τ : α → FreeMagma β, ∀ a, E.Mem a → φ a = embed Γ (τ a) := by
  apply totalSubst_of_supportResources Γ E φ hret
  exact (supportQuotientLift_iff_supportIndexedSection Γ E).2 hsec
