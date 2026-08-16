import equational_theories.CompletenessSupportResources

open FreeMagma
open Law

def SingletonSupport {α : Type} (E : MagmaLaw α) (a₀ : α) : Prop :=
  E.Mem a₀ ∧ ∀ a, E.Mem a → a = a₀

theorem supportRetract_of_singletonSupport {α : Type} {E : MagmaLaw α} {a₀ : α}
    (h : SingletonSupport E a₀) : SupportRetract E := by
  rcases h with ⟨ha₀, huniq⟩
  let r : α → {a // E.Mem a} := fun _ => ⟨a₀, ha₀⟩
  refine ⟨r, ?_⟩
  intro s
  apply Subtype.ext
  exact (huniq s.1 s.2).symm

theorem supportQuotientLift_of_singletonSupport {δ α : Type}
    (Γ : Ctx δ) {E : MagmaLaw α} {a₀ : α}
    (h : SingletonSupport E a₀) : SupportQuotientLift Γ E := by
  intro β φ
  obtain ⟨r, hr⟩ := Quotient.exists_rep (φ a₀)
  refine ⟨fun _ _ => r, ?_⟩
  intro a ha
  have haa₀ : a = a₀ := h.2 a ha
  subst a
  exact hr.symm

def ContextSingletonSupport {α : Type} (Γ : Ctx α) : Prop :=
  ∀ E, E ∈ Γ → ∃ a₀, SingletonSupport E a₀

theorem singletonContext_supportResources {α : Type} {Γ : Ctx α}
    (hΓ : ContextSingletonSupport Γ) :
    (∀ E, E ∈ Γ → SupportRetract E) ∧
    (∀ E, E ∈ Γ → SupportQuotientLift Γ E) := by
  constructor
  · intro E hE
    obtain ⟨a₀, h⟩ := hΓ E hE
    exact supportRetract_of_singletonSupport h
  · intro E hE
    obtain ⟨a₀, h⟩ := hΓ E hE
    exact supportQuotientLift_of_singletonSupport Γ h

theorem FreeMagmaWithLaws.isModel_singletonSupport {α : Type}
    (β : Type) (Γ : Ctx α) (hΓ : ContextSingletonSupport Γ) :
    FreeMagmaWithLaws β Γ ⊧ Γ := by
  obtain ⟨hret, hlift⟩ := singletonContext_supportResources hΓ
  exact FreeMagmaWithLaws.isModel_supportResources β Γ hret hlift

theorem Completeness'_singletonSupport {α β : Type}
    {Γ : Ctx α} {E : MagmaLaw β}
    (hΓ : ContextSingletonSupport Γ)
    (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) := by
  obtain ⟨hret, hlift⟩ := singletonContext_supportResources hΓ
  exact Completeness'_supportResources hret hlift h
