import equational_theories.CompletenessSupportResources

open FreeMagma
open Law

/-- `SingletonSupport E a₀` means that `a₀` occurs in the law and every variable occurring in the
law is equal to `a₀`. No decidable equality on the ambient variable type is assumed. -/
def SingletonSupport {α : Type} (E : MagmaLaw α) (a₀ : α) : Prop :=
  E.Mem a₀ ∧ ∀ a, E.Mem a → a = a₀

/-- Singleton support is retractable constructively: every ambient variable is sent to the one
visible support point, and that map is the identity on the support subtype because all support
points are propositionally equal to `a₀`. -/
theorem supportRetract_of_singletonSupport {α : Type} {E : MagmaLaw α} {a₀ : α}
    (h : SingletonSupport E a₀) : SupportRetract E := by
  rcases h with ⟨ha₀, huniq⟩
  let r : α → {a // E.Mem a} := fun _ => ⟨a₀, ha₀⟩
  refine ⟨r, ?_⟩
  intro s
  apply Subtype.ext
  exact (huniq s.1 s.2).symm

/-- Singleton support also admits quotient-representative selection constructively: choose one
representative of `φ a₀` and reuse it at every support occurrence. -/
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

/-- Context-level hypothesis: every axiom has propositionally singleton support. -/
def ContextSingletonSupport {α : Type} (Γ : Ctx α) : Prop :=
  ∀ E, E ∈ Γ → ∃ a₀, SingletonSupport E a₀

/-- Every singleton-support context supplies both exact resources needed by O10. -/
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

/-- Choice-free quotient-model construction for singleton-support contexts over an arbitrary
variable type. In particular, this theorem has no `[DecidableEq α]` assumption. -/
theorem FreeMagmaWithLaws.isModel_singletonSupport {α : Type}
    (β : Type) (Γ : Ctx α) (hΓ : ContextSingletonSupport Γ) :
    FreeMagmaWithLaws β Γ ⊧ Γ := by
  obtain ⟨hret, hlift⟩ := singletonContext_supportResources hΓ
  exact FreeMagmaWithLaws.isModel_supportResources β Γ hret hlift

/-- Type-0 completeness for singleton-support contexts with no global decidable-equality or choice
assumption on the variable language. -/
theorem Completeness'_singletonSupport {α β : Type}
    {Γ : Ctx α} {E : MagmaLaw β}
    (hΓ : ContextSingletonSupport Γ)
    (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) := by
  obtain ⟨hret, hlift⟩ := singletonContext_supportResources hΓ
  exact Completeness'_supportResources hret hlift h
