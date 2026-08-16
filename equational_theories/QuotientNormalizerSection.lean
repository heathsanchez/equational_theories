import equational_theories.CompletenessCanonicalSections

open FreeMagma
open Law

structure QuotientNormalizerData {δ β : Type} (Γ : Ctx δ) where
  normalize : FreeMagma β → FreeMagma β
  normalize_respects : ∀ {x y : FreeMagma β},
    Nonempty (Γ ⊢' x ≃ y) → normalize x = normalize y
  reduces : ∀ t : FreeMagma β, Γ ⊢' t ≃ normalize t

def quotientRepresentativeData_of_normalizer {δ β : Type}
    {Γ : Ctx δ} (n : QuotientNormalizerData (β := β) Γ) :
    QuotientRepresentativeData (β := β) Γ where
  representative := Quotient.lift n.normalize (by
    intro x y h
    exact n.normalize_respects h)
  embed_representative := by
    intro q
    induction q using FreeMagmaWithLaws.inductionOn with
    | h t =>
        apply FreeMagmaWithLaws.eq.mpr
        exact ⟨derive'.Sym (n.reduces t)⟩

theorem quotientRepresentativeSection_of_normalizer {δ β : Type}
    {Γ : Ctx δ} (n : QuotientNormalizerData (β := β) Γ) :
    QuotientRepresentativeSection (β := β) Γ :=
  ⟨quotientRepresentativeData_of_normalizer n⟩

theorem contextQuotientSections_of_normalizers {δ : Type} {Γ : Ctx δ}
    (hnorm : ∀ β : Type, Nonempty (QuotientNormalizerData (β := β) Γ)) :
    ContextQuotientSections Γ := by
  intro β
  obtain ⟨n⟩ := hnorm β
  exact quotientRepresentativeSection_of_normalizer n

theorem Completeness'_normalizers {δ β : Type}
    {Γ : Ctx δ} {E : MagmaLaw β}
    (hret : ∀ A, A ∈ Γ → SupportRetract A)
    (hnorm : ∀ γ : Type, Nonempty (QuotientNormalizerData (β := γ) Γ))
    (h : Γ ⊧ E) :
    Nonempty (Γ ⊢' E) := by
  exact Completeness'_canonicalSections hret
    (contextQuotientSections_of_normalizers hnorm) h
