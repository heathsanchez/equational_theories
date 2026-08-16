import equational_theories.AssociativityQuotientNormalizer

open FreeMagma
open Law

/-- A more searchable presentation of O29 normalizer data. Instead of guessing an arbitrary syntax
endofunction, expose a semantic invariant and a canonical reconstruction from invariant values. -/
structure InvariantReconstructionData {δ β I : Type} (Γ : Ctx δ) where
  observe : FreeMagma β → I
  reconstruct : I → FreeMagma β
  observe_respects : ∀ {x y : FreeMagma β},
    Nonempty (Γ ⊢' x ≃ y) → observe x = observe y
  reduces : ∀ t : FreeMagma β, Γ ⊢' t ≃ reconstruct (observe t)

/-- Invariant + reconstruction data compiles directly into O29's verified normalizer interface. -/
def QuotientNormalizerData.ofInvariantReconstruction {δ β I : Type}
    {Γ : Ctx δ} (d : InvariantReconstructionData (β := β) (I := I) Γ) :
    QuotientNormalizerData (β := β) Γ where
  normalize := d.reconstruct ∘ d.observe
  normalize_respects := by
    intro x y h
    exact congrArg d.reconstruct (d.observe_respects h)
  reduces := by
    intro t
    exact d.reduces t

/-- Therefore an invariant/reconstruction family in every codomain is sufficient for context-wide
constructive quotient sections. -/
theorem contextQuotientSections_of_invariantReconstruction {δ : Type} {Γ : Ctx δ}
    (h : ∀ β : Type, ∃ I : Type,
      Nonempty (InvariantReconstructionData (β := β) (I := I) Γ)) :
    ContextQuotientSections Γ := by
  apply contextQuotientSections_of_normalizers
  intro β
  obtain ⟨I, d⟩ := h β
  obtain ⟨d⟩ := d
  exact ⟨QuotientNormalizerData.ofInvariantReconstruction d⟩

/-- And with support retraction, the invariant/reconstruction interface is directly a generic
choice-free completeness route. -/
theorem Completeness'_invariantReconstruction {δ β : Type}
    {Γ : Ctx δ} {E : MagmaLaw β}
    (hret : ∀ A, A ∈ Γ → SupportRetract A)
    (hinv : ∀ γ : Type, ∃ I : Type,
      Nonempty (InvariantReconstructionData (β := γ) (I := I) Γ))
    (h : Γ ⊧ E) :
    Nonempty (Γ ⊢' E) := by
  exact Completeness'_canonicalSections hret
    (contextQuotientSections_of_invariantReconstruction hinv) h

private theorem toList_nonempty {β : Type} (t : FreeMagma β) : t.toList ≠ [] := by
  intro ht
  have hz : t.toList.length = 0 := by simp [ht]
  rw [FreeMagma.toList_length] at hz
  exact t.length_ne_0 hz

/-- O30 factors through the new search interface: its semantic invariant is precisely the nonempty
ordered leaf list, reconstructed as the canonical right-associated tree. -/
def invariantReconstructionData_associativity {β : Type} :
    InvariantReconstructionData (β := β)
      (I := {xs : List β // xs ≠ []}) associativityCtx where
  observe := fun t => ⟨t.toList, toList_nonempty t⟩
  reconstruct := fun xs => rightAssocList xs.1 xs.2
  observe_respects := by
    intro x y h
    obtain ⟨d⟩ := h
    apply Subtype.ext
    exact derive'_associativity_toList_eq d
  reduces := by
    intro t
    simpa [associativityNormalize] using derive'_associativity_reduce t

/-- The associative quotient section can therefore be obtained by the generic
invariant/reconstruction compiler rather than by mentioning its hand-written normalizer data. -/
theorem contextQuotientSections_associativity_viaInvariant :
    ContextQuotientSections associativityCtx := by
  apply contextQuotientSections_of_invariantReconstruction
  intro β
  exact ⟨{xs : List β // xs ≠ []}, ⟨invariantReconstructionData_associativity⟩⟩
