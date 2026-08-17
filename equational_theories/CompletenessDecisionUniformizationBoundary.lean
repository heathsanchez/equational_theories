import equational_theories.CompletenessSupportResources

open FreeMagma
open Law

def PropExcludedMiddle : Prop := ∀ p : Prop, p ∨ ¬ p

def PointwiseEqualityDecision (α : Type) : Prop :=
  ∀ a b : α, Nonempty (Decidable (a = b))

def EqualityDecisionUniformizer (α : Type) : Prop :=
  PointwiseEqualityDecision α → Nonempty (DecidableEq α)

/-- Prop-level excluded middle can produce decision data pointwise because the result is wrapped in
`Nonempty`, hence remains Prop-valued. -/
theorem pointwiseEqualityDecision_of_em
    (hem : PropExcludedMiddle) (α : Type) : PointwiseEqualityDecision α := by
  intro a b
  rcases hem (a = b) with h | h
  · exact ⟨isTrue h⟩
  · exact ⟨isFalse h⟩

/-- The remaining gap is uniformization: assembling pointwise decision existence into one
`DecidableEq` function. -/
theorem nonemptyDecidableEq_of_em_uniformizer
    (hem : PropExcludedMiddle) {α : Type}
    (uniformize : EqualityDecisionUniformizer α) : Nonempty (DecidableEq α) :=
  uniformize (pointwiseEqualityDecision_of_em hem α)

/-- O42 factorization: Prop-level excluded middle plus only the equality-decision uniformization
resource is sufficient for the existing choice-free support-resource completeness route. -/
theorem Completeness'_of_em_and_equalityDecisionUniformizer {α β : Type}
    (hem : PropExcludedMiddle)
    (uniformize : EqualityDecisionUniformizer α)
    {Γ : Ctx α} {E : MagmaLaw β}
    (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) := by
  obtain ⟨deq⟩ := nonemptyDecidableEq_of_em_uniformizer hem uniformize
  letI : DecidableEq α := deq
  apply FreeMagmaWithLaws.isDerives
  exact h _ (FreeMagmaWithLaws.isModel_decidableVars_via_resources β Γ)
