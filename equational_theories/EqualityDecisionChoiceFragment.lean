import equational_theories.CompletenessDecisionUniformizationBoundary

/-- The one family of Type-valued objects that O42 needs to uniformize: equality decisions indexed
by pairs of source variables. -/
def EqualityDecisionFamily (α : Type) (ab : α × α) : Type :=
  Decidable (ab.1 = ab.2)

/-- A restricted choice principle for exactly the equality-decision family. This is intentionally
not arbitrary choice over arbitrary indexed families. -/
def EqualityDecisionChoiceFragment (α : Type) : Prop :=
  (∀ ab : α × α, Nonempty (EqualityDecisionFamily α ab)) →
    Nonempty ((ab : α × α) → EqualityDecisionFamily α ab)

/-- O44: O42's curried equality-decision uniformizer and restricted choice over the
pair-indexed equality-decision family are inter-derivable. -/
theorem equalityDecisionUniformizer_iff_choiceFragment (α : Type) :
    EqualityDecisionUniformizer α ↔ EqualityDecisionChoiceFragment α := by
  constructor
  · intro hUniform hPoint
    have hCurried : PointwiseEqualityDecision α := by
      intro a b
      exact hPoint (a, b)
    obtain ⟨deq⟩ := hUniform hCurried
    exact ⟨fun ab => deq ab.1 ab.2⟩
  · intro hChoice hPoint
    have hPairs : ∀ ab : α × α, Nonempty (EqualityDecisionFamily α ab) := by
      intro ab
      exact hPoint ab.1 ab.2
    obtain ⟨decPairs⟩ := hChoice hPairs
    exact ⟨fun a b => decPairs (a, b)⟩

/-- Prop-level excluded middle supplies the pointwise premise of this restricted family; only the
family-specific uniformization remains. -/
theorem equalityDecisionFamily_pointwise_of_em
    (hem : PropExcludedMiddle) (α : Type) :
    ∀ ab : α × α, Nonempty (EqualityDecisionFamily α ab) := by
  intro ab
  exact pointwiseEqualityDecision_of_em hem α ab.1 ab.2

/-- Generic completeness can therefore be stated using only Prop-level excluded middle plus the
restricted equality-decision choice fragment. -/
theorem Completeness'_of_em_and_equalityDecisionChoiceFragment {α β : Type}
    (hem : PropExcludedMiddle)
    (hchoice : EqualityDecisionChoiceFragment α)
    {Γ : Ctx α} {E : Law.MagmaLaw β}
    (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) := by
  apply Completeness'_of_em_and_equalityDecisionUniformizer hem
  · exact (equalityDecisionUniformizer_iff_choiceFragment α).2 hchoice
  · exact h
