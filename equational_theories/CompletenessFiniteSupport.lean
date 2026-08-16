import equational_theories.Completeness
import equational_theories.FreeMagmaEvalCongr

open FreeMagma
open Law

/-- For a single law, a valuation into the quotient only needs representatives on the variables
that occur in that law. With decidable variable equality, those finitely many representatives can
be assembled constructively into a total substitution by using one representative as the default
outside the finite support. -/
theorem PhiAsSubst_onLawSupport {α β γ} [DecidableEq β]
    (Γ : Ctx α) (E : MagmaLaw β) (φ : β → FreeMagmaWithLaws γ Γ) :
    ∃ σ : β → FreeMagma γ,
      (∀ x, E.lhs.Mem x → φ x = embed Γ (σ x)) ∧
      (∀ x, E.rhs.Mem x → φ x = embed Γ (σ x)) := by
  obtain ⟨d, hd⟩ := Quotient.exists_rep (φ E.lhs.first)
  let xs := E.lhs.elems.val ++ E.rhs.elems.val
  have liftList : ∀ ys : List β,
      ∃ σ : β → FreeMagma γ, ∀ x, x ∈ ys → φ x = embed Γ (σ x) := by
    intro ys
    induction ys with
    | nil =>
        exact ⟨fun _ ↦ d, by simp⟩
    | cons y ys ih =>
        obtain ⟨σ, hσ⟩ := ih
        obtain ⟨a, ha⟩ := Quotient.exists_rep (φ y)
        refine ⟨fun x ↦ if x = y then a else σ x, ?_⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simpa using ha.symm
        · by_cases hxy : x = y
          · subst x
            simpa using ha.symm
          · simp [hxy, hσ x hx]
  obtain ⟨σ, hσ⟩ := liftList xs
  refine ⟨σ, ?_, ?_⟩
  · intro x hx
    apply hσ x
    exact List.mem_append_left _ ((E.lhs.elems.2.2 x).2 hx)
  · intro x hx
    apply hσ x
    exact List.mem_append_right _ ((E.rhs.elems.2.2 x).2 hx)

/-- Choice-free model construction for contexts whose variable type has decidable equality.
Instead of lifting an entire quotient-valued valuation, lift only the finite support of the current
axiom and use evaluation congruence to forget all other values. -/
theorem FreeMagmaWithLaws.isModel_decidableVars {α} [DecidableEq α]
    (β) (Γ : Ctx α) : FreeMagmaWithLaws β Γ ⊧ Γ := by
  intro E hE φ
  simp only [satisfiesPhi]
  obtain ⟨σ, hL, hR⟩ := PhiAsSubst_onLawSupport Γ E φ
  calc
    E.lhs ⬝ φ = E.lhs ⬝ (embed Γ ∘ σ) := by
      apply FreeMagma.evalInMagma_congr
      intro x hx
      exact hL x hx
    _ = embed Γ (E.lhs ⬝ σ) := FreeMagmaWithLaws.evalInMagmaIsQuot Γ E.lhs σ
    _ = embed Γ (E.rhs ⬝ σ) := Quotient.sound ⟨derive'.SubstAx hE σ⟩
    _ = E.rhs ⬝ (embed Γ ∘ σ) := (FreeMagmaWithLaws.evalInMagmaIsQuot Γ E.rhs σ).symm
    _ = E.rhs ⬝ φ := by
      symm
      apply FreeMagma.evalInMagma_congr
      intro x hx
      exact hR x hx

/-- The project-standard `Nat`-variable completeness theorem can use the finite-support model and
therefore does not need the global `PhiAsSubst` choice step. This is kept separate from the existing
general theorem until kernel/axiom validation is available. -/
theorem CompletenessNat_noGlobalChoice {Γ : Ctx Nat} {E : MagmaLaw Nat}
    (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) := by
  apply FreeMagmaWithLaws.isDerives
  exact h _ (FreeMagmaWithLaws.isModel_decidableVars Nat Γ)
