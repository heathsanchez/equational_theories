import equational_theories.OccurrenceLift
import equational_theories.CompletenessSupportResources

open FreeMagma
open Law

/-- O38 package: both sides of one source axiom have independently chosen occurrence-local
representatives under the same quotient-valued valuation. No variable-indexed representative map
is part of this data. -/
structure LawOccurrencePackage {δ α β : Type} (Γ : Ctx δ)
    (E : MagmaLaw α) (φ : α → FreeMagmaWithLaws β Γ) where
  lhsRep : FreeMagma β
  rhsRep : FreeMagma β
  lhsLift : OccurrenceLift Γ φ E.lhs lhsRep
  rhsLift : OccurrenceLift Γ φ E.rhs rhsRep

/-- O6 constructs an occurrence package for every law and quotient-valued valuation, without
`DecidableEq` and without choosing one representative per source variable. -/
theorem lawOccurrencePackage_exists {δ α β : Type} (Γ : Ctx δ)
    (E : MagmaLaw α) (φ : α → FreeMagmaWithLaws β Γ) :
    ∃ p : LawOccurrencePackage Γ E φ, True := by
  obtain ⟨l, hl⟩ := occurrenceLift_exists Γ φ E.lhs
  obtain ⟨r, hr⟩ := occurrenceLift_exists Γ φ E.rhs
  exact ⟨⟨l, r, hl, hr⟩, trivial⟩

/-- The exact resource missing after occurrence-local representative acquisition: compile any
occurrence package of an admitted axiom into an ordinary derivability certificate between its two
representative trees.

Crucially this interface asks for neither a total substitution nor a support-indexed substitution.
-/
def OccurrenceAxiomCompiler {δ α : Type} (Γ : Ctx δ) (E : MagmaLaw α) : Prop :=
  ∀ (hE : E ∈ Γ) (β : Type) (φ : α → FreeMagmaWithLaws β Γ)
    (p : LawOccurrencePackage Γ E φ),
      Nonempty (Γ ⊢' p.lhsRep ≃ p.rhsRep)

/-- If an occurrence compiler exists for each source axiom, the quotient is a model of the source
context directly. This bypasses `SupportRetract`, ambient totalization, and `SupportQuotientLift`.
-/
theorem FreeMagmaWithLaws.isModel_occurrenceCompilers {α : Type}
    (β : Type) (Γ : Ctx α)
    (hcompile : ∀ E, E ∈ Γ → OccurrenceAxiomCompiler Γ E) :
    FreeMagmaWithLaws β Γ ⊧ Γ := by
  intro E hE φ
  simp only [satisfiesPhi]
  obtain ⟨l, hl⟩ := occurrenceLift_exists Γ φ E.lhs
  obtain ⟨r, hr⟩ := occurrenceLift_exists Γ φ E.rhs
  let p : LawOccurrencePackage Γ E φ := ⟨l, r, hl, hr⟩
  have hlEval : E.lhs ⬝ φ = embed Γ p.lhsRep := occurrenceLift_eval_eq_embed p.lhsLift
  have hrEval : E.rhs ⬝ φ = embed Γ p.rhsRep := occurrenceLift_eval_eq_embed p.rhsLift
  obtain ⟨d⟩ := hcompile E hE hE β φ p
  calc
    E.lhs ⬝ φ = embed Γ p.lhsRep := hlEval
    _ = embed Γ p.rhsRep := Quotient.sound ⟨d⟩
    _ = E.rhs ⬝ φ := hrEval.symm

/-- Completeness factors through occurrence-axiom compilation, with no support-retraction premise
in the theorem statement. -/
theorem Completeness'_occurrenceCompilers {α β : Type}
    {Γ : Ctx α} {E : MagmaLaw β}
    (hcompile : ∀ A, A ∈ Γ → OccurrenceAxiomCompiler Γ A)
    (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) := by
  apply FreeMagmaWithLaws.isDerives
  exact h _ (FreeMagmaWithLaws.isModel_occurrenceCompilers β Γ hcompile)

/-- Existing O10 support resources are sufficient to build the new compiler. This proves O38 is a
strict refactor of the generic residual, not an unrelated new goal: any old resource route maps into
it, while the converse is deliberately left open. -/
theorem occurrenceAxiomCompiler_of_supportResources {δ α : Type}
    (Γ : Ctx δ) (E : MagmaLaw α)
    (hret : SupportRetract E)
    (hlift : SupportQuotientLift Γ E) :
    OccurrenceAxiomCompiler Γ E := by
  intro hE β φ p
  obtain ⟨τ, hτ⟩ := totalSubst_of_supportResources Γ E φ hret hlift
  have dl : Nonempty (Γ ⊢' p.lhsRep ≃ E.lhs ⬝ τ) := by
    apply FreeMagmaWithLaws.eq.mp
    calc
      embed Γ p.lhsRep = E.lhs ⬝ φ := (occurrenceLift_eval_eq_embed p.lhsLift).symm
      _ = E.lhs ⬝ (embed Γ ∘ τ) := by
        apply FreeMagma.evalInMagma_congr
        intro a ha
        exact hτ a (.inl ha)
      _ = embed Γ (E.lhs ⬝ τ) := FreeMagmaWithLaws.evalInMagmaIsQuot Γ E.lhs τ
  have dr : Nonempty (Γ ⊢' E.rhs ⬝ τ ≃ p.rhsRep) := by
    apply FreeMagmaWithLaws.eq.mp
    calc
      embed Γ (E.rhs ⬝ τ) = E.rhs ⬝ (embed Γ ∘ τ) :=
        (FreeMagmaWithLaws.evalInMagmaIsQuot Γ E.rhs τ).symm
      _ = E.rhs ⬝ φ := by
        symm
        apply FreeMagma.evalInMagma_congr
        intro a ha
        exact hτ a (.inr ha)
      _ = embed Γ p.rhsRep := occurrenceLift_eval_eq_embed p.rhsLift
  obtain ⟨dl'⟩ := dl
  obtain ⟨dr'⟩ := dr
  exact ⟨derive'.Trans dl' (derive'.Trans (derive'.SubstAx hE τ) dr')⟩
