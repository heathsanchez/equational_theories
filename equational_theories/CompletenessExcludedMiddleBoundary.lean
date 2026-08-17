import equational_theories.CompletenessSupportResources

open FreeMagma
open Law

/-- An explicit excluded-middle principle, separated from Lean's standard `Classical` namespace so
we can audit the logical strength of the completeness route without smuggling in
`Classical.choice`. -/
def ExplicitExcludedMiddle : Prop := ∀ p : Prop, p ∨ ¬ p

/-- Explicit excluded middle supplies equality decisions for any type, constructively relative to
the supplied principle. No choice operation is used here. -/
def decidableEq_of_explicitExcludedMiddle (hem : ExplicitExcludedMiddle) (α : Type) :
    DecidableEq α := fun a b =>
  match hem (a = b) with
  | .inl h => isTrue h
  | .inr h => isFalse h

/-- O40 model boundary: if excluded middle is supplied as an independent logical principle, the
existing O10 support-resource route builds the free quotient model without any use of
`Classical.choice` in the theorem body. -/
theorem FreeMagmaWithLaws.isModel_of_explicitExcludedMiddle {α : Type}
    (hem : ExplicitExcludedMiddle) (β : Type) (Γ : Ctx α) :
    FreeMagmaWithLaws β Γ ⊧ Γ := by
  letI : DecidableEq α := decidableEq_of_explicitExcludedMiddle hem α
  exact FreeMagmaWithLaws.isModel_decidableVars_via_resources β Γ

/-- O40 logical factorization of #499. Relative to an explicit excluded-middle principle,
completeness follows through support resources. The theorem is intended to test whether choice is
logically stronger than what this route actually consumes. -/
theorem Completeness'_of_explicitExcludedMiddle {α β : Type}
    (hem : ExplicitExcludedMiddle) {Γ : Ctx α} {E : MagmaLaw β}
    (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) := by
  apply FreeMagmaWithLaws.isDerives
  exact h _ (FreeMagmaWithLaws.isModel_of_explicitExcludedMiddle hem β Γ)
