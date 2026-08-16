import equational_theories.CompletenessFiniteSupport

/-- A one-point override operator gives a constructive weak equality separator:
for any two keys, either they are unequal or equality is double-negation stable at that pair.

This is the exact obstruction exposed by the finite-support completeness construction. The usual
finite-map adapter wants to start from a total default function and override arbitrary support keys.
Without an equality principle, the Boolean observation can separate definite inequality from
`¬¬`-equality, but cannot construct an equality proof from the latter. -/
theorem weakEqDecision_of_onePointOverride
    (α : Type)
    (override : α → Bool → Bool → (α → Bool))
    (at_key : ∀ x d v, override x d v x = v)
    (off_key : ∀ x d v y, y ≠ x → override x d v y = d) :
    ∀ a b : α, (a ≠ b) ∨ ¬¬(a = b) := by
  intro a b
  cases h : override a false true b with
  | false =>
      left
      intro hab
      subst b
      have hat := at_key a false true
      rw [hat] at h
      contradiction
  | true =>
      right
      intro hne
      have hba : b ≠ a := by
        intro hba
        exact hne hba.symm
      have hoff := off_key a false true b hba
      rw [hoff] at h
      contradiction

/-- If equality is stable (`¬¬(a=b) -> a=b`), the same override primitive yields the
*propositional* equality split `(a=b) ∨ (a≠b)`.

This deliberately does not claim `DecidableEq α`: converting a proof-level disjunction in `Prop`
into Type-valued `Decidable (a=b)` is a separate extraction step, and Lean correctly forbids that
elimination constructively. -/
theorem eqOrNe_of_onePointOverride_of_stableEq
    (α : Type)
    (override : α → Bool → Bool → (α → Bool))
    (at_key : ∀ x d v, override x d v x = v)
    (off_key : ∀ x d v y, y ≠ x → override x d v y = d)
    (stableEq : ∀ a b : α, ¬¬(a = b) → a = b) :
    ∀ a b : α, (a = b) ∨ (a ≠ b) := by
  intro a b
  rcases weakEqDecision_of_onePointOverride α override at_key off_key a b with hne | hnne
  · exact Or.inr hne
  · exact Or.inl (stableEq a b hnne)
