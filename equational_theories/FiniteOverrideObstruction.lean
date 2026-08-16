import equational_theories.CompletenessFiniteSupport

/-- A one-point override operator on an arbitrary key type is already strong enough to decide key equality.

This isolates the obstruction in the finite-support completeness construction: any implementation that
starts from a total default function and overrides arbitrary keys while proving that all other keys
retain the default can only exist uniformly when equality on the key type is decidable.

This does *not* show that completeness itself requires `DecidableEq`; it shows that the current
"finite support -> total substitution by overrides" adapter does. -/
theorem decidableEq_of_onePointOverride
    (α : Type)
    (override : α → Bool → Bool → (α → Bool))
    (at_key : ∀ x d v, override x d v x = v)
    (off_key : ∀ x d v y, y ≠ x → override x d v y = d) :
    DecidableEq α := by
  intro a b
  by_cases h : override a false true b = true
  · apply isTrue
    by_contra hne
    have hoff := off_key a false true b hne
    rw [hoff] at h
    contradiction
  · apply isFalse
    intro hab
    subst b
    have hat := at_key a false true
    exact h hat
