import equational_theories.CompletenessFiniteSupport

open FreeMagma
open Law

/-- `OccurrenceLift Γ φ t u` says that `u` is obtained from `t` by choosing a quotient
representative independently at each leaf occurrence. No equality test on source variables is
needed: repeated occurrences of the same source variable are allowed to choose different but
quotient-equivalent representatives. -/
inductive OccurrenceLift {δ α β : Type} (Γ : Ctx δ)
    (φ : α → FreeMagmaWithLaws β Γ) : FreeMagma α → FreeMagma β → Prop
  | leaf (x : α) (r : FreeMagma β) (h : φ x = embed Γ r) :
      OccurrenceLift Γ φ (Lf x) r
  | fork {l r : FreeMagma α} {l' r' : FreeMagma β}
      (hl : OccurrenceLift Γ φ l l')
      (hr : OccurrenceLift Γ φ r r') :
      OccurrenceLift Γ φ (l ⋆ r) (l' ⋆ r')

/-- Every finite FreeMagma term admits an occurrence-local lift of a quotient-valued valuation.
This is structural finite choice, proved inside `Prop`; it does not require `DecidableEq` or a
global representative function. -/
theorem occurrenceLift_exists {δ α β : Type} (Γ : Ctx δ)
    (φ : α → FreeMagmaWithLaws β Γ) :
    ∀ t : FreeMagma α, ∃ u : FreeMagma β, OccurrenceLift Γ φ t u := by
  intro t
  induction t with
  | Leaf x =>
      obtain ⟨r, hr⟩ := Quotient.exists_rep (φ x)
      exact ⟨r, OccurrenceLift.leaf x r hr.symm⟩
  | Fork l r ihl ihr =>
      obtain ⟨l', hl⟩ := ihl
      obtain ⟨r', hr⟩ := ihr
      exact ⟨l' ⋆ r', OccurrenceLift.fork hl hr⟩

/-- An occurrence-local lift evaluates to exactly the original quotient-valued evaluation. -/
theorem occurrenceLift_eval_eq_embed {δ α β : Type} {Γ : Ctx δ}
    {φ : α → FreeMagmaWithLaws β Γ} {t : FreeMagma α} {u : FreeMagma β}
    (h : OccurrenceLift Γ φ t u) :
    t ⬝ φ = embed Γ u := by
  induction h with
  | leaf x r hr =>
      simpa [FreeMagma.evalInMagma] using hr
  | fork hl hr ihl ihr =>
      simp only [FreeMagma.evalInMagma]
      rw [ihl, ihr]
      exact (embed_fork Γ _ _).symm

/-- Combined form: every term evaluation in the quotient has a representative with the same tree
shape as the source term, obtained without any source-variable equality assumption. -/
theorem eval_has_occurrence_rep {δ α β : Type} (Γ : Ctx δ)
    (φ : α → FreeMagmaWithLaws β Γ) (t : FreeMagma α) :
    ∃ u : FreeMagma β, t ⬝ φ = embed Γ u := by
  obtain ⟨u, hu⟩ := occurrenceLift_exists Γ φ t
  exact ⟨u, occurrenceLift_eval_eq_embed hu⟩

/-- Representatives independently chosen for two occurrences of the same source variable are
already coherent in the quotient: they are derivably equal from `Γ`. Thus O6 obtains proof-level
coherence without choosing a canonical representative. -/
theorem occurrence_representatives_derivably_equal {δ α β : Type} {Γ : Ctx δ}
    {φ : α → FreeMagmaWithLaws β Γ} {x : α} {r s : FreeMagma β}
    (hr : φ x = embed Γ r) (hs : φ x = embed Γ s) :
    Nonempty (Γ ⊢' r ≃ s) := by
  apply FreeMagmaWithLaws.eq.mp
  exact hr.symm.trans hs
