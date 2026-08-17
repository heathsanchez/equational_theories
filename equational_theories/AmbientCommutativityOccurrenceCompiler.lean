import equational_theories.OccurrenceAxiomCompilerBoundary
import equational_theories.AmbientCommutativityResourceCompleteness

open FreeMagma
open Law

/-- O39 information route: construct the O38 compiler for the two-variable ambient commutativity
law directly from occurrence-local representatives, without invoking `SupportRetract` or
`SupportQuotientLift`.

The proof deliberately exposes whether ordinary `derive'.SubstAx` still forces a total source
substitution internally. -/
theorem occurrenceAxiomCompiler_ambientCommutativity (κ : Type) :
    OccurrenceAxiomCompiler (ambientCommutativityCtx κ) (ambientCommutativityLaw κ) := by
  intro hE β φ p
  rcases p with ⟨lhsRep, rhsRep, lhsLift, rhsLift⟩
  cases lhsLift with
  | fork hl0 hl1 =>
    cases hl0 with
    | leaf _ l0 h0L =>
      cases hl1 with
      | leaf _ l1 h1L =>
        cases rhsLift with
        | fork hr1 hr0 =>
          cases hr1 with
          | leaf _ r1 h1R =>
            cases hr0 with
            | leaf _ r0 h0R =>
              have d0 : Nonempty (ambientCommutativityCtx κ ⊢' l0 ≃ r0) :=
                occurrence_representatives_derivably_equal h0L h0R
              have d1 : Nonempty (ambientCommutativityCtx κ ⊢' l1 ≃ r1) :=
                occurrence_representatives_derivably_equal h1L h1R
              obtain ⟨d0'⟩ := d0
              obtain ⟨d1'⟩ := d1
              let τ : Bool ⊕ κ → FreeMagma β := fun x =>
                match x with
                | Sum.inl false => l0
                | Sum.inl true => l1
                | Sum.inr _ => l0
              have dax : ambientCommutativityCtx κ ⊢'
                  (l0 ⋆ l1) ≃ (l1 ⋆ l0) := by
                simpa [ambientCommutativityLaw, τ] using
                  (derive'.SubstAx hE τ)
              exact ⟨derive'.Trans dax (derive'.Cong d1' d0')⟩

/-- The O38 completeness route can therefore be instantiated for the ambient commutativity context
using the direct occurrence compiler, with no support-resource premise in the final theorem. -/
theorem Completeness'_ambientCommutativity_occurrenceRoute {κ β : Type} {E : MagmaLaw β}
    (h : ambientCommutativityCtx κ ⊧ E) :
    Nonempty (ambientCommutativityCtx κ ⊢' E) := by
  apply Completeness'_occurrenceCompilers
  · intro A hA
    have hEq : A = ambientCommutativityLaw κ := by
      simpa [ambientCommutativityCtx] using hA
    subst A
    exact occurrenceAxiomCompiler_ambientCommutativity κ
  · exact h
