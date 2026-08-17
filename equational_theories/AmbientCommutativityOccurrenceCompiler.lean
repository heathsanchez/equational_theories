import equational_theories.OccurrenceAxiomCompilerBoundary
import equational_theories.AmbientCommutativityResourceCompleteness

open FreeMagma
open Law

/-- O39 information route: construct the O38 compiler for the two-variable ambient commutativity
law directly from occurrence-local representatives, without invoking `SupportRetract` or
`SupportQuotientLift`.

The proof uses occurrence packages only through their verified evaluation interface. It deliberately
exposes that ordinary `derive'.SubstAx` still consumes a total source substitution internally. -/
theorem occurrenceAxiomCompiler_ambientCommutativity (κ : Type) :
    OccurrenceAxiomCompiler (ambientCommutativityCtx κ) (ambientCommutativityLaw κ) := by
  intro hE β φ p
  obtain ⟨a, ha⟩ := Quotient.exists_rep (φ (Sum.inl false))
  obtain ⟨b, hb⟩ := Quotient.exists_rep (φ (Sum.inl true))
  have ha' : φ (Sum.inl false) = embed (ambientCommutativityCtx κ) a := ha.symm
  have hb' : φ (Sum.inl true) = embed (ambientCommutativityCtx κ) b := hb.symm
  have dl : Nonempty (ambientCommutativityCtx κ ⊢' p.lhsRep ≃ (a ⋆ b)) := by
    apply FreeMagmaWithLaws.eq.mp
    calc
      embed (ambientCommutativityCtx κ) p.lhsRep =
          (ambientCommutativityLaw κ).lhs ⬝ φ :=
        (occurrenceLift_eval_eq_embed p.lhsLift).symm
      _ = φ (Sum.inl false) ⋆ φ (Sum.inl true) := by
        rfl
      _ = embed (ambientCommutativityCtx κ) a ⋆
          embed (ambientCommutativityCtx κ) b := by rw [ha', hb']
      _ = embed (ambientCommutativityCtx κ) (a ⋆ b) :=
        (embed_fork (ambientCommutativityCtx κ) a b).symm
  have dr : Nonempty (ambientCommutativityCtx κ ⊢' (b ⋆ a) ≃ p.rhsRep) := by
    apply FreeMagmaWithLaws.eq.mp
    calc
      embed (ambientCommutativityCtx κ) (b ⋆ a) =
          embed (ambientCommutativityCtx κ) b ⋆
            embed (ambientCommutativityCtx κ) a :=
        embed_fork (ambientCommutativityCtx κ) b a
      _ = φ (Sum.inl true) ⋆ φ (Sum.inl false) := by rw [hb', ha']
      _ = (ambientCommutativityLaw κ).rhs ⬝ φ := by
        rfl
      _ = embed (ambientCommutativityCtx κ) p.rhsRep :=
        occurrenceLift_eval_eq_embed p.rhsLift
  let τ : Bool ⊕ κ → FreeMagma β := fun x =>
    match x with
    | Sum.inl false => a
    | Sum.inl true => b
    | Sum.inr _ => a
  have dax : ambientCommutativityCtx κ ⊢' (a ⋆ b) ≃ (b ⋆ a) := by
    simpa [ambientCommutativityLaw, τ] using (derive'.SubstAx hE τ)
  obtain ⟨dl'⟩ := dl
  obtain ⟨dr'⟩ := dr
  exact ⟨derive'.Trans dl' (derive'.Trans dax dr')⟩

/-- Instantiate O38 completeness using the direct occurrence compiler, with no support-resource
premise in the final theorem. -/
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
