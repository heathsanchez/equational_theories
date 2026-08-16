import equational_theories.SupportFiniteChoiceBoundary

open FreeMagma
open Law

/-- With no axioms, `derive'` relates only literally equal free-magma terms. -/
theorem derive'_empty_eq {α β : Type} {x y : FreeMagma β}
    (d : (∅ : Ctx α) ⊢' x ≃ y) : x = y := by
  induction d with
  | @SubstAx E h σ =>
      exact False.elim h
  | Ref => rfl
  | Sym d ih => exact ih.symm
  | Trans d₁ d₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | Cong d₁ d₂ ih₁ ih₂ => exact congrArg₂ FreeMagma.Fork ih₁ ih₂

/-- Therefore the empty-theory quotient has a constructive representative function: its quotient
relation is literal equality, so quotient elimination back into `FreeMagma` is well-defined. -/
def FreeMagmaWithLaws.unembedEmpty {α β : Type} :
    FreeMagmaWithLaws β (∅ : Ctx α) → FreeMagma β :=
  Quotient.lift id (by
    intro x y h
    obtain ⟨d⟩ := h
    exact derive'_empty_eq d)

@[simp] theorem FreeMagmaWithLaws.unembedEmpty_embed {α β : Type}
    (t : FreeMagma β) :
    FreeMagmaWithLaws.unembedEmpty (α := α) (embed (∅ : Ctx α) t) = t := by
  rfl

/-- The constructive representative is a right inverse to `embed` on every empty-theory quotient
value. -/
theorem FreeMagmaWithLaws.embed_unembedEmpty {α β : Type}
    (q : FreeMagmaWithLaws β (∅ : Ctx α)) :
    embed (∅ : Ctx α) (FreeMagmaWithLaws.unembedEmpty q) = q := by
  induction q using FreeMagmaWithLaws.inductionOn with
  | h t => rfl

/-- Hence O10's quotient-lifting resource is available for every law over the empty theory, with no
support indexing, occurrence materialization, decidable equality, or choice. -/
theorem supportQuotientLift_empty {α δ : Type} (E : MagmaLaw α) :
    SupportQuotientLift (∅ : Ctx δ) E := by
  intro β φ
  refine ⟨fun a _ => FreeMagmaWithLaws.unembedEmpty (φ a), ?_⟩
  intro a ha
  exact (FreeMagmaWithLaws.embed_unembedEmpty (φ a)).symm

/-- Same fact in O20's normal form. -/
theorem supportIndexedQuotientSection_empty {α δ : Type} (E : MagmaLaw α) :
    SupportIndexedQuotientSection (∅ : Ctx δ) E :=
  (supportQuotientLift_iff_supportIndexedSection (∅ : Ctx δ) E).1
    (supportQuotientLift_empty E)

/-- Separator: any claimed generic implication from the empty-theory support quotient lift to an
`a=b ∨ a≠b` decision would immediately yield equality excluded middle for every Type. -/
theorem universalEqualitySplit_of_emptyLiftImpliesSplit
    (H : ∀ (α : Type) (a b : α),
      SupportQuotientLift (∅ : Ctx PUnit) (twoLeafSupportLaw a b) → a = b ∨ a ≠ b) :
    ∀ (α : Type) (a b : α), a = b ∨ a ≠ b := by
  intro α a b
  exact H α a b (supportQuotientLift_empty (twoLeafSupportLaw a b))
