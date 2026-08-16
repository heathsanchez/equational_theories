import equational_theories.SupportFiniteChoiceBoundary

open FreeMagma
open Law

/-- With no axioms, `derive'` relates only literally equal free-magma terms. Written by recursion on
the indexed derivation so the endpoint indices remain generalized. -/
theorem derive'_empty_eq {α β : Type} :
    ∀ {x y : FreeMagma β}, (∅ : Ctx α) ⊢' x ≃ y → x = y
  | _, _, .SubstAx h _ => False.elim h
  | _, _, .Ref => rfl
  | _, _, .Sym d => (derive'_empty_eq d).symm
  | _, _, .Trans d₁ d₂ => (derive'_empty_eq d₁).trans (derive'_empty_eq d₂)
  | _, _, .Cong d₁ d₂ => congrArg₂ FreeMagma.Fork (derive'_empty_eq d₁) (derive'_empty_eq d₂)

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

theorem FreeMagmaWithLaws.embed_unembedEmpty {α β : Type}
    (q : FreeMagmaWithLaws β (∅ : Ctx α)) :
    embed (∅ : Ctx α) (FreeMagmaWithLaws.unembedEmpty q) = q := by
  induction q using FreeMagmaWithLaws.inductionOn with
  | h t => rfl

theorem supportQuotientLift_empty {α δ : Type} (E : MagmaLaw α) :
    SupportQuotientLift (∅ : Ctx δ) E := by
  intro β φ
  refine ⟨fun a _ => FreeMagmaWithLaws.unembedEmpty (φ a), ?_⟩
  intro a ha
  exact (FreeMagmaWithLaws.embed_unembedEmpty (φ a)).symm

theorem supportIndexedQuotientSection_empty {α δ : Type} (E : MagmaLaw α) :
    SupportIndexedQuotientSection (∅ : Ctx δ) E :=
  (supportQuotientLift_iff_supportIndexedSection (∅ : Ctx δ) E).1
    (supportQuotientLift_empty E)

theorem universalEqualitySplit_of_emptyLiftImpliesSplit
    (H : ∀ (α : Type) (a b : α),
      SupportQuotientLift (∅ : Ctx PUnit) (twoLeafSupportLaw a b) → a = b ∨ a ≠ b) :
    ∀ (α : Type) (a b : α), a = b ∨ a ≠ b := by
  intro α a b
  exact H α a b (supportQuotientLift_empty (twoLeafSupportLaw a b))
