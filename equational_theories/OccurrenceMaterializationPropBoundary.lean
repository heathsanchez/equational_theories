import equational_theories.OccurrenceMaterializationEqualityBoundary

open FreeMagma

namespace FreeMagma

/-- Mere pairwise existence of a computational materializer, kept entirely in `Prop`. This is weaker
than a single Type-valued `TwoLeafMemPositionData α` function selecting materializers uniformly for
all pairs. -/
def PairwiseTwoLeafMaterialization (α : Type) : Prop :=
  ∀ a b : α, Nonempty (MemPositionData (Lf a ⋆ Lf b))

/-- One concrete materializer for the two-leaf term decides the equality proposition for its two
labels. The conclusion stays in `Prop`, so there is no global Type-valued decision function here. -/
theorem eqOrNe_of_twoLeafMemPositionData {α : Type} (a b : α)
    (d : MemPositionData (Lf a ⋆ Lf b)) : a = b ∨ a ≠ b := by
  let pa := d.locate a (.inl rfl)
  let pb := d.locate b (.inr rfl)
  match twoLeafPosDecidableEq a b pa pb with
  | isTrue hp =>
      left
      have ha : occurrenceLabel (Lf a ⋆ Lf b) pa = a := d.label_locate a (.inl rfl)
      have hb : occurrenceLabel (Lf a ⋆ Lf b) pb = b := d.label_locate b (.inr rfl)
      rw [hp] at ha
      exact ha.symm.trans hb
  | isFalse hne =>
      right
      intro hab
      subst b
      have hproof :
          (show Mem a (Lf a ⋆ Lf a) from .inl rfl) = (.inr rfl) :=
        Subsingleton.elim _ _
      have hpos :
          d.locate a (.inl rfl) = d.locate a (.inr rfl) :=
        congrArg (d.locate a) hproof
      exact hne hpos

/-- If a materializer merely exists for each pair, equality is propositionally separable for each
pair. This is the Prop-level analogue of O17's stronger uniform-data result. -/
theorem equalitySplit_of_pairwiseTwoLeafMaterialization {α : Type}
    (h : PairwiseTwoLeafMaterialization α) :
    ∀ a b : α, a = b ∨ a ≠ b := by
  intro a b
  obtain ⟨d⟩ := h a b
  exact eqOrNe_of_twoLeafMemPositionData a b d

/-- A Type-valued decidable-equality resource supplies pairwise materializer existence, but the
reverse Type-valued extraction is deliberately not claimed. -/
theorem pairwiseTwoLeafMaterialization_of_nonempty_decidableEq {α : Type}
    (h : Nonempty (DecidableEq α)) : PairwiseTwoLeafMaterialization α := by
  obtain ⟨deq⟩ := h
  letI : DecidableEq α := deq
  intro a b
  exact ⟨memPositionData_of_decidableEq (Lf a ⋆ Lf b)⟩

/-- Uniform Type-valued two-leaf materialization also implies the weaker pairwise Prop existence. -/
theorem pairwiseTwoLeafMaterialization_of_uniform {α : Type}
    (d : TwoLeafMemPositionData α) : PairwiseTwoLeafMaterialization α := by
  intro a b
  exact ⟨d a b⟩

end FreeMagma
