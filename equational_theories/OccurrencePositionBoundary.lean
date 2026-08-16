import equational_theories.FreeMagma

open FreeMagma

namespace FreeMagma

/-- Computational leaf positions of a finite magma term. Unlike `Mem`, this lives in `Type` and
uses `Sum` rather than proposition-level `Or`. -/
def OccurrencePos {α : Type} : FreeMagma α → Type
  | Lf _ => PUnit
  | l ⋆ r => OccurrencePos l ⊕ OccurrencePos r

/-- The variable label found at a computational occurrence position. -/
def occurrenceLabel {α : Type} : (t : FreeMagma α) → OccurrencePos t → α
  | Lf a, _ => a
  | l ⋆ _, Sum.inl p => occurrenceLabel l p
  | _ ⋆ r, Sum.inr p => occurrenceLabel r p

/-- Every computational position certifies ordinary proposition-level membership. -/
theorem occurrenceLabel_mem {α : Type} :
    ∀ (t : FreeMagma α) (p : OccurrencePos t), Mem (occurrenceLabel t p) t
  | Lf _, _ => rfl
  | l ⋆ _, Sum.inl p => .inl (occurrenceLabel_mem l p)
  | _ ⋆ r, Sum.inr p => .inr (occurrenceLabel_mem r p)

/-- Proposition-level membership always proves that a matching computational position exists.
The result deliberately remains under `Nonempty`: eliminating `Mem`'s `Or` directly into a
Type-valued position is exactly the representation boundary being tested. -/
theorem mem_has_occurrence_position {α : Type} (a : α) :
    ∀ t : FreeMagma α, Mem a t → Nonempty {p : OccurrencePos t // occurrenceLabel t p = a}
  | Lf b, h => by
      refine ⟨⟨PUnit.unit, ?_⟩⟩
      exact h.symm
  | l ⋆ r, h => by
      rcases h with hl | hr
      · obtain ⟨⟨p, hp⟩⟩ := mem_has_occurrence_position a l hl
        exact ⟨⟨Sum.inl p, hp⟩⟩
      · obtain ⟨⟨p, hp⟩⟩ := mem_has_occurrence_position a r hr
        exact ⟨⟨Sum.inr p, hp⟩⟩

/-- Type-valued materialization of every `Mem` witness into an actual occurrence position. This is
strictly stronger data than `mem_has_occurrence_position`, whose conclusion is only `Nonempty`. -/
structure MemPositionData {α : Type} (t : FreeMagma α) where
  locate : (a : α) → Mem a t → OccurrencePos t
  label_locate : ∀ a h, occurrenceLabel t (locate a h) = a

/-- Decidable equality supplies computational materialization by searching the finite term by label,
without eliminating the proposition-level `Or` witness into `Type`. -/
def memPositionData_of_decidableEq {α : Type} [DecidableEq α] :
    (t : FreeMagma α) → MemPositionData t
  | Lf b =>
      { locate := fun _ _ => PUnit.unit
        label_locate := by
          intro a h
          exact h.symm }
  | l ⋆ r => by
      let dl := memPositionData_of_decidableEq l
      let dr := memPositionData_of_decidableEq r
      refine {
        locate := fun a h =>
          if hl : Mem a l then Sum.inl (dl.locate a hl)
          else Sum.inr (dr.locate a (by
            rcases h with hl' | hr
            · exact False.elim (hl hl')
            · exact hr))
        label_locate := ?_ }
      intro a h
      split
      next hl => exact dl.label_locate a hl
      next hnl =>
        have hr : Mem a r := by
          rcases h with hl | hr
          · exact False.elim (hnl hl)
          · exact hr
        exact dr.label_locate a hr

/-- A computational position always gives back a proposition-level membership witness for its
label; no equality decision is involved. -/
theorem mem_of_occurrence_position {α : Type} {t : FreeMagma α}
    (p : OccurrencePos t) : Mem (occurrenceLabel t p) t :=
  occurrenceLabel_mem t p

end FreeMagma
