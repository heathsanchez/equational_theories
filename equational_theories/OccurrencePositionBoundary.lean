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

/-- Direct structural decidability of `FreeMagma.Mem` from equality decisions. This deliberately
avoids `elems`, deduplication, and `finEquiv`. -/
def memDecidable {α : Type} [DecidableEq α] (a : α) :
    (t : FreeMagma α) → Decidable (Mem a t)
  | Lf b => inferInstance
  | l ⋆ r =>
      match memDecidable a l with
      | isTrue hl => isTrue (.inl hl)
      | isFalse hnl =>
          match memDecidable a r with
          | isTrue hr => isTrue (.inr hr)
          | isFalse hnr => isFalse (by
              intro h
              rcases h with hl | hr
              · exact hnl hl
              · exact hnr hr)

/-- Search the finite syntax for an actual matching position. The membership proof is used only to
rule out the impossible no-match branch; the left/right computational branch is chosen by the
structural decision procedure above. -/
def memPosition_of_decidableEq {α : Type} [DecidableEq α] (a : α) :
    (t : FreeMagma α) → Mem a t → OccurrencePos t
  | Lf _, _ => PUnit.unit
  | l ⋆ r, h =>
      match memDecidable a l with
      | isTrue hl => Sum.inl (memPosition_of_decidableEq a l hl)
      | isFalse hnl => Sum.inr (memPosition_of_decidableEq a r (Or.resolve_left h hnl))

/-- The structural search really lands on a position carrying the requested variable label. -/
theorem occurrenceLabel_memPosition_of_decidableEq {α : Type} [DecidableEq α] (a : α) :
    ∀ (t : FreeMagma α) (h : Mem a t),
      occurrenceLabel t (memPosition_of_decidableEq a t h) = a
  | Lf b, h => h.symm
  | l ⋆ r, h => by
      unfold memPosition_of_decidableEq
      cases hdec : memDecidable a l with
      | isTrue hl =>
          simpa [hdec, occurrenceLabel] using occurrenceLabel_memPosition_of_decidableEq a l hl
      | isFalse hnl =>
          have hr : Mem a r := Or.resolve_left h hnl
          simpa [hdec, occurrenceLabel] using occurrenceLabel_memPosition_of_decidableEq a r hr

/-- Type-valued materialization of every `Mem` witness into an actual occurrence position. This is
strictly stronger data than `mem_has_occurrence_position`, whose conclusion is only `Nonempty`. -/
structure MemPositionData {α : Type} (t : FreeMagma α) where
  locate : (a : α) → Mem a t → OccurrencePos t
  label_locate : ∀ a h, occurrenceLabel t (locate a h) = a

/-- Decidable equality supplies computational materialization by searching the finite term by label,
without `elems`, `finEquiv`, or proposition-to-Type elimination of the membership witness. -/
def memPositionData_of_decidableEq {α : Type} [DecidableEq α]
    (t : FreeMagma α) : MemPositionData t where
  locate := fun a h => memPosition_of_decidableEq a t h
  label_locate := fun a h => occurrenceLabel_memPosition_of_decidableEq a t h

/-- A computational position always gives back a proposition-level membership witness for its
label; no equality decision is involved. -/
theorem mem_of_occurrence_position {α : Type} {t : FreeMagma α}
    (p : OccurrencePos t) : Mem (occurrenceLabel t p) t :=
  occurrenceLabel_mem t p

end FreeMagma
