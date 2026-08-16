import equational_theories.SupportFiniteChoiceBoundary

open FreeMagma
open Law

/-- Arbitrary Type-family choice over a law's propositionally described support is exactly the mere
existence of a computational map sending each support variable to one matching syntax occurrence.
The equivalence itself remains in `Prop`. -/
theorem supportFamilyChoice_iff_nonempty_positionData {α : Type} (E : MagmaLaw α) :
    SupportFamilyChoice E ↔ Nonempty (LawSupportPositionData E) := by
  constructor
  · intro hchoice
    let t := E.occurrenceTree
    let P : {a : α // E.Mem a} → Type := fun s =>
      {p : OccurrencePos t // occurrenceLabel t p = s.1}
    have hP : ∀ s, Nonempty (P s) := by
      intro s
      have hm : Mem s.1 t := s.2
      simpa [P, t] using mem_has_occurrence_position s.1 t hm
    obtain ⟨g⟩ := hchoice P hP
    refine ⟨{
      locate := fun a ha => (g ⟨a, ha⟩).1
      label_locate := ?_ }⟩
    intro a ha
    exact (g ⟨a, ha⟩).2
  · rintro ⟨pos⟩
    intro P hP
    let t := E.occurrenceTree
    let Q : OccurrencePos t → Type := fun p =>
      P ⟨occurrenceLabel t p, occurrenceLabel_mem t p⟩
    have hQ : ∀ p, Nonempty (Q p) := by
      intro p
      exact hP ⟨occurrenceLabel t p, occurrenceLabel_mem t p⟩
    obtain ⟨g⟩ := chooseOccurrenceFamily t Q hQ
    refine ⟨fun s => ?_⟩
    let p := pos.locate s.1 s.2
    have hp : occurrenceLabel t p = s.1 := pos.label_locate s.1 s.2
    have hs : (⟨occurrenceLabel t p, occurrenceLabel_mem t p⟩ : {x // E.Mem x}) = s := by
      apply Subtype.ext
      exact hp
    exact hs ▸ g p

/-- Consequently O16's occurrence-materialization route and the abstract support-family-choice
resource are equivalent at the proposition/existence level. -/
theorem nonempty_positionData_iff_supportFamilyChoice {α : Type} (E : MagmaLaw α) :
    Nonempty (LawSupportPositionData E) ↔ SupportFamilyChoice E :=
  (supportFamilyChoice_iff_nonempty_positionData E).symm

/-- The exact resource immediately yields the special quotient-representative selector used by O10. -/
theorem supportQuotientLift_of_nonempty_positionData {δ α : Type}
    (Γ : Ctx δ) (E : MagmaLaw α)
    (hpos : Nonempty (LawSupportPositionData E)) :
    SupportQuotientLift Γ E := by
  apply supportQuotientLift_of_supportFamilyChoice Γ E
  exact (supportFamilyChoice_iff_nonempty_positionData E).2 hpos
