import equational_theories.SupportQuotientLiftNormalForm
import equational_theories.CompletenessOccurrenceMaterialization
import equational_theories.OccurrenceMaterializationPropBoundary

open FreeMagma
open Law

/-- Type-valued family choice over the propositionally described support of one law, with the
result kept under `Nonempty` so the whole principle itself lives in `Prop`. -/
def SupportFamilyChoice {α : Type} (E : MagmaLaw α) : Prop :=
  ∀ (P : {a : α // E.Mem a} → Type),
    (∀ s, Nonempty (P s)) → Nonempty (∀ s, P s)

/-- Abstract support-family choice is sufficient to obtain O10's support-indexed quotient section:
each support variable individually has a quotient representative, and the family-choice principle
assembles them coherently into one support-indexed function. -/
theorem supportIndexedSection_of_supportFamilyChoice {δ α : Type}
    (Γ : Ctx δ) (E : MagmaLaw α) (hchoice : SupportFamilyChoice E) :
    SupportIndexedQuotientSection Γ E := by
  intro β φ
  let P : {a : α // E.Mem a} → Type := fun s =>
    {r : FreeMagma β // φ s.1 = embed Γ r}
  have hP : ∀ s, Nonempty (P s) := by
    intro s
    obtain ⟨r, hr⟩ := Quotient.exists_rep (φ s.1)
    exact ⟨⟨r, hr.symm⟩⟩
  obtain ⟨g⟩ := hchoice P hP
  exact ⟨fun s => (g s).1, fun s => (g s).2⟩

/-- Hence support-family choice supplies the quotient-lifting half of O10. -/
theorem supportQuotientLift_of_supportFamilyChoice {δ α : Type}
    (Γ : Ctx δ) (E : MagmaLaw α) (hchoice : SupportFamilyChoice E) :
    SupportQuotientLift Γ E :=
  (supportQuotientLift_iff_supportIndexedSection Γ E).2
    (supportIndexedSection_of_supportFamilyChoice Γ E hchoice)

/-- The smallest nontrivial support: a law whose combined occurrence tree is exactly two leaves. -/
def twoLeafSupportLaw {α : Type} (a b : α) : MagmaLaw α :=
  (Lf a) ≃ (Lf b)

/-- Family choice over just the support of the two-leaf law already lets us materialize every known
membership witness into a concrete left/right occurrence position. -/
theorem twoLeafMemPositionData_of_supportFamilyChoice {α : Type} (a b : α)
    (hchoice : SupportFamilyChoice (twoLeafSupportLaw a b)) :
    MemPositionData (Lf a ⋆ Lf b) := by
  let E := twoLeafSupportLaw a b
  let t : FreeMagma α := Lf a ⋆ Lf b
  let P : {x : α // E.Mem x} → Type := fun s =>
    {p : OccurrencePos t // occurrenceLabel t p = s.1}
  have hP : ∀ s, Nonempty (P s) := by
    intro s
    have hm : Mem s.1 t := by
      exact s.2
    simpa [P, t] using mem_has_occurrence_position s.1 t hm
  obtain ⟨g⟩ := hchoice P hP
  refine {
    locate := fun x hx => (g ⟨x, hx⟩).1
    label_locate := ?_ }
  intro x hx
  exact (g ⟨x, hx⟩).2

/-- Decision-changing boundary: the apparently innocuous ability to choose a Type-valued family
over a propositionally finite two-leaf support already separates equality of those two labels. -/
theorem eqOrNe_of_twoLeafSupportFamilyChoice {α : Type} (a b : α)
    (hchoice : SupportFamilyChoice (twoLeafSupportLaw a b)) :
    a = b ∨ a ≠ b := by
  exact eqOrNe_of_twoLeafMemPositionData a b
    (twoLeafMemPositionData_of_supportFamilyChoice a b hchoice)

/-- A genuine decidable-equality resource supplies support-family choice via O15/O16 occurrence
materialization and structural finite choice. -/
theorem supportFamilyChoice_of_decidableEq {α : Type} [DecidableEq α]
    (E : MagmaLaw α) : SupportFamilyChoice E := by
  intro P hP
  let t := E.occurrenceTree
  let pos : LawSupportPositionData E := memPositionData_of_decidableEq t
  let Q : OccurrencePos t → Type := fun p => P ⟨occurrenceLabel t p, occurrenceLabel_mem t p⟩
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
