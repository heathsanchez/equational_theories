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

theorem supportQuotientLift_of_supportFamilyChoice {δ α : Type}
    (Γ : Ctx δ) (E : MagmaLaw α) (hchoice : SupportFamilyChoice E) :
    SupportQuotientLift Γ E :=
  (supportQuotientLift_iff_supportIndexedSection Γ E).2
    (supportIndexedSection_of_supportFamilyChoice Γ E hchoice)

def twoLeafSupportLaw {α : Type} (a b : α) : MagmaLaw α :=
  (Lf a) ≃ (Lf b)

/-- Correct Prop-level consequence of support-family choice. The failed stronger version returned an
actual `MemPositionData` object and was rejected because `Nonempty` cannot eliminate into `Type`. -/
theorem nonempty_twoLeafMemPositionData_of_supportFamilyChoice {α : Type} (a b : α)
    (hchoice : SupportFamilyChoice (twoLeafSupportLaw a b)) :
    Nonempty (MemPositionData (Lf a ⋆ Lf b)) := by
  let E := twoLeafSupportLaw a b
  let t : FreeMagma α := Lf a ⋆ Lf b
  let P : {x : α // E.Mem x} → Type := fun s =>
    {p : OccurrencePos t // occurrenceLabel t p = s.1}
  have hP : ∀ s, Nonempty (P s) := by
    intro s
    have hm : Mem s.1 t := s.2
    simpa [P, t] using mem_has_occurrence_position s.1 t hm
  obtain ⟨g⟩ := hchoice P hP
  refine ⟨{
    locate := fun x hx => (g ⟨x, hx⟩).1
    label_locate := ?_ }⟩
  intro x hx
  exact (g ⟨x, hx⟩).2

/-- Even though the materializer remains under `Nonempty`, its existence is enough to separate the
two labels because this conclusion stays in `Prop`. -/
theorem eqOrNe_of_twoLeafSupportFamilyChoice {α : Type} (a b : α)
    (hchoice : SupportFamilyChoice (twoLeafSupportLaw a b)) :
    a = b ∨ a ≠ b := by
  obtain ⟨d⟩ := nonempty_twoLeafMemPositionData_of_supportFamilyChoice a b hchoice
  exact eqOrNe_of_twoLeafMemPositionData a b d

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
