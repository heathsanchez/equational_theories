import equational_theories.OccurrencePositionBoundary
import equational_theories.CompletenessSupportResources
import equational_theories.SupportLocalConservativity

open FreeMagma
open Law

def chooseOccurrenceFamily {α : Type} :
    (t : FreeMagma α) →
    (P : FreeMagma.OccurrencePos t → Type) →
    (∀ p, Nonempty (P p)) →
    Nonempty (∀ p, P p)
  | FreeMagma.Leaf _, P, h => by
      obtain ⟨x⟩ := h PUnit.unit
      exact ⟨fun p => by cases p; exact x⟩
  | FreeMagma.Fork l r, P, h => by
      let PL : FreeMagma.OccurrencePos l → Type := fun p => P (Sum.inl p)
      let PR : FreeMagma.OccurrencePos r → Type := fun p => P (Sum.inr p)
      obtain ⟨gl⟩ := chooseOccurrenceFamily l PL (fun p => h (Sum.inl p))
      obtain ⟨gr⟩ := chooseOccurrenceFamily r PR (fun p => h (Sum.inr p))
      exact ⟨fun p => match p with
        | Sum.inl q => gl q
        | Sum.inr q => gr q⟩

def Law.MagmaLaw.occurrenceTree {α : Type} (E : MagmaLaw α) : FreeMagma α :=
  E.lhs ⋆ E.rhs

abbrev LawSupportPositionData {α : Type} (E : MagmaLaw α) :=
  FreeMagma.MemPositionData E.occurrenceTree

theorem lawMem_iff_occurrenceTreeMem {α : Type} {E : MagmaLaw α} {a : α} :
    E.Mem a ↔ FreeMagma.Mem a E.occurrenceTree := by
  rfl

theorem supportQuotientLift_of_positionData {δ α : Type}
    (Γ : Ctx δ) (E : MagmaLaw α) (pos : LawSupportPositionData E) :
    SupportQuotientLift Γ E := by
  intro β φ
  let t := E.occurrenceTree
  let P : FreeMagma.OccurrencePos t → Type := fun p =>
    {r : FreeMagma β // φ (FreeMagma.occurrenceLabel t p) = embed Γ r}
  have hP : ∀ p, Nonempty (P p) := by
    intro p
    obtain ⟨r, hr⟩ := Quotient.exists_rep (φ (FreeMagma.occurrenceLabel t p))
    exact ⟨⟨r, hr.symm⟩⟩
  obtain ⟨g⟩ := chooseOccurrenceFamily t P hP
  refine ⟨fun a ha => ?_, ?_⟩
  · have hm : FreeMagma.Mem a t := (lawMem_iff_occurrenceTreeMem).1 ha
    exact (g (pos.locate a hm)).1
  · intro a ha
    have hm : FreeMagma.Mem a t := (lawMem_iff_occurrenceTreeMem).1 ha
    let p := pos.locate a hm
    have hp := (g p).2
    have hlabel : FreeMagma.occurrenceLabel t p = a := pos.label_locate a hm
    simpa [p, hlabel] using hp

structure ComputableLawSupport {α : Type} (E : MagmaLaw α) where
  positions : LawSupportPositionData E
  retract : SupportRetractionData E

def ContextComputableLawSupport {α : Type} (Γ : Ctx α) : Type :=
  (E : MagmaLaw α) → E ∈ Γ → ComputableLawSupport E

theorem computableLawSupport_resources {α : Type} {Γ : Ctx α}
    (h : ContextComputableLawSupport Γ) :
    (∀ E, E ∈ Γ → SupportRetract E) ∧
    (∀ E, E ∈ Γ → SupportQuotientLift Γ E) := by
  constructor
  · intro E hE
    exact (h E hE).retract.toSupportRetract
  · intro E hE
    exact supportQuotientLift_of_positionData Γ E (h E hE).positions

theorem FreeMagmaWithLaws.isModel_occurrenceMaterialized {α : Type}
    (β : Type) (Γ : Ctx α) (h : ContextComputableLawSupport Γ) :
    FreeMagmaWithLaws β Γ ⊧ Γ := by
  obtain ⟨hret, hlift⟩ := computableLawSupport_resources h
  exact FreeMagmaWithLaws.isModel_supportResources β Γ hret hlift

theorem Completeness'_occurrenceMaterialized {α β : Type}
    {Γ : Ctx α} {E : MagmaLaw β}
    (hdata : ContextComputableLawSupport Γ)
    (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) := by
  obtain ⟨hret, hlift⟩ := computableLawSupport_resources hdata
  exact Completeness'_supportResources hret hlift h

def computableLawSupport_of_decidableEq {α : Type} [DecidableEq α]
    (E : MagmaLaw α) : ComputableLawSupport E where
  positions := FreeMagma.memPositionData_of_decidableEq E.occurrenceTree
  retract := supportRetractionData_of_decidableEq E
