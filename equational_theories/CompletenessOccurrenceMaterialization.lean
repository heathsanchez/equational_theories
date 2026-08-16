import equational_theories.OccurrencePositionBoundary
import equational_theories.CompletenessSupportResources
import equational_theories.SupportLocalConservativity

open FreeMagma
open Law

/-- Constructive finite Type-valued choice directly over the recursive occurrence-position type.
No support deduplication or equivalence to `Fin n` is needed. -/
def chooseOccurrenceFamily {α : Type} :
    (t : FreeMagma α) →
    (P : FreeMagma.OccurrencePos t → Type) →
    (∀ p, Nonempty (P p)) →
    Nonempty (∀ p, P p)
  | .Lf _, P, h => by
      obtain ⟨x⟩ := h PUnit.unit
      exact ⟨fun p => by cases p; exact x⟩
  | l ⋆ r, P, h => by
      let PL : FreeMagma.OccurrencePos l → Type := fun p => P (Sum.inl p)
      let PR : FreeMagma.OccurrencePos r → Type := fun p => P (Sum.inr p)
      obtain ⟨gl⟩ := chooseOccurrenceFamily l PL (fun p => h (Sum.inl p))
      obtain ⟨gr⟩ := chooseOccurrenceFamily r PR (fun p => h (Sum.inr p))
      exact ⟨fun p => match p with
        | Sum.inl q => gl q
        | Sum.inr q => gr q⟩

/-- One law's lhs/rhs occurrences packaged as a single finite syntax tree. -/
def Law.MagmaLaw.occurrenceTree {α : Type} (E : MagmaLaw α) : FreeMagma α :=
  E.lhs ⋆ E.rhs

/-- Computational materialization of every proposition-level law-support witness into a concrete
lhs/rhs occurrence. -/
abbrev LawSupportPositionData {α : Type} (E : MagmaLaw α) :=
  FreeMagma.MemPositionData E.occurrenceTree

/-- Law membership is definitionally the same proposition as membership in the combined occurrence
tree. -/
theorem lawMem_iff_occurrenceTreeMem {α : Type} {E : MagmaLaw α} {a : α} :
    E.Mem a ↔ FreeMagma.Mem a E.occurrenceTree := by
  rfl

/-- Occurrence materialization is enough to choose quotient representatives on every support
variable. Representatives are first chosen over finite *positions* structurally; `locate` then
assigns each support variable one such position. -/
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

/-- Exact computational resources for one context law: occurrence materialization plus the support
retraction data needed to totalize the support assignment at the old interface. -/
structure ComputableLawSupport {α : Type} (E : MagmaLaw α) where
  positions : LawSupportPositionData E
  retract : SupportRetractionData E

/-- Context-level resource bundle. -/
def ContextComputableLawSupport {α : Type} (Γ : Ctx α) : Type :=
  (E : MagmaLaw α) → E ∈ Γ → ComputableLawSupport E

/-- The occurrence-materialized resource bundle supplies O10's two exact completeness resources. -/
theorem computableLawSupport_resources {α : Type} {Γ : Ctx α}
    (h : ContextComputableLawSupport Γ) :
    (∀ E, E ∈ Γ → SupportRetract E) ∧
    (∀ E, E ∈ Γ → SupportQuotientLift Γ E) := by
  constructor
  · intro E hE
    exact (h E hE).retract.toSupportRetract
  · intro E hE
    exact supportQuotientLift_of_positionData Γ E (h E hE).positions

/-- Choice-free quotient-model construction from occurrence materialization + computational support
retraction, with no global `[DecidableEq α]` and no support-to-Fin equivalence. -/
theorem FreeMagmaWithLaws.isModel_occurrenceMaterialized {α : Type}
    (β : Type) (Γ : Ctx α) (h : ContextComputableLawSupport Γ) :
    FreeMagmaWithLaws β Γ ⊧ Γ := by
  obtain ⟨hret, hlift⟩ := computableLawSupport_resources h
  exact FreeMagmaWithLaws.isModel_supportResources β Γ hret hlift

/-- Type-0 completeness under occurrence materialization + computational support retraction. -/
theorem Completeness'_occurrenceMaterialized {α β : Type}
    {Γ : Ctx α} {E : MagmaLaw β}
    (hdata : ContextComputableLawSupport Γ)
    (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) := by
  obtain ⟨hret, hlift⟩ := computableLawSupport_resources hdata
  exact Completeness'_supportResources hret hlift h

/-- Decidable equality supplies the occurrence-materialization half directly from syntax and the
retraction half through O12. This recovers O4 through the more explicit computational interface. -/
def computableLawSupport_of_decidableEq {α : Type} [DecidableEq α]
    (E : MagmaLaw α) : ComputableLawSupport E where
  positions := FreeMagma.memPositionData_of_decidableEq E.occurrenceTree
  retract := supportRetractionData_of_decidableEq E
