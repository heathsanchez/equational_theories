import equational_theories.EmptyTheoryQuotientSection

open FreeMagma
open Law

/-- Computational canonical representative data for one term quotient. This resource is global in
quotient values but independent of any particular law support. -/
structure QuotientRepresentativeData {δ β : Type} (Γ : Ctx δ) where
  representative : FreeMagmaWithLaws β Γ → FreeMagma β
  embed_representative : ∀ q, embed Γ (representative q) = q

/-- Mere existence of a global quotient section, kept in `Prop`. -/
def QuotientRepresentativeSection {δ β : Type} (Γ : Ctx δ) : Prop :=
  Nonempty (QuotientRepresentativeData (β := β) Γ)

/-- A global computational quotient section supplies O10's support-indexed selector for every law,
without inspecting or indexing the law's support. -/
theorem supportQuotientLift_of_quotientRepresentativeData {δ α β0 : Type}
    (Γ : Ctx δ) (E : MagmaLaw α)
    (d : QuotientRepresentativeData (β := β0) Γ) :
    ∀ (φ : α → FreeMagmaWithLaws β0 Γ),
      ∃ σ : (a : α) → E.Mem a → FreeMagma β0,
        ∀ a h, φ a = embed Γ (σ a h) := by
  intro φ
  refine ⟨fun a _ => d.representative (φ a), ?_⟩
  intro a h
  exact (d.embed_representative (φ a)).symm

/-- If global representative data exists for every codomain variable type, then every law has the
support quotient-lifting resource. -/
theorem supportQuotientLift_of_globalSections {δ α : Type}
    (Γ : Ctx δ) (E : MagmaLaw α)
    (hsec : ∀ β : Type, QuotientRepresentativeSection (β := β) Γ) :
    SupportQuotientLift Γ E := by
  intro β φ
  obtain ⟨d⟩ := hsec β
  exact supportQuotientLift_of_quotientRepresentativeData Γ E d φ

/-- The empty theory has canonical representative data in every codomain, obtained from O23's
constructive inverse to `embed`. -/
def quotientRepresentativeData_empty {δ β : Type} :
    QuotientRepresentativeData (β := β) (∅ : Ctx δ) where
  representative := FreeMagmaWithLaws.unembedEmpty
  embed_representative := FreeMagmaWithLaws.embed_unembedEmpty

/-- Hence the empty theory's global section exists as actual Type-valued data, not merely a Prop
existence claim. -/
theorem quotientRepresentativeSection_empty {δ β : Type} :
    QuotientRepresentativeSection (β := β) (∅ : Ctx δ) :=
  ⟨quotientRepresentativeData_empty⟩

/-- O23's law-local result factors through the global canonical-section resource. -/
theorem supportQuotientLift_empty_via_globalSection {α δ : Type} (E : MagmaLaw α) :
    SupportQuotientLift (∅ : Ctx δ) E := by
  apply supportQuotientLift_of_globalSections (∅ : Ctx δ) E
  intro β
  exact quotientRepresentativeSection_empty
