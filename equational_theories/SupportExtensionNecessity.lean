import equational_theories.SupportLocalConservativity

open FreeMagma
open Law

def SupportSubstitutionExtension {α : Type} (E : MagmaLaw α) : Prop :=
  ∀ (β : Type) (σ : (a : α) → E.Mem a → FreeMagma β),
    ∃ τ : α → FreeMagma β, ∀ a (ha : E.Mem a), σ a ha = τ a

theorem supportSubstitutionExtension_of_supportRetract {α : Type} {E : MagmaLaw α}
    (hret : SupportRetract E) : SupportSubstitutionExtension E := by
  intro β σ
  exact totalization_merely_exists_of_retract hret σ

theorem supportRetract_of_supportSubstitutionExtension {α : Type} {E : MagmaLaw α}
    (hext : SupportSubstitutionExtension E) : SupportRetract E := by
  let S := {a : α // E.Mem a}
  let σ : (a : α) → E.Mem a → FreeMagma S := fun a ha => Lf ⟨a, ha⟩
  obtain ⟨τ, hτ⟩ := hext S σ
  let r : α → S := fun a => (τ a).first
  refine ⟨r, ?_⟩
  intro s
  have hterm : (Lf s : FreeMagma S) = τ s.1 := by
    simpa [σ] using hτ s.1 s.2
  have hfirst : s = (τ s.1).first := by
    simpa using congrArg FreeMagma.first hterm
  simpa [r] using hfirst.symm

theorem supportRetract_iff_allSupportSubstitutionExtensions {α : Type} {E : MagmaLaw α} :
    SupportRetract E ↔ SupportSubstitutionExtension E := by
  constructor
  · exact supportSubstitutionExtension_of_supportRetract
  · exact supportRetract_of_supportSubstitutionExtension
