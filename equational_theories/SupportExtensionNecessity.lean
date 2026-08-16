import equational_theories.SupportLocalConservativity

open FreeMagma
open Law

/-- Every support-local substitution into every free-magma codomain can be extended to a total
ambient substitution, preserving all values on support. The whole statement lives in `Prop`. -/
def SupportSubstitutionExtension {α : Type} (E : MagmaLaw α) : Prop :=
  ∀ (β : Type) (σ : (a : α) → E.Mem a → FreeMagma β),
    ∃ τ : α → FreeMagma β, ∀ a (ha : E.Mem a), σ a ha = τ a

/-- O12's proposition-level support retraction supplies every such total extension. -/
theorem supportSubstitutionExtension_of_supportRetract {α : Type} {E : MagmaLaw α}
    (hret : SupportRetract E) : SupportSubstitutionExtension E := by
  intro β σ
  exact totalization_merely_exists_of_retract hret σ

/-- Conversely, if every support-local substitution can be totalized, instantiate the codomain with
the support subtype itself and map each supported variable to its own leaf. Taking the first leaf of
any total extension produces a retraction onto support. -/
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

/-- Exact characterization: proposition-level support retractability is neither merely sufficient nor
an artifact of O12's construction. It is equivalent to totalizability of all support-local free-magma
substitutions. -/
theorem supportRetract_iff_allSupportSubstitutionExtensions {α : Type} {E : MagmaLaw α} :
    SupportRetract E ↔ SupportSubstitutionExtension E := by
  constructor
  · exact supportSubstitutionExtension_of_supportRetract
  · exact supportRetract_of_supportSubstitutionExtension
