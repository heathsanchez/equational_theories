import equational_theories.SupportLocalDerivation
import equational_theories.SupportSemanticBoundary

open FreeMagma
open Law

/-- Computational support-retraction data. This lives in `Type`, unlike `SupportRetract E`, which
merely asserts existence in `Prop`. The distinction matters when the target itself is a Type-valued
proof object. -/
structure SupportRetractionData {α : Type} (E : MagmaLaw α) where
  retract : α → {a // E.Mem a}
  retract_on : ∀ s : {a // E.Mem a}, retract s.1 = s

/-- Computational retraction data implies the proposition-level semantic resource. -/
theorem SupportRetractionData.toSupportRetract {α : Type} {E : MagmaLaw α}
    (d : SupportRetractionData E) : SupportRetract E :=
  ⟨d.retract, d.retract_on⟩

/-- With computational retraction data, a support-local substitution can be totalized as actual
Type-valued data while preserving its value on every visible variable. -/
def totalizeSupportAssignment_of_data {α β : Type} {E : MagmaLaw α}
    (d : SupportRetractionData E)
    (σ : (a : α) → E.Mem a → FreeMagma β) : α → FreeMagma β :=
  fun a => σ (d.retract a).1 (d.retract a).2

/-- The totalization agrees with the support-local assignment on support. -/
theorem totalizeSupportAssignment_of_data_agree {α β : Type} {E : MagmaLaw α}
    (d : SupportRetractionData E)
    (σ : (a : α) → E.Mem a → FreeMagma β)
    (a : α) (ha : E.Mem a) :
    σ a ha = totalizeSupportAssignment_of_data d σ a := by
  have hra : d.retract a = ⟨a, ha⟩ := d.retract_on ⟨a, ha⟩
  simp only [totalizeSupportAssignment_of_data]
  rw [hra]

/-- The support-local calculus is conservative over the existing uniform-substitution calculus
whenever every axiom in the context carries computational support-retraction data. No
`DecidableEq` or `Classical.choice` is used by this translation. -/
def derive'_of_deriveSupport'_retractionData {α β : Type}
    {Γ : Ctx α} {E : MagmaLaw β}
    (hret : (A : MagmaLaw α) → A ∈ Γ → SupportRetractionData A) :
    deriveSupport' Γ E → derive' Γ E
  | .SubstAxSupport (E := A) h σ => by
      let d := hret A h
      let τ := totalizeSupportAssignment_of_data d σ
      have hl : FreeMagma.supportSubst A.lhs (fun a ha => σ a (.inl ha)) = A.lhs ⬝ τ :=
        FreeMagma.supportSubst_eq_eval_of_agree A.lhs _ τ
          (fun a ha => totalizeSupportAssignment_of_data_agree d σ a (.inl ha))
      have hr : FreeMagma.supportSubst A.rhs (fun a ha => σ a (.inr ha)) = A.rhs ⬝ τ :=
        FreeMagma.supportSubst_eq_eval_of_agree A.rhs _ τ
          (fun a ha => totalizeSupportAssignment_of_data_agree d σ a (.inr ha))
      rw [Law.MagmaLaw.supportSubst, hl, hr]
      exact derive'.SubstAx h τ
  | .Ref => .Ref
  | .Sym h => .Sym (derive'_of_deriveSupport'_retractionData hret h)
  | .Trans h₁ h₂ => .Trans (derive'_of_deriveSupport'_retractionData hret h₁)
      (derive'_of_deriveSupport'_retractionData hret h₂)
  | .Cong h₁ h₂ => .Cong (derive'_of_deriveSupport'_retractionData hret h₁)
      (derive'_of_deriveSupport'_retractionData hret h₂)

/-- Decidable equality is one way to construct the computational retraction data, without passing
through the proposition-level existential. -/
def supportRetractionData_of_decidableEq {α : Type} [DecidableEq α]
    (E : MagmaLaw α) : SupportRetractionData E where
  retract := fun a => if h : E.Mem a then ⟨a, h⟩ else ⟨E.lhs.first, .inl E.lhs.first_mem⟩
  retract_on := by
    intro s
    apply Subtype.ext
    simp [s.property]

/-- The older decidable-equality reverse translation factors through computational retraction data. -/
def derive'_of_deriveSupport'_via_retractionData_decidable {α β : Type} [DecidableEq α]
    {Γ : Ctx α} {E : MagmaLaw β} : deriveSupport' Γ E → derive' Γ E :=
  derive'_of_deriveSupport'_retractionData
    (fun A _ => supportRetractionData_of_decidableEq A)

/-- Negative separator retained as a proposition: mere `SupportRetract` is enough to prove that a
totalization exists, but this existential cannot in general be eliminated into the Type-valued
`derive'` object above without additional extraction data. -/
theorem totalization_merely_exists_of_retract {α β : Type} {E : MagmaLaw α}
    (hret : SupportRetract E)
    (σ : (a : α) → E.Mem a → FreeMagma β) :
    ∃ τ : α → FreeMagma β, ∀ a (ha : E.Mem a), σ a ha = τ a := by
  obtain ⟨r, hr⟩ := hret
  let τ : α → FreeMagma β := fun a => σ (r a).1 (r a).2
  refine ⟨τ, ?_⟩
  intro a ha
  have hra : r a = ⟨a, ha⟩ := hr ⟨a, ha⟩
  simp only [τ]
  rw [hra]
