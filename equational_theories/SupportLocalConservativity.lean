import equational_theories.SupportLocalDerivation
import equational_theories.SupportSemanticBoundary

open FreeMagma
open Law

structure SupportRetractionData {α : Type} (E : MagmaLaw α) where
  retract : α → {a // E.Mem a}
  retract_on : ∀ s : {a // E.Mem a}, retract s.1 = s

theorem SupportRetractionData.toSupportRetract {α : Type} {E : MagmaLaw α}
    (d : SupportRetractionData E) : SupportRetract E :=
  ⟨d.retract, d.retract_on⟩

def totalizeSupportAssignment_of_data {α β : Type} {E : MagmaLaw α}
    (d : SupportRetractionData E)
    (σ : (a : α) → E.Mem a → FreeMagma β) : α → FreeMagma β :=
  fun a => σ (d.retract a).1 (d.retract a).2

theorem totalizeSupportAssignment_of_data_agree {α β : Type} {E : MagmaLaw α}
    (d : SupportRetractionData E)
    (σ : (a : α) → E.Mem a → FreeMagma β)
    (a : α) (ha : E.Mem a) :
    σ a ha = totalizeSupportAssignment_of_data d σ a := by
  have hra : d.retract a = ⟨a, ha⟩ := d.retract_on ⟨a, ha⟩
  simpa only [totalizeSupportAssignment_of_data] using
    (congrArg (fun s : {x // E.Mem x} => σ s.1 s.2) hra).symm

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

def supportRetractionData_of_decidableEq {α : Type} [DecidableEq α]
    (E : MagmaLaw α) : SupportRetractionData E where
  retract := fun a => if h : E.Mem a then ⟨a, h⟩ else ⟨E.lhs.first, .inl E.lhs.first_mem⟩
  retract_on := by
    intro s
    apply Subtype.ext
    simp [s.property]

def derive'_of_deriveSupport'_via_retractionData_decidable {α β : Type} [DecidableEq α]
    {Γ : Ctx α} {E : MagmaLaw β} : deriveSupport' Γ E → derive' Γ E :=
  derive'_of_deriveSupport'_retractionData
    (fun A _ => supportRetractionData_of_decidableEq A)

theorem totalization_merely_exists_of_retract {α β : Type} {E : MagmaLaw α}
    (hret : SupportRetract E)
    (σ : (a : α) → E.Mem a → FreeMagma β) :
    ∃ τ : α → FreeMagma β, ∀ a (ha : E.Mem a), σ a ha = τ a := by
  obtain ⟨r, hr⟩ := hret
  let τ : α → FreeMagma β := fun a => σ (r a).1 (r a).2
  refine ⟨τ, ?_⟩
  intro a ha
  have hra : r a = ⟨a, ha⟩ := hr ⟨a, ha⟩
  simpa only [τ] using
    (congrArg (fun s : {x // E.Mem x} => σ s.1 s.2) hra).symm
