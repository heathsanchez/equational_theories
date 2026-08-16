import equational_theories.SupportLocalDerivation
import equational_theories.SupportSemanticBoundary

open FreeMagma
open Law

/-- A support retraction is enough to totalize one support-local substitution while preserving its
value on every variable visible to the axiom. No decidable equality test is required. -/
theorem totalizeSupportAssignment_of_retract {α β : Type} {E : MagmaLaw α}
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

/-- The support-local calculus is conservative over the existing uniform-substitution calculus
whenever every axiom in the context has retractable support. This replaces the previous global
`DecidableEq α` assumption by the exact structural resource exposed independently on the semantic
side in O9. This statement remains deliberately Type-0, matching O9's verified scope. -/
def derive'_of_deriveSupport'_retractable {α β : Type}
    {Γ : Ctx α} {E : MagmaLaw β}
    (hret : ∀ A, A ∈ Γ → SupportRetract A) :
    deriveSupport' Γ E → derive' Γ E
  | .SubstAxSupport (E := A) h σ => by
      obtain ⟨τ, hagree⟩ := totalizeSupportAssignment_of_retract (hret A h) σ
      have hl : FreeMagma.supportSubst A.lhs (fun a ha => σ a (.inl ha)) = A.lhs ⬝ τ :=
        FreeMagma.supportSubst_eq_eval_of_agree A.lhs _ τ
          (fun a ha => hagree a (.inl ha))
      have hr : FreeMagma.supportSubst A.rhs (fun a ha => σ a (.inr ha)) = A.rhs ⬝ τ :=
        FreeMagma.supportSubst_eq_eval_of_agree A.rhs _ τ
          (fun a ha => hagree a (.inr ha))
      rw [Law.MagmaLaw.supportSubst, hl, hr]
      exact derive'.SubstAx h τ
  | .Ref => .Ref
  | .Sym h => .Sym (derive'_of_deriveSupport'_retractable hret h)
  | .Trans h₁ h₂ => .Trans (derive'_of_deriveSupport'_retractable hret h₁)
      (derive'_of_deriveSupport'_retractable hret h₂)
  | .Cong h₁ h₂ => .Cong (derive'_of_deriveSupport'_retractable hret h₁)
      (derive'_of_deriveSupport'_retractable hret h₂)

/-- Decidable equality recovers the older reverse translation only by supplying support
retractions. -/
def derive'_of_deriveSupport'_via_decidable {α β : Type} [DecidableEq α]
    {Γ : Ctx α} {E : MagmaLaw β} : deriveSupport' Γ E → derive' Γ E :=
  derive'_of_deriveSupport'_retractable
    (fun A _ => supportRetract_of_decidableEq A)
