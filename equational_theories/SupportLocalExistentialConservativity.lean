import equational_theories.SupportLocalConservativity

open FreeMagma
open Law

theorem nonempty_derive'_of_deriveSupport'_retractable {α β : Type}
    {Γ : Ctx α} {E : MagmaLaw β}
    (hret : ∀ A, A ∈ Γ → SupportRetract A) :
    deriveSupport' Γ E → Nonempty (derive' Γ E)
  | .SubstAxSupport (E := A) h σ => by
      obtain ⟨τ, hagree⟩ := totalization_merely_exists_of_retract (hret A h) σ
      have hl : FreeMagma.supportSubst A.lhs (fun a ha => σ a (.inl ha)) = A.lhs ⬝ τ :=
        FreeMagma.supportSubst_eq_eval_of_agree A.lhs _ τ
          (fun a ha => hagree a (.inl ha))
      have hr : FreeMagma.supportSubst A.rhs (fun a ha => σ a (.inr ha)) = A.rhs ⬝ τ :=
        FreeMagma.supportSubst_eq_eval_of_agree A.rhs _ τ
          (fun a ha => hagree a (.inr ha))
      refine ⟨?_⟩
      rw [Law.MagmaLaw.supportSubst, hl, hr]
      exact derive'.SubstAx h τ
  | .Ref => ⟨.Ref⟩
  | .Sym h => by
      obtain ⟨d⟩ := nonempty_derive'_of_deriveSupport'_retractable hret h
      exact ⟨.Sym d⟩
  | .Trans h₁ h₂ => by
      obtain ⟨d₁⟩ := nonempty_derive'_of_deriveSupport'_retractable hret h₁
      obtain ⟨d₂⟩ := nonempty_derive'_of_deriveSupport'_retractable hret h₂
      exact ⟨.Trans d₁ d₂⟩
  | .Cong h₁ h₂ => by
      obtain ⟨d₁⟩ := nonempty_derive'_of_deriveSupport'_retractable hret h₁
      obtain ⟨d₂⟩ := nonempty_derive'_of_deriveSupport'_retractable hret h₂
      exact ⟨.Cong d₁ d₂⟩

theorem nonempty_deriveSupport'_iff_nonempty_derive'_of_retractable {α β : Type}
    {Γ : Ctx α} {E : MagmaLaw β}
    (hret : ∀ A, A ∈ Γ → SupportRetract A) :
    Nonempty (deriveSupport' Γ E) ↔ Nonempty (derive' Γ E) := by
  constructor
  · rintro ⟨d⟩
    exact nonempty_derive'_of_deriveSupport'_retractable hret d
  · rintro ⟨d⟩
    exact ⟨deriveSupport'_of_derive' d⟩
