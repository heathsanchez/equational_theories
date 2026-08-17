import equational_theories.Completeness

open FreeMagma
open Law

namespace O47

/-- A magma equipped with a setoid congruence for its operation. -/
structure SetoidMagma (G : Type*) [Magma G] where
  setoid : Setoid G
  op_congr : ∀ {a a' b b' : G}, setoid.Rel a a' → setoid.Rel b b' →
    setoid.Rel (a ◇ b) (a' ◇ b')

/-- A law is satisfied modulo the chosen setoid relation. -/
def satisfiesSetoidPhi {α G : Type*} [Magma G]
    (S : SetoidMagma G) (φ : α → G) (E : MagmaLaw α) : Prop :=
  S.setoid.Rel (E.lhs ⬝ φ) (E.rhs ⬝ φ)

def satisfiesSetoid {α G : Type*} [Magma G]
    (S : SetoidMagma G) (E : MagmaLaw α) : Prop :=
  ∀ φ : α → G, satisfiesSetoidPhi S φ E

def satisfiesSetoidCtx {α G : Type*} [Magma G]
    (S : SetoidMagma G) (Γ : Ctx α) : Prop :=
  ∀ E ∈ Γ, satisfiesSetoid S E

def modelsSetoid {α β : Type*} (Γ : Ctx α) (E : MagmaLaw β) : Prop :=
  ∀ (G : Type) [Magma G] (S : SetoidMagma G),
    satisfiesSetoidCtx S Γ → satisfiesSetoid S E

/-- Evaluation respects a setoid magma congruence. -/
theorem eval_congr {α G : Type*} [Magma G] (S : SetoidMagma G)
    (t : FreeMagma α) {φ ψ : α → G}
    (h : ∀ a, S.setoid.Rel (φ a) (ψ a)) :
    S.setoid.Rel (t ⬝ φ) (t ⬝ ψ) := by
  induction t with
  | Leaf a => exact h a
  | Fork l r ihl ihr =>
      simpa [evalInMagma] using S.op_congr (ihl h) (ihr h)

/-- Soundness of ordinary derivations for setoid semantics. -/
theorem SoundnessSetoid'_u {α β G : Type*} [Magma G]
    (S : SetoidMagma G) {Γ : Ctx α} {E : MagmaLaw β}
    (h : Γ ⊢' E) : satisfiesSetoidCtx S Γ → satisfiesSetoid S E := by
  induction h with
  | @SubstAx A mem σ =>
      intro H φ
      simpa [satisfiesSetoidPhi, SubstEval] using H A mem (fun a => σ a ⬝ φ)
  | Ref =>
      intro _ φ
      exact S.setoid.refl _
  | @Sym t u _ ih =>
      intro H φ
      exact S.setoid.symm (ih H φ)
  | Trans h₁ h₂ ih₁ ih₂ =>
      intro H φ
      exact S.setoid.trans (ih₁ H φ) (ih₂ H φ)
  | Cong h₁ h₂ ih₁ ih₂ =>
      intro H φ
      simpa [satisfiesSetoidPhi, evalInMagma] using S.op_congr (ih₁ H φ) (ih₂ H φ)

/-- The term model as a setoid magma: carrier is raw FreeMagma terms, equality is derivability. -/
def TermSetoidMagma {α β : Type*} (Γ : Ctx α) : SetoidMagma (FreeMagma β) where
  setoid := SetoidOfLaws β Γ
  op_congr := by
    intro a a' b b' ha hb
    exact ⟨derive'.Cong ha hb⟩

/-- The raw-term setoid model satisfies Γ constructively: no quotient representatives are chosen. -/
theorem termSetoid_isModel {α β : Type*} (Γ : Ctx α) :
    satisfiesSetoidCtx (TermSetoidMagma (β := β) Γ) Γ := by
  intro E mem σ
  exact ⟨derive'.SubstAx mem σ⟩

/-- Setoid completeness: validity in all setoid magmas yields an ordinary derivation, with no choice. -/
theorem CompletenessSetoid' {α β : Type*} {Γ : Ctx α} {E : MagmaLaw β}
    (h : modelsSetoid Γ E) : Nonempty (Γ ⊢' E) := by
  have hterm := h (FreeMagma β) (TermSetoidMagma (β := β) Γ) (termSetoid_isModel (β := β) Γ)
  have hLf := hterm Lf
  simpa [satisfiesSetoidPhi, TermSetoidMagma, SetoidOfLaws.iff, evalInMagma_leaf] using hLf

end O47
