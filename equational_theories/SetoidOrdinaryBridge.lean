import equational_theories.SetoidCompletenessBoundary

open FreeMagma
open Law

namespace O48

open O47

/-- The ordinary quotient type associated to a setoid magma. -/
def QuotMagma {G : Type*} [Magma G] (S : SetoidMagma G) := Quotient S.setoid

/-- Canonical projection into the quotient. -/
def qembed {G : Type*} [Magma G] (S : SetoidMagma G) (x : G) : QuotMagma S :=
  Quotient.mk _ x

/-- The setoid congruence makes the quotient inherit the magma operation constructively. -/
instance quotMagmaInst {G : Type*} [Magma G] (S : SetoidMagma G) : Magma (QuotMagma S) where
  op := Quotient.lift₂ (fun x y => qembed S (x ◇ y)) <| by
    intro a b a' b' ha hb
    exact Quotient.sound (S.op_congr ha hb)

@[simp] theorem qembed_op {G : Type*} [Magma G] (S : SetoidMagma G) (x y : G) :
    qembed S (x ◇ y) = qembed S x ◇ qembed S y := rfl

/-- Evaluation commutes with the quotient projection. -/
theorem eval_qembed {α G : Type*} [Magma G] (S : SetoidMagma G)
    (t : FreeMagma α) (φ : α → G) :
    t ⬝ (qembed S ∘ φ) = qembed S (t ⬝ φ) := by
  induction t with
  | Leaf a => rfl
  | Fork l r ihl ihr =>
      simp only [evalInMagma]
      rw [ihl, ihr]
      rfl

/-- The exact bridge resource: lift one whole source-variable valuation through the quotient. -/
def SourceValuationLift {α G : Type*} [Magma G] (S : SetoidMagma G) : Prop :=
  ∀ φ : α → QuotMagma S,
    ∃ σ : α → G, ∀ a, φ a = qembed S (σ a)

/-- With source-valuation lifting, a setoid model descends to an ordinary quotient model. -/
theorem quotient_isModel_of_sourceLift {α G : Type} [Magma G]
    (S : SetoidMagma G) {Γ : Ctx α}
    (hS : satisfiesSetoidCtx S Γ)
    (hLift : SourceValuationLift (α := α) S) :
    QuotMagma S ⊧ Γ := by
  intro A mem φ
  obtain ⟨σ, hσ⟩ := hLift φ
  have hfun : φ = qembed S ∘ σ := funext fun a => hσ a
  rw [hfun]
  simp only [satisfiesPhi]
  rw [eval_qembed, eval_qembed]
  exact Quotient.sound (hS A mem σ)

/-- O48 bridge: ordinary equality-model entailment implies setoid entailment once exactly the
source-variable quotient-lifting resource is supplied. No target-variable representative choice
is needed. -/
theorem ordinary_to_setoid_of_sourceLift {α β : Type}
    {Γ : Ctx α} {E : MagmaLaw β}
    (hOrd : Γ ⊧ E)
    (hLift : ∀ (G : Type) [Magma G] (S : SetoidMagma G),
      SourceValuationLift (α := α) S) :
    modelsSetoid Γ E := by
  intro G instG S hS φ
  letI : Magma G := instG
  have hQ : QuotMagma S ⊧ Γ := quotient_isModel_of_sourceLift S hS (hLift G S)
  have hEq : QuotMagma S ⊧ E := hOrd _ hQ
  have hφ := hEq (qembed S ∘ φ)
  simp only [satisfiesPhi] at hφ
  rw [eval_qembed, eval_qembed] at hφ
  exact Quotient.exact hφ

end O48
