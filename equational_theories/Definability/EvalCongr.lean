import equational_theories.Definability.Basic

/-- Evaluating a `FreeMagma` expression only depends on the values assigned to the variables that
actually occur in it. This is shared proof infrastructure for definability constructions. -/
theorem FreeMagma.evalInMagma_congr {α G} [Magma G] {φ ψ : α → G} :
    ∀ (m : FreeMagma α), (∀ a, m.Mem a → φ a = ψ a) → m ⬝ φ = m ⬝ ψ
  | Lf _, h => h _ rfl
  | m₁ ⋆ m₂, h =>
    congrArg₂ Magma.op (evalInMagma_congr m₁ fun _ ha ↦ h _ (.inl ha))
      (evalInMagma_congr m₂ fun _ ha ↦ h _ (.inr ha))
