import equational_theories.FreeMagma

/-- Evaluating a `FreeMagma` expression only depends on the values assigned to variables that
actually occur in it. This is generic evaluation infrastructure, independent of definability. -/
theorem FreeMagma.evalInMagma_congr {α G} [Magma G] {φ ψ : α → G} :
    ∀ (m : FreeMagma α), (∀ a, m.Mem a → φ a = ψ a) → m ⬝ φ = m ⬝ ψ
  | Lf _, h => h _ rfl
  | m₁ ⋆ m₂, h =>
    congrArg₂ Magma.op (evalInMagma_congr m₁ fun _ ha ↦ h _ (.inl ha))
      (evalInMagma_congr m₂ fun _ ha ↦ h _ (.inr ha))
