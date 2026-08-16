import equational_theories.Definability.Simple

open FirstOrder.Language

/-- A binary operation represented by a `FreeMagma (Fin 2)` is automatically term-definable in
any magma: translate the free-magma expression to the first-order magma language and realize it. -/
theorem FreeMagma.eval_termDefinable {G : Type*} [M : Magma G]
    (t : FreeMagma (Fin 2)) :
    let _ := M.FOStructure
    (∅ : Set G).TermDefinable MagmaLanguage (fun v : Fin 2 → G ↦ t ⬝ v) := by
  let _ := M.FOStructure
  use (MagmaLanguage.lhomWithConstants (∅ : Set G)).onTerm t.toTerm
  funext v
  simp [FreeMagma.toTerm_realize]

/-- If the variables of a `FreeMagma` expression are assigned to the two arguments of a binary
operation, the resulting evaluator is term-definable. This is the reusable composition of
`fmapHom` with `eval_termDefinable`. -/
theorem FreeMagma.eval_comp_termDefinable {α G : Type*} [M : Magma G]
    (t : FreeMagma α) (σ : α → Fin 2) :
    let _ := M.FOStructure
    (∅ : Set G).TermDefinable MagmaLanguage (fun v : Fin 2 → G ↦ t ⬝ (v ∘ σ)) := by
  simpa [FreeMagma.evalInMagma_fmapHom] using
    (FreeMagma.eval_termDefinable (G := G) (FreeMagma.fmapHom σ t))
