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
