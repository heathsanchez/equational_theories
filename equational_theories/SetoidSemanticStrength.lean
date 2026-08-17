import equational_theories.SetoidOrdinaryBridge

open FreeMagma
open Law

namespace O50

open O47 O48

/-- Ordinary equality as a setoid-magma structure. -/
def EqualitySetoidMagma (G : Type*) [Magma G] : SetoidMagma G where
  setoid := Setoid.rfl
  op_congr := by
    intro a a' b b' ha hb
    cases ha
    cases hb
    rfl

/-- Setoid satisfaction for the equality setoid is ordinary satisfaction. -/
theorem satisfiesSetoid_equality_iff {α G : Type*} [Magma G]
    (E : MagmaLaw α) :
    satisfiesSetoid (EqualitySetoidMagma G) E ↔ G ⊧ E := by
  rfl

/-- Setoid validity is a stronger semantic premise than ordinary equality-model validity. -/
theorem modelsSetoid_to_ordinary {α β : Type} {Γ : Ctx α} {E : MagmaLaw β} :
    modelsSetoid Γ E → Γ ⊧ E := by
  intro h G instG hΓ φ
  letI : Magma G := instG
  have hSetCtx : satisfiesSetoidCtx (EqualitySetoidMagma G) Γ := by
    intro A mem σ
    exact hΓ A mem σ
  exact h G (EqualitySetoidMagma G) hSetCtx φ

/-- Under the exact O48 source-lift bridge, ordinary and setoid validity coincide. -/
theorem ordinary_iff_setoid_of_sourceLift {α β : Type}
    {Γ : Ctx α} {E : MagmaLaw β}
    (hLift : ∀ (G : Type) [Magma G] (S : SetoidMagma G),
      SourceValuationLift (α := α) S) :
    (Γ ⊧ E) ↔ modelsSetoid Γ E := by
  constructor
  · intro h
    exact ordinary_to_setoid_of_sourceLift h hLift
  · exact modelsSetoid_to_ordinary

end O50
