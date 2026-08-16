import equational_theories.OccurrencePositionBoundary

open FreeMagma

namespace FreeMagma

/-- Uniform computational materialization just for two-leaf terms. This is much weaker-looking than
`[DecidableEq α]`: it only asks that known membership proofs in `Lf a ⋆ Lf b` can be mapped to
concrete leaf positions. O17 tests whether even this already carries equality-discrimination power. -/
def TwoLeafMemPositionData (α : Type) : Type :=
  (a b : α) → MemPositionData (Lf a ⋆ Lf b)

/-- Decidable equality supplies the two-leaf materializer by O15. -/
def twoLeafMemPositionData_of_decidableEq {α : Type} [DecidableEq α] :
    TwoLeafMemPositionData α :=
  fun a b => memPositionData_of_decidableEq (Lf a ⋆ Lf b)

/-- The two positions of a two-leaf term are computationally decidable without looking at labels. -/
def twoLeafPosDecidableEq {α : Type} (a b : α) :
    DecidableEq (OccurrencePos (Lf a ⋆ Lf b)) := by
  intro p q
  cases p with
  | inl p =>
      cases q with
      | inl q => exact isTrue (by cases p; cases q; rfl)
      | inr q => exact isFalse (by intro h; cases h)
  | inr p =>
      cases q with
      | inl q => exact isFalse (by intro h; cases h)
      | inr q => exact isTrue (by cases p; cases q; rfl)

/-- If the materializer sends the known left occurrence of `a` and known right occurrence of `b`
to the same concrete position, their labels must be equal. -/
theorem eq_of_twoLeaf_positions_eq {α : Type} (d : TwoLeafMemPositionData α)
    (a b : α)
    (hpos : (d a b).locate a (.inl rfl) = (d a b).locate b (.inr rfl)) :
    a = b := by
  have ha := (d a b).label_locate a (.inl rfl)
  have hb := (d a b).label_locate b (.inr rfl)
  rw [hpos] at ha
  exact ha.symm.trans hb

/-- If `a=b`, proof irrelevance forces the two known membership proofs to be observationally
identical to the materializer, hence their returned positions must coincide. -/
theorem twoLeaf_positions_eq_of_eq {α : Type} (d : TwoLeafMemPositionData α)
    (a b : α) (hab : a = b) :
    (d a b).locate a (.inl rfl) = (d a b).locate b (.inr rfl) := by
  subst b
  have hp : (show Mem a (Lf a ⋆ Lf a) from .inl rfl) = (.inr rfl) :=
    Subsingleton.elim _ _
  exact congrArg ((d a a).locate a) hp

/-- Uniform computational occurrence materialization for two-leaf terms already yields decidable
equality on the ambient label type. The decision is made by comparing the two finite positions;
no inspection of the labels themselves is used by the comparison. -/
def decidableEq_of_twoLeafMemPositionData {α : Type}
    (d : TwoLeafMemPositionData α) : DecidableEq α := by
  intro a b
  let pa := (d a b).locate a (.inl rfl)
  let pb := (d a b).locate b (.inr rfl)
  match twoLeafPosDecidableEq a b pa pb with
  | isTrue hp =>
      exact isTrue (eq_of_twoLeaf_positions_eq d a b hp)
  | isFalse hne =>
      exact isFalse (fun hab => hne (twoLeaf_positions_eq_of_eq d a b hab))

/-- O15's decidable-equality search and two-leaf computational occurrence materialization are
inter-derivable as Type-valued resources. -/
theorem twoLeafMaterialization_iff_decidableEq_data {α : Type} :
    Nonempty (TwoLeafMemPositionData α) ↔ Nonempty (DecidableEq α) := by
  constructor
  · rintro ⟨d⟩
    exact ⟨decidableEq_of_twoLeafMemPositionData d⟩
  · rintro ⟨deq⟩
    letI : DecidableEq α := deq
    exact ⟨twoLeafMemPositionData_of_decidableEq⟩

end FreeMagma
