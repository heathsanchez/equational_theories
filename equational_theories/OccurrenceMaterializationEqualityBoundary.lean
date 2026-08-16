import equational_theories.OccurrencePositionBoundary

open FreeMagma

namespace FreeMagma

def TwoLeafMemPositionData (α : Type) : Type :=
  (a b : α) → MemPositionData (Lf a ⋆ Lf b)

def twoLeafMemPositionData_of_decidableEq {α : Type} [DecidableEq α] :
    TwoLeafMemPositionData α :=
  fun a b => memPositionData_of_decidableEq (Lf a ⋆ Lf b)

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

theorem eq_of_twoLeaf_positions_eq {α : Type} (d : TwoLeafMemPositionData α)
    (a b : α)
    (hpos : (d a b).locate a (.inl rfl) = (d a b).locate b (.inr rfl)) :
    a = b := by
  have ha := (d a b).label_locate a (.inl rfl)
  have hb := (d a b).label_locate b (.inr rfl)
  rw [hpos] at ha
  exact ha.symm.trans hb

theorem twoLeaf_positions_eq_of_eq {α : Type} (d : TwoLeafMemPositionData α)
    (a b : α) (hab : a = b) :
    (d a b).locate a (.inl rfl) = (d a b).locate b (.inr rfl) := by
  subst b
  have hp : (show Mem a (Lf a ⋆ Lf a) from .inl rfl) = (.inr rfl) :=
    Subsingleton.elim _ _
  exact congrArg ((d a a).locate a) hp

def decidableEq_of_twoLeafMemPositionData {α : Type}
    (d : TwoLeafMemPositionData α) : DecidableEq α := by
  intro a b
  let pa := (d a b).locate a (.inl rfl)
  let pb := (d a b).locate b (.inr rfl)
  match twoLeafPosDecidableEq a b pa pb with
  | isTrue hp => exact isTrue (eq_of_twoLeaf_positions_eq d a b hp)
  | isFalse hne => exact isFalse (fun hab => hne (twoLeaf_positions_eq_of_eq d a b hab))

theorem twoLeafMaterialization_iff_decidableEq_data {α : Type} :
    Nonempty (TwoLeafMemPositionData α) ↔ Nonempty (DecidableEq α) := by
  constructor
  · rintro ⟨d⟩
    exact ⟨decidableEq_of_twoLeafMemPositionData d⟩
  · rintro ⟨deq⟩
    letI : DecidableEq α := deq
    exact ⟨twoLeafMemPositionData_of_decidableEq⟩

end FreeMagma
