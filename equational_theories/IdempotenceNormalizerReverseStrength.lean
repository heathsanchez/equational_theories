import equational_theories.IdempotenceNormalizerBoundary
import Mathlib.Data.Set.Basic

open FreeMagma
open Law

/-- A natural computational-normalizer interface for idempotence: O29 normalizer data plus the
requirement that variables are already canonical. -/
structure LeafFixedIdempotenceNormalizer (β : Type) where
  data : QuotientNormalizerData (β := β) idempotenceCtx
  fixesLeaf : ∀ a : β, data.normalize (Lf a) = Lf a

private def idempotentSetMagma (β : Type) : Magma (Set β) where
  op := Set.union

private theorem idempotentSetMagma_isModel {β : Type} :
    letI : Magma (Set β) := idempotentSetMagma β
    Set β ⊧ idempotenceCtx := by
  letI : Magma (Set β) := idempotentSetMagma β
  intro E hE φ
  have hEq : E = idempotenceLaw := by
    simpa [idempotenceCtx] using hE
  subst E
  change φ PUnit.unit ∪ φ PUnit.unit = φ PUnit.unit
  exact Set.union_self _

/-- If `Lf a ⋆ Lf b` is derivably equal under idempotence to a leaf, then `a = b`.
The separating model is powerset union, which records both leaf labels constructively. -/
theorem eq_of_idempotence_pair_derives_leaf {β : Type} {a b c : β}
    (d : idempotenceCtx ⊢' (Lf a ⋆ Lf b) ≃ Lf c) : a = b := by
  letI : Magma (Set β) := idempotentSetMagma β
  have hmodel : Set β ⊧ idempotenceCtx := idempotentSetMagma_isModel
  have hset0 := (Soundness'_u d hmodel) (fun x => ({x} : Set β))
  change ({a} ∪ {b} : Set β) = {c} at hset0
  have haU : a ∈ ({a} ∪ {b} : Set β) := by simp
  have hbU : b ∈ ({a} ∪ {b} : Set β) := by simp
  have haC : a ∈ ({c} : Set β) := by simpa [hset0] using haU
  have hbC : b ∈ ({c} : Set β) := by simpa [hset0] using hbU
  have hac : a = c := by simpa using haC
  have hbc : b = c := by simpa using hbC
  exact hac.trans hbc.symm

/-- O35 reverse-strength theorem. Any computational idempotence normalizer that fixes leaves
already provides decidable equality on the underlying variable type. -/
def decidableEq_of_leafFixedIdempotenceNormalizer {β : Type}
    (N : LeafFixedIdempotenceNormalizer β) : DecidableEq β := fun a b =>
  match hnorm : N.data.normalize (Lf a ⋆ Lf b) with
  | .Leaf c =>
      isTrue (by
        have d := N.data.reduces (Lf a ⋆ Lf b)
        rw [hnorm] at d
        exact eq_of_idempotence_pair_derives_leaf d)
  | .Fork l r =>
      isFalse (by
        intro hab
        subst b
        have hrel : RelOfLaws β idempotenceCtx (Lf a ⋆ Lf a) (Lf a) :=
          ⟨derive'_idempotence_step (Lf a)⟩
        have heq := N.data.normalize_respects hrel
        rw [hnorm, N.fixesLeaf a] at heq
        cases heq)

/-- The explicit O32 normalizer satisfies the leaf-fixed interface whenever equality is already
decidable. This closes the scoped equivalence for this natural normalizer class. -/
def leafFixedIdempotenceNormalizer_of_decidableEq {β : Type} [DecidableEq β] :
    LeafFixedIdempotenceNormalizer β where
  data := quotientNormalizerData_idempotence
  fixesLeaf := by intro a; rfl

/-- For the leaf-fixed O29 interface, existence of computational normalizer data is inter-derivable
with decidable equality. The reverse direction is O32; the forward direction is the O35 theorem. -/
theorem nonempty_leafFixedNormalizer_iff_nonempty_decidableEq (β : Type) :
    Nonempty (LeafFixedIdempotenceNormalizer β) ↔ Nonempty (DecidableEq β) := by
  constructor
  · rintro ⟨N⟩
    exact ⟨decidableEq_of_leafFixedIdempotenceNormalizer N⟩
  · rintro ⟨inst⟩
    letI : DecidableEq β := inst
    exact ⟨leafFixedIdempotenceNormalizer_of_decidableEq⟩
