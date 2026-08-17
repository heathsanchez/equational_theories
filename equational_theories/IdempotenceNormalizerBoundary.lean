import equational_theories.QuotientNormalizerSection

open FreeMagma
open Law

/-- Idempotence: x ◇ x = x. -/
def idempotenceLaw : MagmaLaw PUnit :=
  (Lf PUnit.unit ⋆ Lf PUnit.unit) ≃ Lf PUnit.unit

def idempotenceCtx : Ctx PUnit :=
  {idempotenceLaw}

/-- One idempotence contraction at an arbitrary substituted term. -/
def derive'_idempotence_step {β : Type} (t : FreeMagma β) :
    idempotenceCtx ⊢' (t ⋆ t) ≃ t := by
  let σ : PUnit → FreeMagma β := fun _ => t
  have hmem : idempotenceLaw ∈ idempotenceCtx := by
    simp [idempotenceCtx]
  have h := derive'.SubstAx hmem σ
  simpa [idempotenceLaw, σ, FreeMagma.evalInMagma] using h

/-- Obvious recursive idempotence normalizer. The only non-structural operation is comparison of
already-normalized children. -/
def idempotenceNormalize {β : Type} [DecidableEq β] : FreeMagma β → FreeMagma β
  | .Leaf a => .Leaf a
  | .Fork l r =>
      let nl := idempotenceNormalize l
      let nr := idempotenceNormalize r
      if h : nl = nr then nl else nl ⋆ nr

/-- Every term derivably reduces to the duplicate-child normal form. -/
def derive'_idempotence_reduce {β : Type} [DecidableEq β] :
    (t : FreeMagma β) → idempotenceCtx ⊢' t ≃ idempotenceNormalize t
  | .Leaf a => derive'.Ref
  | .Fork l r => by
      have dl := derive'_idempotence_reduce l
      have dr := derive'_idempotence_reduce r
      have dc := derive'.Cong dl dr
      let nl := idempotenceNormalize l
      let nr := idempotenceNormalize r
      by_cases h : nl = nr
      · have hs : idempotenceCtx ⊢' (nl ⋆ nr) ≃ nl := by
          simpa [h] using derive'_idempotence_step nl
        simpa [idempotenceNormalize, nl, nr, h] using derive'.Trans dc hs
      · simpa [idempotenceNormalize, nl, nr, h] using dc

/-- The algebra whose multiplication is exactly the normalization combine-step. This is a
separating model for the proposed normal form: its operation contracts equal normalized children
and otherwise keeps the fork. -/
def idempotenceNormalMagma (β : Type) [DecidableEq β] : Magma (FreeMagma β) where
  op a b := if h : a = b then a else a ⋆ b

/-- Evaluating a term in the normal-form algebra under leaf injection computes the proposed
recursive normalizer. -/
theorem eval_idempotenceNormalMagma_eq_normalize {β : Type} [DecidableEq β]
    (t : FreeMagma β) :
    @FreeMagma.evalInMagma β (FreeMagma β) (idempotenceNormalMagma β) t Lf =
      idempotenceNormalize t := by
  induction t with
  | Leaf a => rfl
  | Fork l r ihl ihr =>
      change (if h : (l ⬝ Lf) = (r ⬝ Lf) then (l ⬝ Lf) else (l ⬝ Lf) ⋆ (r ⬝ Lf)) = _
      rw [ihl, ihr]
      rfl

/-- The normal-form algebra satisfies idempotence. -/
theorem idempotenceNormalMagma_isModel {β : Type} [DecidableEq β] :
    (FreeMagma β) ⊧ idempotenceCtx := by
  letI : Magma (FreeMagma β) := idempotenceNormalMagma β
  intro E hE φ
  have hEq : E = idempotenceLaw := by
    simpa [idempotenceCtx] using hE
  subst E
  change (if h : φ PUnit.unit = φ PUnit.unit then φ PUnit.unit else
    φ PUnit.unit ⋆ φ PUnit.unit) = φ PUnit.unit
  simp

/-- Derivability under idempotence preserves the proposed normal form. Rather than recurse over
indexed derivation proofs, use soundness in the normal-form algebra learned from O25/O30. -/
theorem idempotenceNormalize_respects {β : Type} [DecidableEq β] {x y : FreeMagma β}
    (d : idempotenceCtx ⊢' x ≃ y) :
    idempotenceNormalize x = idempotenceNormalize y := by
  letI : Magma (FreeMagma β) := idempotenceNormalMagma β
  have hxy : x ⬝ Lf = y ⬝ Lf :=
    (Soundness'_u d idempotenceNormalMagma_isModel) Lf
  calc
    idempotenceNormalize x = x ⬝ Lf := (eval_idempotenceNormalMagma_eq_normalize x).symm
    _ = y ⬝ Lf := hxy
    _ = idempotenceNormalize y := eval_idempotenceNormalMagma_eq_normalize y

/-- Scoped O29 normalizer data. This deliberately retains `[DecidableEq β]`; O32 tests whether
comparison data is a property of normalizer acquisition rather than of the O29 compiler itself. -/
def quotientNormalizerData_idempotence {β : Type} [DecidableEq β] :
    QuotientNormalizerData (β := β) idempotenceCtx where
  normalize := idempotenceNormalize
  normalize_respects := by
    intro x y h
    obtain ⟨d⟩ := h
    exact idempotenceNormalize_respects d
  reduces := derive'_idempotence_reduce
