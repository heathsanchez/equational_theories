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

/-- Every term derivably reduces to the obvious duplicate-child normal form. -/
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
          subst nr
          exact derive'_idempotence_step nl
        simpa [idempotenceNormalize, nl, nr, h] using derive'.Trans dc hs
      · simpa [idempotenceNormalize, nl, nr, h] using dc

/-- The proposed normal-form hypothesis: derivability under idempotence preserves the recursive
normalizer. O32 is allowed to fail here; that would reject the obvious normal form rather than be
reclassified as an equality-data obstruction. -/
theorem idempotenceNormalize_respects {β : Type} [DecidableEq β] {x y : FreeMagma β}
    (d : idempotenceCtx ⊢' x ≃ y) :
    idempotenceNormalize x = idempotenceNormalize y := by
  induction d with
  | SubstAx h σ =>
      have hEq : idempotenceLaw = idempotenceLaw := rfl
      simp [idempotenceCtx] at h
      -- The substituted axiom is `t ⋆ t ≃ t`; both sides normalize to the same value.
      simp [idempotenceLaw, FreeMagma.evalInMagma, idempotenceNormalize]
  | Ref => rfl
  | Sym d ih => exact ih.symm
  | Trans d₁ d₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | Cong d₁ d₂ ih₁ ih₂ =>
      simp [idempotenceNormalize, ih₁, ih₂]

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
