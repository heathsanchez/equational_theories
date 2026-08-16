import equational_theories.CanonicalQuotientSection

open FreeMagma
open Law

/-- The nontrivial equational theory x ◇ y = y. -/
def rightProjectionLaw : MagmaLaw Bool :=
  (Lf false ⋆ Lf true) ≃ Lf true

def rightProjectionCtx : Ctx Bool :=
  {rightProjectionLaw}

/-- Every derivable equality in the right-projection theory preserves the last leaf. The proof
interprets derivability in the concrete right-projection magma and applies soundness. -/
theorem derive'_rightProjection_last_eq {β : Type} {x y : FreeMagma β}
    (d : rightProjectionCtx ⊢' x ≃ y) : x.last = y.last := by
  letI : Magma β := ⟨fun _ b => b⟩
  have hmodel : β ⊧ rightProjectionCtx := by
    intro E hE φ
    have hEq : E = rightProjectionLaw := by
      simpa [rightProjectionCtx] using hE
    subst E
    rfl
  have eval_last : ∀ t : FreeMagma β, t ⬝ (fun b => b) = t.last := by
    intro t
    induction t with
    | Leaf a => rfl
    | Fork l r ihl ihr =>
        simpa [FreeMagma.evalInMagma] using ihr
  have hxy : x ⬝ (fun b => b) = y ⬝ (fun b => b) :=
    (Soundness'_u d hmodel) (fun b => b)
  calc
    x.last = x ⬝ (fun b => b) := (eval_last x).symm
    _ = y ⬝ (fun b => b) := hxy
    _ = y.last := eval_last y

/-- Every term is derivably equal to the leaf carrying its last variable. -/
def derive'_rightProjection_reduce {β : Type} :
    (t : FreeMagma β) → rightProjectionCtx ⊢' t ≃ Lf t.last
  | .Leaf a => derive'.Ref
  | .Fork l r => by
      let σ : Bool → FreeMagma β := fun b =>
        match b with
        | false => l
        | true => r
      have hmem : rightProjectionLaw ∈ rightProjectionCtx := by
        simp [rightProjectionCtx]
      have hax0 := derive'.SubstAx hmem σ
      have hax : rightProjectionCtx ⊢' (l ⋆ r) ≃ r := by
        simpa [rightProjectionLaw, σ, FreeMagma.evalInMagma] using hax0
      exact derive'.Trans hax (derive'_rightProjection_reduce r)

/-- Canonical representative of a quotient class: its last leaf. -/
def FreeMagmaWithLaws.unembedRightProjection {β : Type} :
    FreeMagmaWithLaws β rightProjectionCtx → FreeMagma β :=
  Quotient.lift (fun t => Lf t.last) (by
    intro x y h
    obtain ⟨d⟩ := h
    exact congrArg Lf (derive'_rightProjection_last_eq d))

@[simp] theorem FreeMagmaWithLaws.unembedRightProjection_embed {β : Type}
    (t : FreeMagma β) :
    FreeMagmaWithLaws.unembedRightProjection (embed rightProjectionCtx t) = Lf t.last := by
  rfl

/-- The canonical last-leaf representative embeds back to the original quotient class. -/
theorem FreeMagmaWithLaws.embed_unembedRightProjection {β : Type}
    (q : FreeMagmaWithLaws β rightProjectionCtx) :
    embed rightProjectionCtx (FreeMagmaWithLaws.unembedRightProjection q) = q := by
  induction q using FreeMagmaWithLaws.inductionOn with
  | h t =>
      apply FreeMagmaWithLaws.eq.mpr
      exact ⟨derive'.Sym (derive'_rightProjection_reduce t)⟩

/-- Actual Type-valued canonical quotient representative data for a second nonempty theory. -/
def quotientRepresentativeData_rightProjection {β : Type} :
    QuotientRepresentativeData (β := β) rightProjectionCtx where
  representative := FreeMagmaWithLaws.unembedRightProjection
  embed_representative := FreeMagmaWithLaws.embed_unembedRightProjection

/-- Therefore every law has support quotient lifting over the right-projection quotient, with no
support indexing and no decidable equality on the law-variable type. -/
theorem supportQuotientLift_rightProjection {α : Type} (E : MagmaLaw α) :
    SupportQuotientLift rightProjectionCtx E := by
  apply supportQuotientLift_of_globalSections rightProjectionCtx E
  intro β
  exact ⟨quotientRepresentativeData_rightProjection⟩
