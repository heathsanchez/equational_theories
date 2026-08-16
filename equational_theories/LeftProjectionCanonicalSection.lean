import equational_theories.CanonicalQuotientSection

open FreeMagma
open Law

/-- The nontrivial equational theory x ◇ y = x. -/
def leftProjectionLaw : MagmaLaw Bool :=
  (Lf false ⋆ Lf true) ≃ Lf false

def leftProjectionCtx : Ctx Bool :=
  {leftProjectionLaw}

/-- Every derivable equality in the left-projection theory preserves the first leaf.
Defined by dependent structural recursion on the derivation so the indexed endpoints remain visible. -/
def derive'_leftProjection_first_eq {β : Type} :
    {x y : FreeMagma β} → (leftProjectionCtx ⊢' x ≃ y) → x.first = y.first
  | _, _, .SubstAx (E := E) h σ => by
      have hE : E = leftProjectionLaw := by
        simpa [leftProjectionCtx] using h
      subst E
      rfl
  | _, _, .Ref => rfl
  | _, _, .Sym d => (derive'_leftProjection_first_eq d).symm
  | _, _, .Trans d₁ d₂ =>
      (derive'_leftProjection_first_eq d₁).trans (derive'_leftProjection_first_eq d₂)
  | _, _, .Cong d₁ d₂ => derive'_leftProjection_first_eq d₁

/-- Every term is derivably equal to the leaf carrying its first variable.
This is computational proof data in `Type`, so it is a `def`, not a proposition-valued theorem. -/
def derive'_leftProjection_reduce {β : Type} :
    (t : FreeMagma β) → leftProjectionCtx ⊢' t ≃ Lf t.first
  | .Leaf a => derive'.Ref
  | .Fork l r => by
      let σ : Bool → FreeMagma β := fun b =>
        match b with
        | false => l
        | true => r
      have hmem : leftProjectionLaw ∈ leftProjectionCtx := by
        simp [leftProjectionCtx]
      have hax0 := derive'.SubstAx hmem σ
      have hax : leftProjectionCtx ⊢' (l ⋆ r) ≃ l := by
        simpa [leftProjectionLaw, σ, FreeMagma.evalInMagma] using hax0
      exact derive'.Trans hax (derive'_leftProjection_reduce l)

/-- Canonical representative of a quotient class: its first leaf. Well-definedness follows from
first-leaf invariance of derivability, not from any equality decision on β. -/
def FreeMagmaWithLaws.unembedLeftProjection {β : Type} :
    FreeMagmaWithLaws β leftProjectionCtx → FreeMagma β :=
  Quotient.lift (fun t => Lf t.first) (by
    intro x y h
    obtain ⟨d⟩ := h
    exact congrArg Lf (derive'_leftProjection_first_eq d))

@[simp] theorem FreeMagmaWithLaws.unembedLeftProjection_embed {β : Type}
    (t : FreeMagma β) :
    FreeMagmaWithLaws.unembedLeftProjection (embed leftProjectionCtx t) = Lf t.first := by
  rfl

/-- The canonical first-leaf representative embeds back to the original quotient class. -/
theorem FreeMagmaWithLaws.embed_unembedLeftProjection {β : Type}
    (q : FreeMagmaWithLaws β leftProjectionCtx) :
    embed leftProjectionCtx (FreeMagmaWithLaws.unembedLeftProjection q) = q := by
  induction q using FreeMagmaWithLaws.inductionOn with
  | h t =>
      apply FreeMagmaWithLaws.eq.mpr
      exact ⟨derive'.Sym (derive'_leftProjection_reduce t)⟩

/-- Actual Type-valued canonical quotient representative data for a nonempty theory. -/
def quotientRepresentativeData_leftProjection {β : Type} :
    QuotientRepresentativeData (β := β) leftProjectionCtx where
  representative := FreeMagmaWithLaws.unembedLeftProjection
  embed_representative := FreeMagmaWithLaws.embed_unembedLeftProjection

/-- Therefore every law has support quotient lifting over the left-projection quotient, with no
support indexing and no decidable equality on the law-variable type. -/
theorem supportQuotientLift_leftProjection {α : Type} (E : MagmaLaw α) :
    SupportQuotientLift leftProjectionCtx E := by
  apply supportQuotientLift_of_globalSections leftProjectionCtx E
  intro β
  exact ⟨quotientRepresentativeData_leftProjection⟩
