import equational_theories.CanonicalQuotientSection

open FreeMagma
open Law

/-- The nontrivial equational theory x ◇ y = x. -/
def leftProjectionLaw : MagmaLaw Bool :=
  (Lf false ⋆ Lf true) ≃ Lf false

def leftProjectionCtx : Ctx Bool :=
  {leftProjectionLaw}

/-- Every derivable equality in the left-projection theory preserves the first leaf.
Rather than recurse over the indexed derivation family, interpret the proof in the concrete
left-projection magma on β and use soundness. -/
theorem derive'_leftProjection_first_eq {β : Type} {x y : FreeMagma β}
    (d : leftProjectionCtx ⊢' x ≃ y) : x.first = y.first := by
  letI : Magma β := ⟨fun a _ => a⟩
  have hmodel : β ⊧ leftProjectionCtx := by
    intro E hE φ
    have hEq : E = leftProjectionLaw := by
      simpa [leftProjectionCtx] using hE
    subst E
    rfl
  have eval_first : ∀ t : FreeMagma β, t ⬝ (fun b => b) = t.first := by
    intro t
    induction t with
    | Leaf a => rfl
    | Fork l r ihl ihr =>
        simpa [FreeMagma.evalInMagma] using ihl
  have hxy : x ⬝ (fun b => b) = y ⬝ (fun b => b) :=
    (Soundness'_u d hmodel) (fun b => b)
  calc
    x.first = x ⬝ (fun b => b) := (eval_first x).symm
    _ = y ⬝ (fun b => b) := hxy
    _ = y.first := eval_first y

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
