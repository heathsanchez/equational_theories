import equational_theories.LeftProjectionCanonicalSection
import equational_theories.CompletenessSupportResources

open FreeMagma
open Law

def ambientLeftProjectionLaw (κ : Type) : MagmaLaw (Bool ⊕ κ) :=
  (Lf (Sum.inl false) ⋆ Lf (Sum.inl true)) ≃ Lf (Sum.inl false)

def ambientLeftProjectionCtx (κ : Type) : Ctx (Bool ⊕ κ) :=
  {ambientLeftProjectionLaw κ}

theorem derive'_ambientLeftProjection_first_eq {κ β : Type} {x y : FreeMagma β}
    (d : ambientLeftProjectionCtx κ ⊢' x ≃ y) : x.first = y.first := by
  letI : Magma β := ⟨fun a _ => a⟩
  have hmodel : β ⊧ ambientLeftProjectionCtx κ := by
    intro E hE φ
    have hEq : E = ambientLeftProjectionLaw κ := by
      simpa [ambientLeftProjectionCtx] using hE
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

def derive'_ambientLeftProjection_reduce {κ β : Type} :
    (t : FreeMagma β) → ambientLeftProjectionCtx κ ⊢' t ≃ Lf t.first
  | .Leaf a => derive'.Ref
  | .Fork l r => by
      let σ : Bool ⊕ κ → FreeMagma β := fun x =>
        match x with
        | Sum.inl false => l
        | Sum.inl true => r
        | Sum.inr _ => l
      have hmem : ambientLeftProjectionLaw κ ∈ ambientLeftProjectionCtx κ := by
        simp [ambientLeftProjectionCtx]
      have hax0 := derive'.SubstAx hmem σ
      have hax : ambientLeftProjectionCtx κ ⊢' (l ⋆ r) ≃ l := by
        simpa [ambientLeftProjectionLaw, σ, FreeMagma.evalInMagma] using hax0
      exact derive'.Trans hax (derive'_ambientLeftProjection_reduce l)

def FreeMagmaWithLaws.unembedAmbientLeftProjection {κ β : Type} :
    FreeMagmaWithLaws β (ambientLeftProjectionCtx κ) → FreeMagma β :=
  Quotient.lift (fun t => Lf t.first) (by
    intro x y h
    obtain ⟨d⟩ := h
    exact congrArg Lf (derive'_ambientLeftProjection_first_eq d))

theorem FreeMagmaWithLaws.embed_unembedAmbientLeftProjection {κ β : Type}
    (q : FreeMagmaWithLaws β (ambientLeftProjectionCtx κ)) :
    embed (ambientLeftProjectionCtx κ)
      (FreeMagmaWithLaws.unembedAmbientLeftProjection q) = q := by
  induction q using FreeMagmaWithLaws.inductionOn with
  | h t =>
      apply FreeMagmaWithLaws.eq.mpr
      exact ⟨derive'.Sym (derive'_ambientLeftProjection_reduce t)⟩

def quotientRepresentativeData_ambientLeftProjection {κ β : Type} :
    QuotientRepresentativeData (β := β) (ambientLeftProjectionCtx κ) where
  representative := FreeMagmaWithLaws.unembedAmbientLeftProjection
  embed_representative := FreeMagmaWithLaws.embed_unembedAmbientLeftProjection

def supportRetractionData_ambientLeftProjection (κ : Type) :
    SupportRetractionData (ambientLeftProjectionLaw κ) where
  retract := fun x =>
    match x with
    | Sum.inl false => ⟨Sum.inl false, by exact .inl (.inl rfl)⟩
    | Sum.inl true => ⟨Sum.inl true, by exact .inl (.inr rfl)⟩
    | Sum.inr _ => ⟨Sum.inl false, by exact .inl (.inl rfl)⟩
  retract_on := by
    intro s
    apply Subtype.ext
    rcases s with ⟨x, hx⟩
    cases x with
    | inl b => cases b <;> rfl
    | inr k =>
        have : False := by
          simpa [ambientLeftProjectionLaw, MagmaLaw.Mem, FreeMagma.Mem] using hx
        exact False.elim this

theorem supportQuotientLift_ambientLeftProjection {κ α : Type} (E : MagmaLaw α) :
    SupportQuotientLift (ambientLeftProjectionCtx κ) E := by
  apply supportQuotientLift_of_globalSections (ambientLeftProjectionCtx κ) E
  intro β
  exact ⟨quotientRepresentativeData_ambientLeftProjection⟩

theorem contextSupportRetract_ambientLeftProjection {κ : Type} :
    ∀ E, E ∈ ambientLeftProjectionCtx κ → SupportRetract E := by
  intro E hE
  have hEq : E = ambientLeftProjectionLaw κ := by
    simpa [ambientLeftProjectionCtx] using hE
  subst E
  exact (supportRetractionData_ambientLeftProjection κ).toSupportRetract

theorem Completeness'_ambientLeftProjection {κ β : Type}
    {E : MagmaLaw β}
    (h : ambientLeftProjectionCtx κ ⊧ E) :
    Nonempty (ambientLeftProjectionCtx κ ⊢' E) := by
  exact Completeness'_supportResources
    contextSupportRetract_ambientLeftProjection
    (fun A _ => supportQuotientLift_ambientLeftProjection A)
    h
