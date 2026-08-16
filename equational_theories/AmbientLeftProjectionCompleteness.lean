import equational_theories.LeftProjectionCanonicalSection
import equational_theories.CompletenessSupportResources

open FreeMagma
open Law

/-- Left projection embedded in an ambient variable type with an arbitrary extra component. -/
def ambientLeftProjectionLaw (κ : Type) : MagmaLaw (Bool ⊕ κ) :=
  (Lf (Sum.inl false) ⋆ Lf (Sum.inl true)) ≃ Lf (Sum.inl false)

def ambientLeftProjectionCtx (κ : Type) : Ctx (Bool ⊕ κ) :=
  {ambientLeftProjectionLaw κ}

/-- Derivability in the ambient left-projection theory still preserves the first leaf. No equality
structure on κ is used. Dependent recursion keeps the indexed derivation endpoints explicit. -/
def derive'_ambientLeftProjection_first_eq {κ β : Type} :
    {x y : FreeMagma β} →
      (ambientLeftProjectionCtx κ ⊢' x ≃ y) → x.first = y.first
  | _, _, .SubstAx (E := E) h σ => by
      have hE : E = ambientLeftProjectionLaw κ := by
        simpa [ambientLeftProjectionCtx] using h
      subst E
      rfl
  | _, _, .Ref => rfl
  | _, _, .Sym d => (derive'_ambientLeftProjection_first_eq d).symm
  | _, _, .Trans d₁ d₂ =>
      (derive'_ambientLeftProjection_first_eq d₁).trans
        (derive'_ambientLeftProjection_first_eq d₂)
  | _, _, .Cong d₁ d₂ => derive'_ambientLeftProjection_first_eq d₁

/-- Every term reduces derivably to the leaf containing its first variable. This is Type-valued
proof data, constructed directly by syntax recursion. -/
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

/-- Canonical representative for the ambient theory's quotient. -/
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

/-- The two actual support points can be retracted from `Bool ⊕ κ` by structural case analysis;
no `DecidableEq κ` is involved. -/
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
          simpa [ambientLeftProjectionLaw, FreeMagma.Mem] using hx
        exact False.elim this

/-- All laws over this quotient get O10's representative-selection resource from the global
canonical section, independently of their own support representation. -/
theorem supportQuotientLift_ambientLeftProjection {κ α : Type} (E : MagmaLaw α) :
    SupportQuotientLift (ambientLeftProjectionCtx κ) E := by
  apply supportQuotientLift_of_globalSections (ambientLeftProjectionCtx κ) E
  intro β
  exact ⟨quotientRepresentativeData_ambientLeftProjection⟩

/-- The context's only axiom has a constructive support retraction even though the ambient type
contains arbitrary κ. -/
theorem contextSupportRetract_ambientLeftProjection {κ : Type} :
    ∀ E, E ∈ ambientLeftProjectionCtx κ → SupportRetract E := by
  intro E hE
  have hEq : E = ambientLeftProjectionLaw κ := by
    simpa [ambientLeftProjectionCtx] using hE
  subst E
  exact (supportRetractionData_ambientLeftProjection κ).toSupportRetract

/-- Choice-free Type-0 completeness for a nonempty theory whose ambient variable type is
`Bool ⊕ κ`, with κ completely arbitrary and no `[DecidableEq κ]` assumption. -/
theorem Completeness'_ambientLeftProjection {κ β : Type}
    {E : MagmaLaw β}
    (h : ambientLeftProjectionCtx κ ⊧ E) :
    Nonempty (ambientLeftProjectionCtx κ ⊢' E) := by
  exact Completeness'_supportResources
    contextSupportRetract_ambientLeftProjection
    (fun A _ => supportQuotientLift_ambientLeftProjection A)
    h
