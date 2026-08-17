import equational_theories.CompletenessSupportResources

open FreeMagma
open Law

/-- Commutativity embedded in an ambient type carrying an arbitrary extra component. -/
def ambientCommutativityLaw (κ : Type) : MagmaLaw (Bool ⊕ κ) :=
  (Lf (Sum.inl false) ⋆ Lf (Sum.inl true)) ≃
    (Lf (Sum.inl true) ⋆ Lf (Sum.inl false))

def ambientCommutativityCtx (κ : Type) : Ctx (Bool ⊕ κ) :=
  {ambientCommutativityLaw κ}

/-- O37 production route, part 1: the two visible axiom variables admit a constructive support
retraction even though the ambient `κ` is arbitrary. -/
theorem supportRetract_ambientCommutativity (κ : Type) :
    SupportRetract (ambientCommutativityLaw κ) := by
  let r : Bool ⊕ κ → {a // (ambientCommutativityLaw κ).Mem a} := fun x =>
    match x with
    | Sum.inl false => ⟨Sum.inl false, by simp [ambientCommutativityLaw, MagmaLaw.Mem, FreeMagma.Mem]⟩
    | Sum.inl true => ⟨Sum.inl true, by simp [ambientCommutativityLaw, MagmaLaw.Mem, FreeMagma.Mem]⟩
    | Sum.inr _ => ⟨Sum.inl false, by simp [ambientCommutativityLaw, MagmaLaw.Mem, FreeMagma.Mem]⟩
  refine ⟨r, ?_⟩
  intro s
  apply Subtype.ext
  rcases s with ⟨x, hx⟩
  cases x with
  | inl b => cases b <;> rfl
  | inr k =>
      have : False := by
        simpa [ambientCommutativityLaw, MagmaLaw.Mem, FreeMagma.Mem] using hx
      exact False.elim this

/-- O37 production route, part 2: choose representatives only for the two variables the axiom can
observe. No equality/order on the target variables or on ambient `κ` is needed. -/
theorem supportQuotientLift_ambientCommutativity (κ : Type) :
    SupportQuotientLift (ambientCommutativityCtx κ) (ambientCommutativityLaw κ) := by
  intro β φ
  obtain ⟨r0, hr0⟩ := Quotient.exists_rep (φ (Sum.inl false))
  obtain ⟨r1, hr1⟩ := Quotient.exists_rep (φ (Sum.inl true))
  let σ : (a : Bool ⊕ κ) → (ambientCommutativityLaw κ).Mem a → FreeMagma β :=
    fun a ha =>
      match a with
      | Sum.inl false => r0
      | Sum.inl true => r1
      | Sum.inr _ => False.elim (by
          simpa [ambientCommutativityLaw, MagmaLaw.Mem, FreeMagma.Mem] using ha)
  refine ⟨σ, ?_⟩
  intro a ha
  cases a with
  | inl b =>
      cases b
      · exact hr0.symm
      · exact hr1.symm
  | inr k =>
      exact False.elim (by
        simpa [ambientCommutativityLaw, MagmaLaw.Mem, FreeMagma.Mem] using ha)

/-- The singleton context exposes the two O10 resources by inspection. -/
theorem contextSupportResources_ambientCommutativity (κ : Type) :
    (∀ E, E ∈ ambientCommutativityCtx κ → SupportRetract E) ∧
    (∀ E, E ∈ ambientCommutativityCtx κ → SupportQuotientLift (ambientCommutativityCtx κ) E) := by
  constructor
  · intro E hE
    have hEq : E = ambientCommutativityLaw κ := by
      simpa [ambientCommutativityCtx] using hE
    subst E
    exact supportRetract_ambientCommutativity κ
  · intro E hE
    have hEq : E = ambientCommutativityLaw κ := by
      simpa [ambientCommutativityCtx] using hE
    subst E
    exact supportQuotientLift_ambientCommutativity κ

/-- O37: prospective ROUTE SELECT test. For commutativity, choose the finite-support resource route
before attempting a sorting/canonical-normalizer route. This yields choice-free completeness for an
ambient type containing arbitrary `κ`, with no `DecidableEq κ` and no comparison assumption on the
target variable type `β`. -/
theorem Completeness'_ambientCommutativity_resourceRoute {κ β : Type} {E : MagmaLaw β}
    (h : ambientCommutativityCtx κ ⊧ E) :
    Nonempty (ambientCommutativityCtx κ ⊢' E) := by
  obtain ⟨hret, hlift⟩ := contextSupportResources_ambientCommutativity κ
  exact Completeness'_supportResources hret hlift h
