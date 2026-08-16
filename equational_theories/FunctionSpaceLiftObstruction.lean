import equational_theories.Completeness

/-- `FamilyLift q` says that postcomposition by `q : A → B` is surjective on *every* function
space: every indexed family of `B`-values admits a pointwise lift to `A`.

This is the abstract shape of `PhiAsSubst_aux`: `q` is `embed Γ`, and the index type is the
variable type of the valuation. -/
def FamilyLift {A B : Type} (q : A → B) : Prop :=
  ∀ (ι : Type) (f : ι → B), ∃ g : ι → A, ∀ i, f i = q (g i)

/-- A proposition-level schema for choosing an element from every member of an arbitrary
Type-valued family, assuming each member is merely nonempty. -/
def TypeChoiceSchema : Prop :=
  ∀ (ι : Type) (P : ι → Type), (∀ i, Nonempty (P i)) → Nonempty (∀ i, P i)

/-- If every surjection admits arbitrary function-space lifting, then the Type-valued choice schema
follows. The proof uses the dependent projection `Sigma P → ι` as the surjection. -/
theorem typeChoiceSchema_of_surjective_familyLift
    (hLift : ∀ {A B : Type} (q : A → B), Function.Surjective q → FamilyLift q) :
    TypeChoiceSchema := by
  intro ι P hne
  let q : Sigma P → ι := fun z ↦ z.1
  have hq : Function.Surjective q := by
    intro i
    obtain ⟨x⟩ := hne i
    exact ⟨⟨i, x⟩, rfl⟩
  obtain ⟨g, hg⟩ := hLift q hq ι id
  refine ⟨fun i ↦ ?_⟩
  have hi : i = (g i).1 := hg i
  exact hi.symm ▸ (g i).2

/-- Conversely, the Type-valued choice schema lifts every surjection through every function space:
choose one preimage in the fiber over each value `f i`. -/
theorem surjective_familyLift_of_typeChoiceSchema
    (hChoice : TypeChoiceSchema) :
    ∀ {A B : Type} (q : A → B), Function.Surjective q → FamilyLift q := by
  intro A B q hq ι f
  let P : ι → Type := fun i ↦ {a : A // f i = q a}
  have hP : ∀ i, Nonempty (P i) := by
    intro i
    obtain ⟨a, ha⟩ := hq (f i)
    exact ⟨⟨a, ha.symm⟩⟩
  obtain ⟨g⟩ := hChoice ι P hP
  exact ⟨fun i ↦ (g i).1, fun i ↦ (g i).2⟩

/-- Arbitrary function-space lifting of surjections is propositionally equivalent to the
Type-valued choice schema. Both directions are proved without assuming choice: choice appears only
as the proposition being characterized. -/
theorem surjectiveFamilyLift_iff_typeChoiceSchema :
    (∀ {A B : Type} (q : A → B), Function.Surjective q → FamilyLift q) ↔ TypeChoiceSchema := by
  exact ⟨typeChoiceSchema_of_surjective_familyLift,
    surjective_familyLift_of_typeChoiceSchema⟩

/-- The quotient embedding used by completeness is pointwise surjective without choice: each
individual quotient value has a representative. -/
theorem embed_surjective {α β : Type} (Γ : Ctx α) :
    Function.Surjective (embed Γ : FreeMagma β → FreeMagmaWithLaws β Γ) := by
  intro x
  obtain ⟨r, hr⟩ := Quotient.exists_rep x
  exact ⟨r, hr.symm⟩

/-- `PhiAsSubst_aux` is exactly the one-index-type function-space lifting instance needed for the
quotient embedding. The baseline implementation obtains it using `Classical.axiomOfChoice`. -/
theorem phiAsSubst_aux_is_familyLift_instance {α β γ : Type}
    (Γ : Ctx α) (φ : β → FreeMagmaWithLaws γ Γ) :
    ∃ σ : β → FreeMagma γ, ∀ x, φ x = embed Γ (σ x) :=
  PhiAsSubst_aux Γ φ

/-- Conversely, a `FamilyLift` hypothesis for `embed Γ` immediately supplies the global
representative function used by completeness. -/
theorem phiAsSubst_aux_of_familyLift {α β γ : Type}
    (Γ : Ctx α)
    (h : FamilyLift (embed Γ : FreeMagma γ → FreeMagmaWithLaws γ Γ))
    (φ : β → FreeMagmaWithLaws γ Γ) :
    ∃ σ : β → FreeMagma γ, ∀ x, φ x = embed Γ (σ x) := by
  exact h β φ
