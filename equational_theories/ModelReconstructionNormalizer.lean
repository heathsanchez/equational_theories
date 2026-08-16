import equational_theories.InvariantReconstructionNormalizer

open FreeMagma
open Law

/-- O33 search interface. The observable is no longer supplied explicitly: it is evaluation into a
concrete magma model of the context. Soundness then supplies preservation under every derivation. -/
structure ModelReconstructionPackage {δ β : Type} (Γ : Ctx δ) where
  I : Type
  magma : Magma I
  leaf : β → I
  model : @satisfiesSet δ I magma Γ
  reconstruct : I → FreeMagma β
  reduces : ∀ t : FreeMagma β,
    Γ ⊢' t ≃ reconstruct (@FreeMagma.evalInMagma β I magma leaf t)

/-- A model/reconstruction package automatically compiles into O32's invariant/reconstruction
interface; the `observe_respects` field is generated solely by soundness. -/
def InvariantReconstructionData.ofModelPackage {δ β : Type} {Γ : Ctx δ}
    (p : ModelReconstructionPackage (β := β) Γ) :
    InvariantReconstructionData (β := β) (I := p.I) Γ := by
  letI : Magma p.I := p.magma
  refine {
    observe := fun t => t ⬝ p.leaf
    reconstruct := p.reconstruct
    observe_respects := ?_
    reduces := ?_ }
  · intro x y h
    obtain ⟨d⟩ := h
    exact (Soundness'_u d p.model) p.leaf
  · intro t
    exact p.reduces t

/-- Hence a model/reconstruction package in every codomain is sufficient for context-wide
constructive quotient sections. -/
theorem contextQuotientSections_of_modelReconstruction {δ : Type} {Γ : Ctx δ}
    (h : ∀ β : Type, Nonempty (ModelReconstructionPackage (β := β) Γ)) :
    ContextQuotientSections Γ := by
  apply contextQuotientSections_of_invariantReconstruction
  intro β
  obtain ⟨p⟩ := h β
  exact ⟨p.I, ⟨InvariantReconstructionData.ofModelPackage p⟩⟩

/-- And support retraction plus model/reconstruction packages is directly a choice-free
completeness route. -/
theorem Completeness'_modelReconstruction {δ β : Type}
    {Γ : Ctx δ} {E : MagmaLaw β}
    (hret : ∀ A, A ∈ Γ → SupportRetract A)
    (hmodel : ∀ γ : Type, Nonempty (ModelReconstructionPackage (β := γ) Γ))
    (h : Γ ⊧ E) :
    Nonempty (Γ ⊢' E) := by
  exact Completeness'_canonicalSections hret
    (contextQuotientSections_of_modelReconstruction hmodel) h

/-- Nonempty words form the natural semantic model for associativity. -/
abbrev NonemptyWord (β : Type) := {xs : List β // xs ≠ []}

private theorem append_nonempty_left {β : Type} {xs ys : List β} (hxs : xs ≠ []) :
    xs ++ ys ≠ [] := by
  cases xs with
  | nil => exact False.elim (hxs rfl)
  | cons a as => simp

instance nonemptyWordMagma {β : Type} : Magma (NonemptyWord β) where
  op x y := ⟨x.1 ++ y.1, append_nonempty_left x.2⟩

private def nonemptyWordLeaf {β : Type} (b : β) : NonemptyWord β :=
  ⟨[b], by simp⟩

private theorem nonemptyWord_assoc_model {β : Type} :
    NonemptyWord β ⊧ associativityCtx := by
  intro E hE φ
  have hEq : E = associativityLaw := by
    simpa [associativityCtx] using hE
  subst E
  apply Subtype.ext
  exact List.append_assoc _ _ _

private theorem eval_nonemptyWord_eq_toList {β : Type} :
    ∀ t : FreeMagma β,
      t ⬝ nonemptyWordLeaf =
        (⟨t.toList, by
          intro ht
          have hz : t.toList.length = 0 := by simp [ht]
          rw [FreeMagma.toList_length] at hz
          exact t.length_ne_0 hz⟩ : NonemptyWord β)
  | .Leaf a => by
      apply Subtype.ext
      rfl
  | .Fork l r => by
      apply Subtype.ext
      change ((l ⬝ nonemptyWordLeaf).1 ++ (r ⬝ nonemptyWordLeaf).1) = l.toList ++ r.toList
      rw [congrArg Subtype.val (eval_nonemptyWord_eq_toList l),
          congrArg Subtype.val (eval_nonemptyWord_eq_toList r)]

/-- Associativity now factors through the smaller O33 interface: one concrete model, singleton leaf
encoding, canonical right-associated reconstruction, and the already verified reduction proof. -/
def modelReconstructionPackage_associativity {β : Type} :
    ModelReconstructionPackage (β := β) associativityCtx where
  I := NonemptyWord β
  magma := nonemptyWordMagma
  leaf := nonemptyWordLeaf
  model := nonemptyWord_assoc_model
  reconstruct := fun w => rightAssocList w.1 w.2
  reduces := by
    intro t
    have heval := eval_nonemptyWord_eq_toList t
    have hred := derive'_associativity_reduce t
    simpa [associativityNormalize, heval] using hred

/-- Validation: O30's global quotient-section result can be regenerated without manually proving
invariant preservation; soundness derives it from the nonempty-word model. -/
theorem contextQuotientSections_associativity_viaModel :
    ContextQuotientSections associativityCtx := by
  apply contextQuotientSections_of_modelReconstruction
  intro β
  exact ⟨modelReconstructionPackage_associativity⟩
