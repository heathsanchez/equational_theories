import equational_theories.CompletenessSupportResources

open FreeMagma
open Law

/-- Computational finite indexing of one law's support. Unlike the repository's existing
`MagmaLaw.finEquiv`, this is supplied as explicit data rather than extracted by an operation whose
axiom audit includes `Classical.choice`. -/
structure SupportIndexing {α : Type} (E : MagmaLaw α) where
  n : Nat
  equiv : {a // E.Mem a} ≃ Fin n

/-- Constructively choose from a Type-valued family indexed by `Fin n`. -/
def chooseFinFamily : ∀ {n : Nat} (P : Fin n → Type),
    (∀ i, Nonempty (P i)) → Nonempty (∀ i, P i)
  | 0, P, h => ⟨fun i => Fin.elim0 i⟩
  | n + 1, P, h => by
      obtain ⟨x0⟩ := h 0
      obtain ⟨g⟩ := chooseFinFamily (fun i : Fin n => P i.succ) (fun i => h i.succ)
      exact ⟨fun i => Fin.cases x0 g i⟩

/-- Explicit computational support indexing is enough to choose quotient representatives on all
variables visible to one law, with no global `DecidableEq` and no `Classical.choice`. -/
theorem supportQuotientLift_of_indexing {δ α : Type}
    (Γ : Ctx δ) (E : MagmaLaw α) (idx : SupportIndexing E) :
    SupportQuotientLift Γ E := by
  intro β φ
  let P : Fin idx.n → Type := fun i =>
    {r : FreeMagma β // φ (idx.equiv.symm i).1 = embed Γ r}
  have hP : ∀ i, Nonempty (P i) := by
    intro i
    obtain ⟨r, hr⟩ := Quotient.exists_rep (φ (idx.equiv.symm i).1)
    exact ⟨⟨r, hr.symm⟩⟩
  obtain ⟨g⟩ := chooseFinFamily P hP
  refine ⟨fun a ha => (g (idx.equiv ⟨a, ha⟩)).1, ?_⟩
  intro a ha
  simpa using (g (idx.equiv ⟨a, ha⟩)).2

/-- Explicit support indexing also supplies a support retraction without ambient decidable equality:
map every ambient variable to a fixed support point, except support points are recovered by the
indexing inverse only when a support witness is already available. The retraction itself therefore
needs an ambient map whose restriction is the support identity; we package that separately. -/
structure RetractableSupportIndexing {α : Type} (E : MagmaLaw α) extends SupportIndexing E where
  retract : α → {a // E.Mem a}
  retract_on : ∀ s : {a // E.Mem a}, retract s.1 = s

/-- A retractable computational finite indexing supplies both O10 resources. -/
theorem supportResources_of_indexing {δ α : Type}
    (Γ : Ctx δ) (E : MagmaLaw α) (idx : RetractableSupportIndexing E) :
    SupportRetract E ∧ SupportQuotientLift Γ E := by
  exact ⟨⟨idx.retract, idx.retract_on⟩,
    supportQuotientLift_of_indexing Γ E idx.toSupportIndexing⟩

/-- Context-level computational support data. This is strictly an explicit-data assumption, not a
proposition asserting mere finite cardinality. -/
def ContextRetractableSupportIndexing {α : Type} (Γ : Ctx α) : Type :=
  (E : MagmaLaw α) → E ∈ Γ → RetractableSupportIndexing E

/-- Choice-free model construction for contexts carrying explicit retractable finite support
indices, with no global `[DecidableEq α]`. -/
theorem FreeMagmaWithLaws.isModel_indexedSupport {α : Type}
    (β : Type) (Γ : Ctx α) (idx : ContextRetractableSupportIndexing Γ) :
    FreeMagmaWithLaws β Γ ⊧ Γ := by
  apply FreeMagmaWithLaws.isModel_supportResources β Γ
  · intro E hE
    exact ⟨(idx E hE).retract, (idx E hE).retract_on⟩
  · intro E hE
    exact supportQuotientLift_of_indexing Γ E (idx E hE).toSupportIndexing

/-- Type-0 completeness for explicitly indexed finite-support contexts, again without a global
ambient equality decision. -/
theorem Completeness'_indexedSupport {α β : Type}
    {Γ : Ctx α} {E : MagmaLaw β}
    (idx : ContextRetractableSupportIndexing Γ)
    (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) := by
  apply Completeness'_supportResources
    (fun A hA => ⟨(idx A hA).retract, (idx A hA).retract_on⟩)
    (fun A hA => supportQuotientLift_of_indexing Γ A (idx A hA).toSupportIndexing)
    h
