import equational_theories.MagmaLaw

open FreeMagma
open Law

/-- Pointwise lifting of one surjection over one fixed index type. -/
def FamilyLiftAt {A B : Type} (ι : Type) (q : A → B) : Prop :=
  ∀ f : ι → B, ∃ g : ι → A, ∀ i, f i = q (g i)

/-- Choice restricted to one fixed index type. -/
def IndexedChoiceSchema (ι : Type) : Prop :=
  ∀ P : ι → Type, (∀ i, Nonempty (P i)) → Nonempty (∀ i, P i)

/-- For a fixed index type, lifting every surjection over that index implies choice over that index. -/
theorem indexedChoice_of_surjective_familyLiftAt (ι : Type)
    (hLift : ∀ {A B : Type} (q : A → B), Function.Surjective q → FamilyLiftAt ι q) :
    IndexedChoiceSchema ι := by
  intro P hne
  let q : Sigma P → ι := fun z ↦ z.1
  have hq : Function.Surjective q := by
    intro i
    obtain ⟨x⟩ := hne i
    exact ⟨⟨i, x⟩, rfl⟩
  obtain ⟨g, hg⟩ := hLift q hq id
  refine ⟨fun i ↦ ?_⟩
  have hi : i = (g i).1 := hg i
  exact hi.symm ▸ (g i).2

/-- Conversely, indexed choice lifts every surjection over that fixed index type. -/
theorem surjective_familyLiftAt_of_indexedChoice (ι : Type)
    (hChoice : IndexedChoiceSchema ι) :
    ∀ {A B : Type} (q : A → B), Function.Surjective q → FamilyLiftAt ι q := by
  intro A B q hq f
  let P : ι → Type := fun i ↦ {a : A // f i = q a}
  have hP : ∀ i, Nonempty (P i) := by
    intro i
    obtain ⟨a, ha⟩ := hq (f i)
    exact ⟨⟨a, ha.symm⟩⟩
  obtain ⟨g⟩ := hChoice P hP
  exact ⟨fun i ↦ (g i).1, fun i ↦ (g i).2⟩

/-- Fixed-index family lifting of arbitrary surjections is exactly fixed-index choice. -/
theorem surjectiveFamilyLiftAt_iff_indexedChoice (ι : Type) :
    (∀ {A B : Type} (q : A → B), Function.Surjective q → FamilyLiftAt ι q) ↔
      IndexedChoiceSchema ι := by
  exact ⟨indexedChoice_of_surjective_familyLiftAt ι,
    surjective_familyLiftAt_of_indexedChoice ι⟩

/-- Finite index types support Type-valued choice constructively by recursion. -/
theorem fin_indexedChoice : ∀ n : Nat, IndexedChoiceSchema (Fin n)
  | 0 => by
      intro P h
      exact ⟨fun i => Fin.elim0 i⟩
  | n + 1 => by
      intro P h
      obtain ⟨x0⟩ := h 0
      have htail : ∀ i : Fin n, Nonempty (P i.succ) := fun i => h i.succ
      obtain ⟨g⟩ := fin_indexedChoice n (fun i => P i.succ) htail
      exact ⟨fun i => Fin.cases x0 g i⟩

/-- Indexed choice transports across an equivalence of index types. -/
theorem indexedChoice_equiv {ι κ : Type} (e : ι ≃ κ)
    (h : IndexedChoiceSchema ι) : IndexedChoiceSchema κ := by
  intro P hP
  have hQ : ∀ i : ι, Nonempty (P (e i)) := fun i => hP (e i)
  obtain ⟨g⟩ := h (fun i => P (e i)) hQ
  refine ⟨fun k => ?_⟩
  simpa using g (e.symm k)

/-- With decidable variable equality, the support subtype of a law becomes explicitly equivalent
to `Fin n`; this is the exact Type-level finiteness resource used to make support-indexed choice
constructive. -/
theorem lawSupport_indexedChoice {α : Type} [DecidableEq α] (E : MagmaLaw α) :
    IndexedChoiceSchema {a // E.Mem a} := by
  exact indexedChoice_equiv E.finEquiv (fin_indexedChoice E.elems.1.length)

/-- Consequently, with decidable equality, every pointwise surjection can be lifted over the
support subtype of a law without invoking global choice. -/
theorem lawSupport_surjectiveFamilyLiftAt {α : Type} [DecidableEq α] (E : MagmaLaw α) :
    ∀ {A B : Type} (q : A → B), Function.Surjective q →
      FamilyLiftAt {a // E.Mem a} q :=
  surjective_familyLiftAt_of_indexedChoice _ (lawSupport_indexedChoice E)
