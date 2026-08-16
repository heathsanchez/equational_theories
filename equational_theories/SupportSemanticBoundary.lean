import equational_theories.MagmaLaw

open FreeMagma
open Law

def SupportRetract {α : Type} (E : MagmaLaw α) : Prop :=
  ∃ r : α → {a // E.Mem a}, ∀ s : {a // E.Mem a}, r s.1 = s

def SupportValuationExtension {α : Type} (E : MagmaLaw α) (G : Type) : Prop :=
  ∀ ψ : {a // E.Mem a} → G, ∃ φ : α → G, ∀ s, φ s.1 = ψ s

theorem supportValuationExtension_of_retract {α : Type} (E : MagmaLaw α)
    (hret : SupportRetract E) : ∀ G : Type, SupportValuationExtension E G := by
  intro G ψ
  obtain ⟨r, hr⟩ := hret
  refine ⟨fun a => ψ (r a), ?_⟩
  intro s
  exact congrArg ψ (hr s)

theorem supportRetract_of_allValuationExtensions {α : Type} (E : MagmaLaw α)
    (hext : ∀ G : Type, SupportValuationExtension E G) : SupportRetract E := by
  obtain ⟨r, hr⟩ := hext {a // E.Mem a} id
  exact ⟨r, hr⟩

theorem supportRetract_iff_allValuationExtensions {α : Type} (E : MagmaLaw α) :
    SupportRetract E ↔ ∀ G : Type, SupportValuationExtension E G := by
  exact ⟨supportValuationExtension_of_retract E,
    supportRetract_of_allValuationExtensions E⟩

theorem satisfies_of_attach_noDecide {α G : Type} [Magma G] {E : MagmaLaw α} :
    G ⊧ E.attach → G ⊧ E := by
  intro h φ
  exact satisfiesPhi_attach.1 (h (fun s => φ s.1))

theorem satisfies_attach_of_supportExtension {α G : Type} [Magma G] {E : MagmaLaw α}
    (hext : SupportValuationExtension E G) : G ⊧ E → G ⊧ E.attach := by
  intro h ψ
  obtain ⟨φ, hφ⟩ := hext ψ
  have hfun : (fun s : {a // E.Mem a} => φ s.1) = ψ := by
    funext s
    exact hφ s
  have hatt : satisfiesPhi (fun s : {a // E.Mem a} => φ s.1) E.attach :=
    satisfiesPhi_attach.2 (h φ)
  simpa [hfun] using hatt

theorem satisfies_attach_iff_of_retract {α G : Type} [Magma G] {E : MagmaLaw α}
    (hret : SupportRetract E) : G ⊧ E.attach ↔ G ⊧ E := by
  refine ⟨satisfies_of_attach_noDecide, ?_⟩
  exact satisfies_attach_of_supportExtension
    (supportValuationExtension_of_retract E hret G)

theorem supportRetract_of_decidableEq {α : Type} [DecidableEq α] (E : MagmaLaw α) :
    SupportRetract E := by
  let d : {a // E.Mem a} := ⟨E.lhs.first, .inl E.lhs.first_mem⟩
  let r : α → {a // E.Mem a} := fun a => if h : E.Mem a then ⟨a, h⟩ else d
  refine ⟨r, ?_⟩
  intro s
  apply Subtype.ext
  simp [r, s.property]

theorem satisfies_attach_via_decidableRetract {α G : Type} [DecidableEq α] [Magma G]
    {E : MagmaLaw α} : G ⊧ E.attach ↔ G ⊧ E :=
  satisfies_attach_iff_of_retract (supportRetract_of_decidableEq E)
