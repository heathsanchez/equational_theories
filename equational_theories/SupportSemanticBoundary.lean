import equational_theories.MagmaLaw

open FreeMagma
open Law

/-- A law has retractable support when the inclusion of its support subtype into the ambient
variable type admits a retraction. This is weaker and more structural than globally assuming
`DecidableEq` on the variable type. -/
def SupportRetract {α : Type} (E : MagmaLaw α) : Prop :=
  ∃ r : α → {a // E.Mem a}, ∀ s : {a // E.Mem a}, r s.1 = s

/-- Every valuation on a law's support can be extended to the full variable type. -/
def SupportValuationExtension {α : Type} (E : MagmaLaw α) (G : Type) : Prop :=
  ∀ ψ : {a // E.Mem a} → G, ∃ φ : α → G, ∀ s, φ s.1 = ψ s

/-- A support retraction extends support valuations into every codomain. -/
theorem supportValuationExtension_of_retract {α : Type} (E : MagmaLaw α)
    (hret : SupportRetract E) : ∀ G : Type, SupportValuationExtension E G := by
  intro G ψ
  obtain ⟨r, hr⟩ := hret
  refine ⟨fun a => ψ (r a), ?_⟩
  intro s
  rw [hr s]

/-- Conversely, if support valuations extend into every codomain, instantiate the codomain with
the support subtype itself and extend the identity valuation to obtain a retraction. -/
theorem supportRetract_of_allValuationExtensions {α : Type} (E : MagmaLaw α)
    (hext : ∀ G : Type, SupportValuationExtension E G) : SupportRetract E := by
  obtain ⟨r, hr⟩ := hext {a // E.Mem a} id
  exact ⟨r, hr⟩

/-- Support retractability is exactly uniform support-valuation extension. -/
theorem supportRetract_iff_allValuationExtensions {α : Type} (E : MagmaLaw α) :
    SupportRetract E ↔ ∀ G : Type, SupportValuationExtension E G := by
  exact ⟨supportValuationExtension_of_retract E,
    supportRetract_of_allValuationExtensions E⟩

/-- Satisfaction of the attached/support-normalized law always implies satisfaction of the
original law; this direction needs no decidable equality and no extension principle. -/
theorem satisfies_of_attach_noDecide {α G : Type} [Magma G] {E : MagmaLaw α} :
    G ⊧ E.attach → G ⊧ E := by
  intro h φ
  exact satisfiesPhi_attach.1 (h (fun s => φ s.1))

/-- The reverse semantic direction needs only extension of valuations from support, not decidable
equality itself. -/
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

/-- Hence support retractability is sufficient for semantic equivalence between a law and its
support-normalized form. -/
theorem satisfies_attach_iff_of_retract {α G : Type} [Magma G] {E : MagmaLaw α}
    (hret : SupportRetract E) : G ⊧ E.attach ↔ G ⊧ E := by
  refine ⟨satisfies_of_attach_noDecide, ?_⟩
  exact satisfies_attach_of_supportExtension
    (supportValuationExtension_of_retract E G hret)

/-- Decidable equality is one sufficient mechanism for constructing a support retraction: preserve
support variables exactly and send all off-support variables to one visible support variable. -/
theorem supportRetract_of_decidableEq {α : Type} [DecidableEq α] (E : MagmaLaw α) :
    SupportRetract E := by
  let d : {a // E.Mem a} := ⟨E.lhs.first, .inl E.lhs.first_mem⟩
  let r : α → {a // E.Mem a} := fun a => if h : E.Mem a then ⟨a, h⟩ else d
  refine ⟨r, ?_⟩
  intro s
  apply Subtype.ext
  simp [r, s.property]

/-- Recover the existing semantic equivalence from the strictly weaker support-retraction
interface. -/
theorem satisfies_attach_via_decidableRetract {α G : Type} [DecidableEq α] [Magma G]
    {E : MagmaLaw α} : G ⊧ E.attach ↔ G ⊧ E :=
  satisfies_attach_iff_of_retract (supportRetract_of_decidableEq E)
