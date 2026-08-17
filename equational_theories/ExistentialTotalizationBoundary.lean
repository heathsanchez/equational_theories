import equational_theories.SupportLocalDerivation

open FreeMagma
open Law

def PropExcludedMiddleO45 : Prop := ∀ p : Prop, p ∨ ¬ p

def GlobalDecisionOracleO45 := (p : Prop) → Decidable p

/-- A total substitution extending one support-local assignment for one axiom. -/
def TotalSupportExtension {α β : Type} (E : MagmaLaw α)
    (σ : (a : α) → E.Mem a → FreeMagma β) :=
  {τ : α → FreeMagma β // ∀ a (ha : E.Mem a), τ a = σ a ha}

/-- Prop EM can decide support membership pointwise while the decision object remains under
`Nonempty` (hence in Prop). -/
theorem pointwiseSupportDecision_of_em_o45
    (hem : PropExcludedMiddleO45) {α : Type} (E : MagmaLaw α) :
    ∀ a : α, Nonempty (Decidable (E.Mem a)) := by
  intro a
  rcases hem (E.Mem a) with h | h
  · exact ⟨isTrue h⟩
  · exact ⟨isFalse h⟩

/-- A Type-valued decision oracle can construct an actual total extension. This is the positive
control for the O45 separator. -/
def totalSupportExtension_of_globalDecision_o45
    (decideP : GlobalDecisionOracleO45) {α β : Type} (E : MagmaLaw α)
    (σ : (a : α) → E.Mem a → FreeMagma β) :
    TotalSupportExtension E σ := by
  let d : FreeMagma β := σ E.lhs.first (.inl E.lhs.first_mem)
  let τ : α → FreeMagma β := fun a =>
    match decideP (E.Mem a) with
    | isTrue ha => σ a ha
    | isFalse _ => d
  refine ⟨τ, ?_⟩
  intro a ha
  change (match decideP (E.Mem a) with
    | isTrue h => σ a h
    | isFalse _ => d) = σ a ha
  cases hdec : decideP (E.Mem a) with
  | isTrue h =>
      simp [hdec]
  | isFalse h =>
      exact False.elim (h ha)

/-- O45 negative control. Merely wrapping the desired total function in `Nonempty` does not let a
Prop-valued excluded-middle proof be eliminated while constructing the function's values.

`fail_if_success` makes this a verifier-backed rejection test: if Lean ever accepts the attempted
Prop-to-Type extraction below, this file fails to build and the boundary must be revisited. -/
example (hem : PropExcludedMiddleO45) {α β : Type} (E : MagmaLaw α)
    (σ : (a : α) → E.Mem a → FreeMagma β) : True := by
  fail_if_success
    have _h : Nonempty (TotalSupportExtension E σ) := by
      let d : FreeMagma β := σ E.lhs.first (.inl E.lhs.first_mem)
      apply Nonempty.intro
      let τ : α → FreeMagma β := fun a => by
        rcases hem (E.Mem a) with ha | hna
        · exact σ a ha
        · exact d
      refine ⟨τ, ?_⟩
      intro a ha
      simp [τ, ha]
  trivial

/-- The same existential wrapper is constructible once decision data is supplied in Type. -/
theorem nonemptyTotalSupportExtension_of_globalDecision_o45
    (decideP : GlobalDecisionOracleO45) {α β : Type} (E : MagmaLaw α)
    (σ : (a : α) → E.Mem a → FreeMagma β) :
    Nonempty (TotalSupportExtension E σ) :=
  ⟨totalSupportExtension_of_globalDecision_o45 decideP E σ⟩
