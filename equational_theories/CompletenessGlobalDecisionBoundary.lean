import equational_theories.CompletenessSupportResources

open FreeMagma
open Law

def GlobalDecisionOracle := (p : Prop) → Decidable p

def decidableEq_of_globalDecisionOracle
    (oracle : GlobalDecisionOracle) (α : Type) : DecidableEq α :=
  fun a b => oracle (a = b)

theorem FreeMagmaWithLaws.isModel_of_globalDecisionOracle {α : Type}
    (oracle : GlobalDecisionOracle) (β : Type) (Γ : Ctx α) :
    FreeMagmaWithLaws β Γ ⊧ Γ := by
  letI : DecidableEq α := decidableEq_of_globalDecisionOracle oracle α
  exact FreeMagmaWithLaws.isModel_decidableVars_via_resources β Γ

theorem Completeness'_of_globalDecisionOracle {α β : Type}
    (oracle : GlobalDecisionOracle) {Γ : Ctx α} {E : MagmaLaw β}
    (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) := by
  apply FreeMagmaWithLaws.isDerives
  exact h _ (FreeMagmaWithLaws.isModel_of_globalDecisionOracle oracle β Γ)
