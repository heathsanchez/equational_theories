import equational_theories.AmbientCommutativityResourceCompleteness
import equational_theories.SupportLocalDerivation

open FreeMagma
open Law

/-- O43: the commutativity axiom itself can be instantiated in the support-local derivation
calculus without constructing any total `(Bool ⊕ κ) → FreeMagma β` substitution.

Only the two variables that actually occur in the law are assigned representatives. -/
def deriveSupport'_ambientCommutativity_instance
    {κ β : Type} (a b : FreeMagma β) :
    deriveSupport' (ambientCommutativityCtx κ) ((a ⋆ b) ≃ (b ⋆ a)) := by
  have hE : ambientCommutativityLaw κ ∈ ambientCommutativityCtx κ := by
    simp [ambientCommutativityCtx]
  let σ : (x : Bool ⊕ κ) → (ambientCommutativityLaw κ).Mem x → FreeMagma β :=
    fun x hx =>
      match x with
      | Sum.inl false => a
      | Sum.inl true => b
      | Sum.inr k => False.elim (by
          have hfalse : False := by
            simpa [Law.MagmaLaw.Mem, ambientCommutativityLaw, FreeMagma.Mem] using hx
          exact hfalse)
  simpa [ambientCommutativityLaw, Law.MagmaLaw.supportSubst, FreeMagma.supportSubst, σ] using
    (deriveSupport'.SubstAxSupport hE σ)

/-- The ordinary derivation architecture can consume the same support-local certificate once a
source-variable equality decision is supplied. This keeps the translation-back boundary explicit. -/
def derive'_ambientCommutativity_instance_of_decidableEq
    {κ β : Type} [DecidableEq (Bool ⊕ κ)] (a b : FreeMagma β) :
    ambientCommutativityCtx κ ⊢' ((a ⋆ b) ≃ (b ⋆ a)) :=
  derive'_of_deriveSupport'_decidable (deriveSupport'_ambientCommutativity_instance a b)
