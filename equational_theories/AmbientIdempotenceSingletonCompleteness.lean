import equational_theories.IdempotenceNormalizerBoundary
import equational_theories.CompletenessSingletonSupport

open FreeMagma
open Law

/-- Idempotence embedded in an ambient variable type with an arbitrary extra component. -/
def ambientIdempotenceLaw (κ : Type) : MagmaLaw (PUnit ⊕ κ) :=
  (Lf (Sum.inl PUnit.unit) ⋆ Lf (Sum.inl PUnit.unit)) ≃ Lf (Sum.inl PUnit.unit)

def ambientIdempotenceCtx (κ : Type) : Ctx (PUnit ⊕ κ) :=
  {ambientIdempotenceLaw κ}

/-- The ambient idempotence axiom has propositionally singleton support, independently of any
equality procedure on the ambient type. -/
theorem singletonSupport_ambientIdempotence (κ : Type) :
    SingletonSupport (ambientIdempotenceLaw κ) (Sum.inl PUnit.unit) := by
  constructor
  · simp [ambientIdempotenceLaw, MagmaLaw.Mem, FreeMagma.Mem]
  · intro a ha
    rcases a with a | k
    · cases a
      rfl
    · exfalso
      simpa [ambientIdempotenceLaw, MagmaLaw.Mem, FreeMagma.Mem] using ha

/-- Therefore the whole singleton context satisfies O11's support condition. -/
theorem contextSingletonSupport_ambientIdempotence (κ : Type) :
    ContextSingletonSupport (ambientIdempotenceCtx κ) := by
  intro E hE
  have hEq : E = ambientIdempotenceLaw κ := by
    simpa [ambientIdempotenceCtx] using hE
  subst E
  exact ⟨Sum.inl PUnit.unit, singletonSupport_ambientIdempotence κ⟩

/-- O36: choice-free completeness for ambient idempotence through the O11 singleton-support route.
No `DecidableEq κ` and no `DecidableEq β` are assumed. -/
theorem Completeness'_ambientIdempotence_singletonRoute {κ β : Type} {E : MagmaLaw β}
    (h : ambientIdempotenceCtx κ ⊧ E) :
    Nonempty (ambientIdempotenceCtx κ ⊢' E) := by
  exact Completeness'_singletonSupport
    (contextSingletonSupport_ambientIdempotence κ) h
