import Batteries.Data.List.Basic
import equational_theories.Definability.Basic
import equational_theories.Definability.FreeMagmaTerm
import equational_theories.FreeMagmaEvalCongr
import equational_theories.Definability.Simple
import equational_theories.Equations.All

open FirstOrder.Language
open Law
open Law.MagmaLaw

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from any law `lhs = rhs`, where
lhs and rhs are the same shape, but with disjoint sets of variables. -/
theorem Equation46_termDefinableFrom_equalShape {L : NatMagmaLaw}
  (hShape : L.lhs ⬝ (fun _ ↦ Lf 0) = L.rhs ⬝ (fun _ ↦ Lf 0) := by rfl)
  (hDisjoint : L.lhs.elems.val.Disjoint L.rhs.elems := by rw [List.Disjoint]; decide +kernel)
  : Law46.TermDefinableFrom L := by
  intro G M hGL
  use ⟨fun x _ ↦ @Term.realize _ _ M.FOStructure _ (fun _ ↦ x) L.lhs.toTerm⟩
  have hboth : ∀ z : G, L.lhs ⬝ (fun _ ↦ z) = L.rhs ⬝ (fun _ ↦ z) := fun z ↦ by
    have h := congrArg (FreeMagma.evalInMagma (fun _ ↦ z)) hShape
    rwa [FreeMagma.SubstEval, FreeMagma.SubstEval] at h
  have hconst : ∀ x x' : G, L.lhs ⬝ (fun _ ↦ x) = L.lhs ⬝ (fun _ ↦ x') := by
    intro x x'
    let ψ : ℕ → G := fun n ↦ if n ∈ L.lhs.elems.val then x else x'
    calc L.lhs ⬝ (fun _ ↦ x)
        = L.lhs ⬝ ψ :=
          (FreeMagma.evalInMagma_congr _ fun a ha ↦ if_pos ((L.lhs.elems.2.2 a).2 ha)).symm
      _ = L.rhs ⬝ ψ := hGL ψ
      _ = L.rhs ⬝ (fun _ ↦ x') :=
          FreeMagma.evalInMagma_congr _ fun a ha ↦
            if_neg fun hm ↦ hDisjoint hm ((L.rhs.elems.2.2 a).2 ha)
      _ = L.lhs ⬝ (fun _ ↦ x') := (hboth x').symm
  constructor
  · rw [@Law46.models_iff]
    intro x y z w
    show @Term.realize _ _ M.FOStructure _ (fun _ ↦ x) L.lhs.toTerm
        = @Term.realize _ _ M.FOStructure _ (fun _ ↦ z) L.lhs.toTerm
    rw [FreeMagma.toTerm_realize, FreeMagma.toTerm_realize]
    exact hconst x z
  · simpa [Magma.FinArityOp, FreeMagma.toTerm_realize, Function.comp_def] using
      (FreeMagma.eval_comp_termDefinable (G := G) L.lhs (fun _ ↦ (0 : Fin 2)))

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from Equation 40 `x ◇ x = y ◇ y`. -/
theorem Equation46_termDefinableFrom_Equation40 : Law46.TermDefinableFrom Law40 :=
  Equation46_termDefinableFrom_equalShape

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from 4276 `x ◇ (x ◇ x) = y ◇ (y ◇ y)`. -/
theorem Equation46_termDefinableFrom_Equation4276 : Law46.TermDefinableFrom Law4276 :=
  Equation46_termDefinableFrom_equalShape

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from 4308 `x ◇ (x ◇ y) = z ◇ (z ◇ w)`. -/
theorem Equation46_termDefinableFrom_Equation4308 : Law46.TermDefinableFrom Law4308 :=
  Equation46_termDefinableFrom_equalShape

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from 4336 `x ◇ (y ◇ x) = z ◇ (w ◇ z)`. -/
theorem Equation46_termDefinableFrom_Equation4336 : Law46.TermDefinableFrom Law4336 :=
  Equation46_termDefinableFrom_equalShape

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from 4355 `x ◇ (y ◇ y) = z ◇ (w ◇ w)`. -/
theorem Equation46_termDefinableFrom_Equation4355 : Law46.TermDefinableFrom Law4355 :=
  Equation46_termDefinableFrom_equalShape
