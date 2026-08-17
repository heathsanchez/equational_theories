import equational_theories.ManuallyProved.Equation1729.SmallMagma

namespace Eq1729

open AddToMagma

/-- Benchmark reconstruction of the pre-PR #1162 `reduce_to_new_axioms` proof.
The merged patch is not consulted. -/
theorem reduce_to_new_axioms_capital
    {S' : N → SM} {L₀' : N → N} {op : N → N → M}
    (h_i' : axiom_i' L₀')
    (h_iii' : axiom_iii' S' L₀')
    (h_iv' : axiom_iv' S' L₀')
    (h_v : axiom_v S' op)
    (h_vi' : axiom_vi' S' op)
    (h_vii' : axiom_vii' S' L₀' op) :
    ∃ (G : Type) (_ : Magma G), Equation1729 G ∧ ¬ Equation817 G := by
  suffices E : ExtOpsWithProps SM N
  · exact ⟨M, extMagmaInst E, ExtMagma_sat_eq1729 E, ExtMagma_unsat_eq817 E⟩
  exact {
    S := S
    L := fun a => Eq1729.L a
    R := fun a => Eq1729.R a
    S' := S'
    L' := fun a => Eq1729.L' h_i' a
    R' := fun a => Eq1729.R' a
    rest_map := op
    squaring_prop_SM := by intros; rfl
    left_map_SM := by
      intro x y
      simp [Eq1729.L, SM_op_eq_add, add_comm]
    right_map_SM := by
      intro x y
      simp [Eq1729.R, Eq1729.L, SM_op_eq_add]
    SM_sat_1729 := SM_obeys_1729
    axiom_1 := by
      intro a x
      simp only [Eq1729.L', SM_square_square_eq_zero, Equiv.coe_fn_mk, Function.comp_apply]
      apply (R' a).symm.injective
      unfold axiom_i' at h_i'
      have hi (t : N) : L₀' (L₀' t) = (R' 0).symm t := congrFun h_i' t
      symm
      calc
        (R' 0).symm (L₀' (R' 0 (R' (S a) x)))
            = L₀' (L₀' (L₀' (R' 0 (R' (S a) x)))) := by
                rw [hi]
        _ = L₀' ((R' 0).symm (R' 0 (R' (S a) x))) := by
                rw [hi]
        _ = L₀' (R' (S a) x) := by simp
    axiom_21 := by
      intro a b y h
      exact R'_axiom_iia a b y h
    axiom_22 := by
      intro a x
      exact R'_axiom_iib a x
    axiom_3 := by
      intro x y a h
      simpa [Eq1729.L, Eq1729.L', Function.comp_apply] using h_iii' a x y h
    axiom_4 := by
      intro x
      simpa [Eq1729.L', Function.comp_apply] using h_iv' x
    axiom_5 := by
      intro x
      exact h_v x
    axiom_6 := by
      intro y a
      simpa [Eq1729.L] using h_vi' y a
    axiom_7 := by
      intro x y hxy hno
      have hno' : ∀ a : SM, x ≠ R' a y := by
        intro a ha
        exact hno ⟨a, ha⟩
      obtain ⟨z, hz1, hz2⟩ := h_vii' x y hxy hno'
      refine ⟨z, hz1, ?_⟩
      simpa [Eq1729.L', Function.comp_apply] using hz2
  }

end Eq1729
