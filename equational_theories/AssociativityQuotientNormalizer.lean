import equational_theories.QuotientNormalizerSection

open FreeMagma
open Law

/-- Associativity as a non-collapsing equational theory: parenthesization is forgotten while the
entire ordered leaf sequence is preserved. -/
def associativityLaw : MagmaLaw (Option Bool) :=
  ((Lf (none : Option Bool) ⋆ Lf (some false)) ⋆ Lf (some true)) ≃
    (Lf none ⋆ (Lf (some false) ⋆ Lf (some true)))

def associativityCtx : Ctx (Option Bool) :=
  {associativityLaw}

private theorem freeMagma_toList_ne_nil {β : Type} (t : FreeMagma β) : t.toList ≠ [] := by
  intro h
  have hz : t.toList.length = 0 := by simp [h]
  rw [FreeMagma.toList_length] at hz
  exact t.length_ne_0 hz

/-- Canonical right-associated tree for a nonempty list. -/
def rightAssocList {β : Type} : (xs : List β) → xs ≠ [] → FreeMagma β
  | [], h => False.elim (h rfl)
  | a :: rest, _ =>
      match rest with
      | [] => Lf a
      | b :: bs => Lf a ⋆ rightAssocList (b :: bs) (by simp)

private theorem rightAssocList_proof_irrel {β : Type} (xs : List β)
    (h₁ h₂ : xs ≠ []) : rightAssocList xs h₁ = rightAssocList xs h₂ := by
  have hp : h₁ = h₂ := Subsingleton.elim _ _
  subst hp
  rfl

private theorem append_ne_nil_left {β : Type} {xs ys : List β} (hxs : xs ≠ []) :
    xs ++ ys ≠ [] := by
  intro h
  have hx : xs = [] := (List.append_eq_nil.mp h).1
  exact hxs hx

/-- One primitive associativity rewrite. -/
def derive'_associativity_step {β : Type} (a b c : FreeMagma β) :
    associativityCtx ⊢' ((a ⋆ b) ⋆ c) ≃ (a ⋆ (b ⋆ c)) := by
  let σ : Option Bool → FreeMagma β := fun x =>
    match x with
    | none => a
    | some false => b
    | some true => c
  have hmem : associativityLaw ∈ associativityCtx := by
    simp [associativityCtx]
  have h := derive'.SubstAx hmem σ
  simpa [associativityLaw, σ, FreeMagma.evalInMagma] using h

/-- Concatenating two canonical nonempty trees is derivably equal to the canonical tree for the
concatenated leaf list. -/
def derive'_assoc_canon_append {β : Type} :
    (xs ys : List β) → (hxs : xs ≠ []) → (hys : ys ≠ []) →
      associativityCtx ⊢'
        (rightAssocList xs hxs ⋆ rightAssocList ys hys) ≃
          rightAssocList (xs ++ ys) (append_ne_nil_left hxs)
  | [], _, hxs, _ => False.elim (hxs rfl)
  | a :: rest, ys, hxs, hys => by
      cases rest with
      | nil =>
          cases ys with
          | nil => exact False.elim (hys rfl)
          | cons b bs =>
              exact derive'.Ref
      | cons b bs =>
          let tail : List β := b :: bs
          have htail : tail ≠ [] := by simp [tail]
          have ih := derive'_assoc_canon_append tail ys htail hys
          have hs := derive'_associativity_step
            (Lf a) (rightAssocList tail htail) (rightAssocList ys hys)
          have hc : associativityCtx ⊢'
              (Lf a ⋆ (rightAssocList tail htail ⋆ rightAssocList ys hys)) ≃
                (Lf a ⋆ rightAssocList (tail ++ ys) (append_ne_nil_left htail)) :=
            derive'.Cong derive'.Ref ih
          simpa [rightAssocList, tail] using derive'.Trans hs hc

/-- Canonical right-associated normal form of a magma term. -/
def associativityNormalize {β : Type} (t : FreeMagma β) : FreeMagma β :=
  rightAssocList t.toList (freeMagma_toList_ne_nil t)

private theorem associativityNormalize_eq_of_toList_eq {β : Type} {x y : FreeMagma β}
    (h : x.toList = y.toList) : associativityNormalize x = associativityNormalize y := by
  unfold associativityNormalize
  cases h
  exact rightAssocList_proof_irrel _ _ _

/-- Every term is derivably equal, using associativity alone, to its canonical right-associated
normal form. -/
def derive'_associativity_reduce {β : Type} :
    (t : FreeMagma β) → associativityCtx ⊢' t ≃ associativityNormalize t
  | .Leaf a => derive'.Ref
  | .Fork l r => by
      have dl := derive'_associativity_reduce l
      have dr := derive'_associativity_reduce r
      have dc := derive'.Cong dl dr
      have da := derive'_assoc_canon_append
        l.toList r.toList (freeMagma_toList_ne_nil l) (freeMagma_toList_ne_nil r)
      simpa [associativityNormalize, FreeMagma.toList] using derive'.Trans dc da

/-- Derivability under associativity preserves the full leaf sequence. Soundness is evaluated in
the list magma under append, where term evaluation is exactly `toList`. -/
theorem derive'_associativity_toList_eq {β : Type} {x y : FreeMagma β}
    (d : associativityCtx ⊢' x ≃ y) : x.toList = y.toList := by
  letI : Magma (List β) := ⟨List.append⟩
  have hmodel : List β ⊧ associativityCtx := by
    intro E hE φ
    have hEq : E = associativityLaw := by
      simpa [associativityCtx] using hE
    subst E
    simp [associativityLaw, FreeMagma.evalInMagma, List.append_assoc]
  have eval_toList : ∀ t : FreeMagma β, t ⬝ (fun b => [b]) = t.toList := by
    intro t
    induction t with
    | Leaf a => rfl
    | Fork l r ihl ihr =>
        simp [FreeMagma.evalInMagma, ihl, ihr, FreeMagma.toList]
  have hxy : x ⬝ (fun b => [b]) = y ⬝ (fun b => [b]) :=
    (Soundness'_u d hmodel) (fun b => [b])
  calc
    x.toList = x ⬝ (fun b => [b]) := (eval_toList x).symm
    _ = y ⬝ (fun b => [b]) := hxy
    _ = y.toList := eval_toList y

/-- O30: associativity supplies O29's generic verified-normalizer resource in every codomain. -/
def quotientNormalizerData_associativity {β : Type} :
    QuotientNormalizerData (β := β) associativityCtx where
  normalize := associativityNormalize
  normalize_respects := by
    intro x y h
    obtain ⟨d⟩ := h
    exact associativityNormalize_eq_of_toList_eq (derive'_associativity_toList_eq d)
  reduces := derive'_associativity_reduce

/-- Therefore the associative quotient admits a constructive global section in every codomain. -/
theorem contextQuotientSections_associativity : ContextQuotientSections associativityCtx := by
  apply contextQuotientSections_of_normalizers
  intro β
  exact ⟨quotientNormalizerData_associativity⟩
