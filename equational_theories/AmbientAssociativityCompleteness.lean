import equational_theories.AssociativityQuotientNormalizer

open FreeMagma
open Law

/-- Associativity embedded in an ambient variable type carrying an arbitrary extra component. -/
def ambientAssociativityLaw (κ : Type) : MagmaLaw ((Option Bool) ⊕ κ) :=
  ((Lf (Sum.inl none) ⋆ Lf (Sum.inl (some false))) ⋆ Lf (Sum.inl (some true))) ≃
    (Lf (Sum.inl none) ⋆ (Lf (Sum.inl (some false)) ⋆ Lf (Sum.inl (some true))))

def ambientAssociativityCtx (κ : Type) : Ctx ((Option Bool) ⊕ κ) :=
  {ambientAssociativityLaw κ}

private theorem ambient_freeMagma_toList_ne_nil {β : Type} (t : FreeMagma β) : t.toList ≠ [] := by
  intro h
  have hz : t.toList.length = 0 := by simp [h]
  rw [FreeMagma.toList_length] at hz
  exact t.length_ne_0 hz

private theorem ambient_append_ne_nil_left {β : Type} {xs ys : List β} (hxs : xs ≠ []) :
    xs ++ ys ≠ [] := by
  intro h
  have hx : xs = [] := (List.append_eq_nil.mp h).1
  exact hxs hx

/-- Primitive associativity rewrite from the ambient axiom. -/
def derive'_ambientAssociativity_step {κ β : Type} (a b c : FreeMagma β) :
    ambientAssociativityCtx κ ⊢' ((a ⋆ b) ⋆ c) ≃ (a ⋆ (b ⋆ c)) := by
  let σ : (Option Bool) ⊕ κ → FreeMagma β := fun x =>
    match x with
    | Sum.inl none => a
    | Sum.inl (some false) => b
    | Sum.inl (some true) => c
    | Sum.inr _ => a
  have hmem : ambientAssociativityLaw κ ∈ ambientAssociativityCtx κ := by
    simp [ambientAssociativityCtx]
  have h := derive'.SubstAx hmem σ
  simpa [ambientAssociativityLaw, σ, FreeMagma.evalInMagma] using h

/-- Canonical-list concatenation lemma for the ambient associativity theory. -/
def derive'_ambientAssoc_canon_append {κ β : Type} :
    (xs ys : List β) → (hxs : xs ≠ []) → (hys : ys ≠ []) →
      ambientAssociativityCtx κ ⊢'
        (rightAssocList xs hxs ⋆ rightAssocList ys hys) ≃
          rightAssocList (xs ++ ys) (ambient_append_ne_nil_left hxs)
  | [], _, hxs, _ => False.elim (hxs rfl)
  | a :: rest, ys, hxs, hys => by
      cases rest with
      | nil =>
          cases ys with
          | nil => exact False.elim (hys rfl)
          | cons b bs => exact derive'.Ref
      | cons b bs =>
          let tail : List β := b :: bs
          have htail : tail ≠ [] := by simp [tail]
          have ih := derive'_ambientAssoc_canon_append tail ys htail hys
          have hs := derive'_ambientAssociativity_step
            (κ := κ) (Lf a) (rightAssocList tail htail) (rightAssocList ys hys)
          have hc : ambientAssociativityCtx κ ⊢'
              (Lf a ⋆ (rightAssocList tail htail ⋆ rightAssocList ys hys)) ≃
                (Lf a ⋆ rightAssocList (tail ++ ys) (ambient_append_ne_nil_left htail)) :=
            derive'.Cong derive'.Ref ih
          simpa [rightAssocList, tail] using derive'.Trans hs hc

/-- The same canonical right-associated normal form works in the ambient theory. -/
def ambientAssociativityNormalize {β : Type} (t : FreeMagma β) : FreeMagma β :=
  rightAssocList t.toList (ambient_freeMagma_toList_ne_nil t)

private theorem ambientAssociativityNormalize_eq_of_toList_eq {β : Type}
    {x y : FreeMagma β} (h : x.toList = y.toList) :
    ambientAssociativityNormalize x = ambientAssociativityNormalize y := by
  unfold ambientAssociativityNormalize
  cases h
  have hp : ambient_freeMagma_toList_ne_nil x = ambient_freeMagma_toList_ne_nil y :=
    Subsingleton.elim _ _
  cases hp
  rfl

/-- Every term reduces to the canonical right-associated tree under the ambient associativity axiom. -/
def derive'_ambientAssociativity_reduce {κ β : Type} :
    (t : FreeMagma β) →
      ambientAssociativityCtx κ ⊢' t ≃ ambientAssociativityNormalize t
  | .Leaf a => derive'.Ref
  | .Fork l r => by
      have dl := derive'_ambientAssociativity_reduce (κ := κ) l
      have dr := derive'_ambientAssociativity_reduce (κ := κ) r
      have dc := derive'.Cong dl dr
      have da := derive'_ambientAssoc_canon_append (κ := κ)
        l.toList r.toList (ambient_freeMagma_toList_ne_nil l) (ambient_freeMagma_toList_ne_nil r)
      simpa [ambientAssociativityNormalize, FreeMagma.toList] using derive'.Trans dc da

/-- Ambient associativity derivability preserves the entire leaf sequence. -/
theorem derive'_ambientAssociativity_toList_eq {κ β : Type} {x y : FreeMagma β}
    (d : ambientAssociativityCtx κ ⊢' x ≃ y) : x.toList = y.toList := by
  letI : Magma (List β) := ⟨List.append⟩
  have hmodel : List β ⊧ ambientAssociativityCtx κ := by
    intro E hE φ
    have hEq : E = ambientAssociativityLaw κ := by
      simpa [ambientAssociativityCtx] using hE
    subst E
    simp [ambientAssociativityLaw, FreeMagma.evalInMagma, List.append_assoc]
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

/-- Verified normalizer data for ambient associativity, independent of equality on κ. -/
def quotientNormalizerData_ambientAssociativity {κ β : Type} :
    QuotientNormalizerData (β := β) (ambientAssociativityCtx κ) where
  normalize := ambientAssociativityNormalize
  normalize_respects := by
    intro x y h
    obtain ⟨d⟩ := h
    exact ambientAssociativityNormalize_eq_of_toList_eq
      (derive'_ambientAssociativity_toList_eq d)
  reduces := derive'_ambientAssociativity_reduce

/-- The three actual axiom variables retract constructively from the arbitrary ambient type. -/
def supportRetractionData_ambientAssociativity (κ : Type) :
    SupportRetractionData (ambientAssociativityLaw κ) where
  retract := fun x =>
    match x with
    | Sum.inl none => ⟨Sum.inl none, by exact .inl (.inl (.inl rfl))⟩
    | Sum.inl (some false) => ⟨Sum.inl (some false), by exact .inl (.inl (.inr rfl))⟩
    | Sum.inl (some true) => ⟨Sum.inl (some true), by exact .inl (.inr rfl)⟩
    | Sum.inr _ => ⟨Sum.inl none, by exact .inl (.inl (.inl rfl))⟩
  retract_on := by
    intro s
    apply Subtype.ext
    rcases s with ⟨x, hx⟩
    cases x with
    | inl o =>
        cases o with
        | none => rfl
        | some b => cases b <;> rfl
    | inr k =>
        have : False := by
          simpa [ambientAssociativityLaw, MagmaLaw.Mem, FreeMagma.Mem] using hx
        exact False.elim this

theorem contextSupportRetract_ambientAssociativity {κ : Type} :
    ∀ E, E ∈ ambientAssociativityCtx κ → SupportRetract E := by
  intro E hE
  have hEq : E = ambientAssociativityLaw κ := by
    simpa [ambientAssociativityCtx] using hE
  subst E
  exact (supportRetractionData_ambientAssociativity κ).toSupportRetract

/-- O31 target: choice-free completeness for associativity embedded beside arbitrary κ. -/
theorem Completeness'_ambientAssociativity {κ β : Type} {E : MagmaLaw β}
    (h : ambientAssociativityCtx κ ⊧ E) :
    Nonempty (ambientAssociativityCtx κ ⊢' E) := by
  exact Completeness'_normalizers
    contextSupportRetract_ambientAssociativity
    (fun γ => ⟨quotientNormalizerData_ambientAssociativity (κ := κ) (β := γ)⟩)
    h
