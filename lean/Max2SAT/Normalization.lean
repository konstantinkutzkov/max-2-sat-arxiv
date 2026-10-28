import Max2SAT.ConstraintCheck

namespace Max2SAT.Constraint

def NoOpposites (terms : List (Literal n)) : Prop :=
  ∀ a ∈ terms, a.neg ∉ terms

private theorem neg_ne_self (a : Literal n) : a.neg ≠ a := by
  rcases a with ⟨i,p⟩
  cases p <;> simp [Literal.neg]

theorem cancelAux_subset (fuel : ℕ) (C : Constraint n) :
    ∀ a ∈ (cancelAux fuel C).terms, a ∈ C.terms := by
  induction fuel generalizing C with
  | zero => intro a ha; exact ha
  | succ fuel ih =>
    rcases C with ⟨terms,b⟩
    cases terms with
    | nil => intro a ha; exact ha
    | cons v vs =>
      by_cases h : v.neg ∈ vs
      · simp only [cancelAux,ite_eq_left h]
        intro a ha
        exact List.mem_cons_of_mem _ (List.mem_of_mem_erase (ih _ a ha))
      · simp only [cancelAux,ite_eq_right h,List.mem_cons]
        intro a ha
        exact ha.elim Or.inl (fun ht => Or.inr (ih _ a ht))

theorem cancelAux_noOpposites (fuel : ℕ) (C : Constraint n)
    (hf : C.terms.length ≤ fuel) : NoOpposites (cancelAux fuel C).terms := by
  induction fuel generalizing C with
  | zero =>
    have he : C.terms=[] := List.length_eq_zero_iff.mp (by omega)
    simp [cancelAux,NoOpposites,he]
  | succ fuel ih =>
    rcases C with ⟨terms,b⟩
    cases terms with
    | nil => simp [cancelAux,NoOpposites]
    | cons v vs =>
      have hl : vs.length ≤ fuel := by simpa using Nat.le_of_succ_le_succ hf
      by_cases h : v.neg ∈ vs
      · simp only [cancelAux,ite_eq_left h]
        apply ih
        exact le_trans List.length_erase_le hl
      · simp only [cancelAux,ite_eq_right h]
        have ht := ih (Constraint.mk vs b) hl
        have hs := cancelAux_subset fuel (Constraint.mk vs b)
        intro a ha hna
        rcases List.mem_cons.mp ha with ha | ha
        · subst a
          rcases List.mem_cons.mp hna with hna | hna
          · exact neg_ne_self v hna
          · exact h (hs _ hna)
        · rcases List.mem_cons.mp hna with hna | hna
          · have hav : a=v.neg := by rw [←hna,Literal.neg_neg]
            exact h (hav ▸ hs a ha)
          · exact ht a ha hna

theorem normalize_noOpposites (C : Constraint n) : NoOpposites (normalize C).terms :=
  cancelAux_noOpposites C.terms.length C (le_refl _)

/-- A minimum assignment sets every remaining literal occurrence to false. -/
def zeroAssignment (terms : List (Literal n)) : Assignment n :=
  fun i => decide ((Literal.mk i false) ∈ terms)

theorem zeroAssignment_value (terms : List (Literal n)) (h : NoOpposites terms)
    (a : Literal n) (ha : a ∈ terms) : a.value (zeroAssignment terms)=0 := by
  have hn := h a ha
  rcases a with ⟨i,p⟩
  cases p
  · simp [Literal.value,Literal.eval,zeroAssignment,ha]
  · simp only [Literal.neg,Bool.not_true] at hn
    simp [Literal.value,Literal.eval,zeroAssignment,hn]

theorem zeroAssignment_lhs (C : Constraint n) (h : NoOpposites C.terms) :
    C.lhs (zeroAssignment C.terms)=0 := by
  unfold lhs
  apply List.sum_eq_zero
  intro z hz
  rcases List.mem_map.mp hz with ⟨a,ha,rfl⟩
  exact zeroAssignment_value C.terms h a ha

/-- The exact minimum of the original left-hand side, with an explicit
assignment attaining it. This also applies to the temporary summed constraint. -/
theorem minimum_lhs (C : Constraint n) :
    C.lhs (zeroAssignment (normalize C).terms) = C.bound-(normalize C).bound ∧
      ∀ x, C.bound-(normalize C).bound ≤ C.lhs x := by
  constructor
  · have h := cancelAux_exact C.terms.length C (zeroAssignment (normalize C).terms)
    change (normalize C).lhs _ - (normalize C).bound = _ at h
    rw [zeroAssignment_lhs _ (normalize_noOpposites C)] at h
    omega
  · intro x
    have h := cancelAux_exact C.terms.length C x
    have hn := (normalize C).lhs_nonneg x
    change (normalize C).lhs x - (normalize C).bound = _ at h
    omega

/-- Cancellation computes the exact feasibility test for one constraint.
Applying it to the sum remains only a sufficient test for a collection. -/
theorem infeasible_iff (C : Constraint n) :
    infeasible C=true ↔ ¬ ∃ x, C.Holds x := by
  constructor
  · intro h ⟨x,hx⟩
    exact infeasible_sound C h x hx
  · intro h
    by_contra hn
    have hb : 0 ≤ (normalize C).bound := by simpa [infeasible] using hn
    apply h
    refine ⟨zeroAssignment (normalize C).terms, (normalize_iff C _).mp ?_⟩
    change (normalize C).lhs _ ≤ (normalize C).bound
    rw [zeroAssignment_lhs _ (normalize_noOpposites C)]
    exact hb
end Max2SAT.Constraint
