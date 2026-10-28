import Max2SAT.Bias.Moments

/-! Coordinate influence bounds for accumulated preferred-value comparisons. -/
namespace Max2SAT.Bias
open FairCoin
noncomputable section

private theorem literal_update_other (a : Literal n) (x : Assignment n) (w : Fin n)
    (b : Bool) (h : a.var≠w) : a.value (Function.update x w b)=a.value x := by
  simp [Literal.value,Literal.eval,h]

private theorem literal_change (a : Literal n) (x y : Assignment n) :
    |(a.value x : ℝ)-(a.value y : ℝ)|≤1 := by
  have h1 := a.value_nonneg x; have h2 := a.value_nonneg y
  have h3 := a.value_le_one x; have h4 := a.value_le_one y
  rw [abs_le]; constructor <;> exact_mod_cast (by omega : _)

theorem lhs_change (terms : List (Literal n)) (x : Assignment n) (w : Fin n) (b : Bool) :
    |(((terms.map (fun a => a.value (Function.update x w b))).sum : ℤ) : ℝ)-
      (((terms.map (fun a => a.value x)).sum : ℤ) : ℝ)|≤termCount terms w := by
  induction terms with
  | nil => simp [termCount]
  | cons a terms ih =>
    simp only [List.map_cons,List.sum_cons,Int.cast_add]
    calc
      _ = |((a.value (Function.update x w b) : ℝ)-a.value x)+
        ((((terms.map (fun a => a.value (Function.update x w b))).sum : ℤ) : ℝ)-
        (((terms.map (fun a => a.value x)).sum : ℤ) : ℝ))| := by congr 1; ring
      _ ≤ |(a.value (Function.update x w b) : ℝ)-a.value x|+_ := abs_add_le _ _
      _ ≤ (if a.var=w then 1 else 0)+(termCount terms w : ℝ) := by
        apply add_le_add ?_ ih
        by_cases h : a.var=w
        · simp only [h,ite_true]; exact literal_change _ _ _
        · simp [h,literal_update_other a x w b h]
      _ = _ := by by_cases h : a.var=w <;> simp [termCount,h]; ring

private theorem clause_score_change (c : Clause n) (x : Assignment n) (w : Fin n)
    (b : Bool) :
    |(c.score (Function.update x w b) : ℝ)-c.score x|≤clauseD w c+clauseU w c := by
  cases c with
  | unit a =>
    by_cases h : a.var=w
    · simpa [clauseD,clauseU,h,Clause.score] using literal_change a (Function.update x w b) x
    · simp [clauseD,clauseU,h,Clause.score,literal_update_other a x w b h]
  | pair a c =>
    by_cases ha : a.var=w
    · have h0 : (0:ℝ) ≤ (if c.var=w then 1 else 0) := by split <;> norm_num
      simp only [clauseD,clauseU,ha,ite_true,Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero]
      simp only [Clause.score]
      split <;> split <;> norm_num <;> positivity
    · by_cases hc : c.var=w
      · simp only [clauseD,clauseU,ha,hc,ite_true,ite_false,Nat.cast_one,Nat.cast_zero,zero_add,add_zero]
        simp only [Clause.score]
        split <;> split <;> norm_num
      · simp [Clause.score,Literal.eval,clauseD,clauseU,ha,hc]

theorem score_change (F : Formula n) (x : Assignment n) (w : Fin n) (b : Bool) :
    |(score F (Function.update x w b) : ℝ)-score F x|≤B F w := by
  induction F with
  | nil => simp [B,D,U]
  | cons c F ih =>
    simp only [score_cons,Int.cast_add]
    calc
      _ = |((c.score (Function.update x w b) : ℝ)-c.score x)+
        ((score F (Function.update x w b) : ℝ)-score F x)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (clause_score_change c x w b) ih
      _ = (B (c::F) w : ℝ) := by simp [B,D,U]; ring

theorem benefit_same (F : Formula n) (p : Fin n → Bool) (i : Fin n)
    (x : Assignment n) (h : x i=p i) : benefit F p i x=0 := by
  have hf := Literal.force_eq_self (preferred p i) x true (by simp [Literal.eval,preferred,h])
  simp [benefit,hf]

theorem benefit_other (F : Formula n) (p : Fin n → Bool) (i : Fin n)
    (x : Assignment n) (h : x i≠p i) (hF : wellFormed F) :
    benefit F p i x=(pruningConstraint F (preferred p i)).lhs x-
      ((pruningConstraint F (preferred p i)).bound+1 : ℤ) := by
  have hf := Literal.force_eq_self (preferred p i) x false (by simp [Literal.eval,preferred,h])
  have hh := pruning_gain_identity F (preferred p i) x hF
  rw [hf] at hh
  unfold benefit
  exact_mod_cast hh.symm

theorem benefit_change_other (F : Formula n) (p : Fin n → Bool) (i w : Fin n)
    (x : Assignment n) (b : Bool) (hi : i≠w) (hF : wellFormed F) :
    |benefit F p i (Function.update x w b)-benefit F p i x|≤
      termCount (pruningConstraint F (preferred p i)).terms w := by
  by_cases hp : x i=p i
  · rw [benefit_same F p i x hp,benefit_same F p i _ (by simp [hi,hp])]
    simp
  · rw [benefit_other F p i x hp hF,benefit_other F p i _ (by simpa [hi]) hF]
    simpa only [sub_sub_sub_cancel_right,Constraint.lhs] using
      lhs_change (pruningConstraint F (preferred p i)).terms x w b

theorem benefit_change_self (F : Formula n) (p : Fin n → Bool) (w : Fin n)
    (x : Assignment n) (b : Bool) :
    |benefit F p w (Function.update x w b)-benefit F p w x|≤B F w := by
  have hf : (preferred p w).force true (Function.update x w b)=(preferred p w).force true x := by
    simp [Literal.force,preferred,Function.update_idem]
  simp only [benefit,hf,Int.cast_sub]
  have he : (score F ((preferred p w).force true x) : ℝ)-score F (Function.update x w b)-
      ((score F ((preferred p w).force true x) : ℝ)-score F x) =
      -((score F (Function.update x w b) : ℝ)-score F x) := by ring
  rw [he,abs_neg]
  exact score_change F x w b

/-- A variable contributes through its own comparison and through neighboring comparisons. -/
theorem statistic_change (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (w : Fin n) (x : Assignment n) (b : Bool) (hF : wellFormed F) :
    |statistic F p P (Function.update x w b)-statistic F p P x|≤
      (if w∈P then (B F w : ℝ) else 0)+(D F w : ℝ) := by
  classical
  unfold statistic
  rw [←Finset.sum_sub_distrib]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hl : ∀ i∈P, |benefit F p i (Function.update x w b)-benefit F p i x|≤
      (if i=w then (B F w : ℝ) else 0)+(termCount (pruningConstraint F (preferred p i)).terms w : ℝ) := by
    intro i hi
    by_cases hw : i=w
    · subst i
      exact le_trans (benefit_change_self F p w x b) (by simp)
    · simpa [hw] using benefit_change_other F p i w x b hw hF
  apply le_trans (Finset.sum_le_sum hl) ?_
  rw [Finset.sum_add_distrib]
  have hc : (∑ i∈P, (termCount (pruningConstraint F (preferred p i)).terms w : ℝ))≤D F w := by
    have hh := Finset.sum_le_univ_sum_of_nonneg (s:=P)
      (f:=fun i => (termCount (pruningConstraint F (preferred p i)).terms w : ℝ)) (fun i => by positivity)
    have he : (∑ i : Fin n, (termCount (pruningConstraint F (preferred p i)).terms w : ℝ))=D F w := by
      exact_mod_cast column_count F p w hF
    rwa [he] at hh
  simpa using add_le_add_left hc (if w∈P then (B F w : ℝ) else 0)

theorem statistic_bounded (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (hF : wellFormed F) :
    BoundedDifferences (statistic F p P) (fun w => 2*(B F w : ℝ)) := by
  intro w x b
  apply le_trans (statistic_change F p P w x b hF)
  have hd : (D F w : ℝ)≤B F w := by simp [B]
  split <;> linarith

end
end Max2SAT.Bias
