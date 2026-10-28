import Max2SAT.Counts.Comparisons

/-! Exact algebra linking the implemented sum to the two statistics in
the accumulation proof. No independence or concentration hypothesis is used. -/
namespace Max2SAT.Counts

theorem centered_bit (b : Bool) : bit b-1/2=direction b/2 := by
  cases b <;> norm_num [direction]

theorem preferred_average (d : ℚ) : direction (decide (0≤d))*d=|d| := by
  by_cases h : 0≤d
  · simp [h,direction,abs_of_nonneg h]
  · simp [h,direction,abs_of_neg (lt_of_not_ge h)]

theorem opposite_direction (a b : Bool) (h : a≠b) : direction b= -direction a := by
  cases a <;> cases b <;> simp_all [direction]

theorem eval_minus_average (A : Affine n) (S : Finset (Fin n)) (x : Assignment n) :
    A.eval x-A.average S x =
      ∑ w, if w∈S then 0 else A.coeff w*direction (x w)/2 := by
  unfold Affine.eval Affine.average
  rw [show (A.constant+∑ w, A.coeff w*bit (x w))-
      (A.constant+∑ w, A.coeff w*(if w∈S then bit (x w) else 1/2)) =
      (∑ w, A.coeff w*bit (x w))-
        ∑ w, A.coeff w*(if w∈S then bit (x w) else 1/2) by ring,
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w∈S
  · simp [hw]
  · simp only [ite_eq_right hw]
    calc
      A.coeff w*bit (x w)-A.coeff w*(1/2) = A.coeff w*(bit (x w)-1/2) := by ring
      _ = A.coeff w*direction (x w)/2 := by rw [centered_bit]; ring

def accumulatedGap (H : Fin n → Affine n) (s : Fin n → ℚ)
    (P : Finset (Fin n)) (round : Fin n → ℕ) (x : Assignment n) : ℚ :=
  ∑ t∈P, if x t≠preference H round x t then
    |(H t).average (earlier round t) x|-s t else 0

def compensation (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (x : Assignment n) : ℚ :=
  ∑ t∈P, if x t≠preference H round x t then
    -(direction (x t))*(∑ w, if round w<round t then 0
      else (H t).coeff w*direction (x w)/2) else 0

theorem comparison_sum_identity (H : Fin n → Affine n) (s : Fin n → ℚ)
    (P : Finset (Fin n)) (round : Fin n → ℕ) (x : Assignment n) :
    (comparisonExpr H s P round x).eval x =
      accumulatedGap H s P round x+compensation H P round x := by
  unfold comparisonExpr accumulatedGap compensation
  rw [Affine.eval_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : x t≠preference H round x t
  · simp only [ite_eq_left ht,Affine.eval_shift,Affine.eval_scale]
    have he := eval_minus_average (H t) (earlier round t) x
    simp only [earlier,Finset.mem_filter,Finset.mem_univ,true_and] at he
    have hp := preferred_average ((H t).average (earlier round t) x)
    change direction (preference H round x t)*(H t).average (earlier round t) x = _ at hp
    have hd := opposite_direction (x t) (preference H round x t) ht
    rw [hd] at hp ⊢
    rw [←he,←hp]
    unfold earlier
    ring
  · simp [ht]

theorem passing_requires_compensation (H : Fin n → Affine n) (s : Fin n → ℚ)
    (P : Finset (Fin n)) (round : Fin n → ℕ) (x : Assignment n) (b : ℚ)
    (hgap : b≤accumulatedGap H s P round x)
    (hpass : (comparisonBudget H s P round x).Holds x) :
    compensation H P round x≤ -b := by
  rw [comparisonBudget,Affine.budget_holds,comparison_sum_identity] at hpass
  linarith

end Max2SAT.Counts
