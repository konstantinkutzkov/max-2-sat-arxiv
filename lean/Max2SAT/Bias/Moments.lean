import Max2SAT.Bias.Incidence
import Max2SAT.Bias.FairCoin

/-! Exact means of fixed-preference score comparisons. -/
namespace Max2SAT.FairCoin
noncomputable section

theorem average_list_sum (l : List α) (f : α → Assignment n → ℝ) :
    average n (fun x => (l.map (fun a => f a x)).sum) =
      (l.map (fun a => average n (f a))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simpa [average_add] using congrArg (average n (f a)+·) ih

theorem average_finset_sum (s : Finset α) (f : α → Assignment n → ℝ) :
    average n (fun x => ∑ a ∈ s, f a x)=∑ a ∈ s, average n (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha,average_add,ih]

theorem average_update (f : Assignment n → ℝ) (i : Fin n) :
    average n f=(average n (fun x => f (Function.update x i false))+
      average n (fun x => f (Function.update x i true)))/2 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [average,update_cons_zero]
      ring
    · simp only [average,update_cons_succ]
      rw [ih (fun x => f (Fin.cons false x)) j,ih (fun x => f (Fin.cons true x)) j]
      ring

theorem average_literal (a : Literal n) :
    average n (fun x => (a.value x : ℝ))=1/2 := by
  rw [average_update _ a.var]
  rcases a with ⟨i,p⟩
  cases p <;> simp [Literal.value,Literal.eval]

theorem average_lhs (C : Constraint n) :
    average n (fun x => (C.lhs x : ℝ))=(C.terms.length : ℝ)/2 := by
  simp only [Constraint.lhs,Int.cast_list_sum,List.map_map,Function.comp_def]
  rw [average_list_sum]
  simp [average_literal,List.sum_replicate,div_eq_mul_inv]

end
end Max2SAT.FairCoin

namespace Max2SAT.Bias
open FairCoin
noncomputable section

/-- Gain from replacing the current bit by its fixed preferred value. -/
def benefit (F : Formula n) (p : Fin n → Bool) (i : Fin n) (x : Assignment n) : ℝ :=
  (score F ((preferred p i).force true x)-score F x : ℤ)

def statistic (F : Formula n) (p : Fin n → Bool) (P : Finset (Fin n))
    (x : Assignment n) : ℝ := ∑ i ∈ P, benefit F p i x

theorem mean_benefit (F : Formula n) (p : Fin n → Bool) (i : Fin n)
    (hF : wellFormed F) :
    average n (benefit F p i) =
      ((D F i : ℝ)/2-((pruningConstraint F (preferred p i)).bound+1 : ℤ))/2 := by
  let v := preferred p i
  have hmix : average n (fun x => (score F x : ℝ)) =
      (average n (fun x => (score F (v.force true x) : ℝ))+
       average n (fun x => (score F (v.force false x) : ℝ)))/2 := by
    have hh := average_update (fun x => (score F x : ℝ)) i
    cases hp : p i <;> simpa [v,preferred,Literal.force,hp,add_comm] using hh
  have hg : (fun x => (score F (v.force true x) : ℝ)-(score F (v.force false x) : ℝ)) =
      (fun x => ((pruningConstraint F v).lhs x : ℝ)-((pruningConstraint F v).bound+1 : ℤ)) := by
    funext x
    exact_mod_cast (pruning_gain_identity F v x hF).symm
  have hm := congrArg (average n) hg
  rw [average_sub,average_sub,average_lhs,average_const,pruning_length F v hF] at hm
  unfold benefit
  simp only [Int.cast_sub]
  rw [average_sub]
  change _ = ((D F v.var : ℝ)/2-((pruningConstraint F v).bound+1 : ℤ))/2
  linarith

theorem mean_initial_benefit (F : Formula n) (i : Fin n) (hF : wellFormed F) :
    average n (benefit F (initialPreference F) i) = |(gap F i : ℝ)|/4 := by
  rw [mean_benefit F _ i hF,pruning_bound_counts F _ hF]
  have hD := (degree_counts F i hF).1
  by_cases hg : 0≤gap F i
  · have hr : 0≤(gap F i : ℝ) := by exact_mod_cast hg
    rw [abs_of_nonneg hr]
    simp only [preferred,initialPreference,decide_eq_true hg]
    change ((D F i : ℝ)/2-((d2 F (pos i).neg-d1 F (pos i)+d1 F (pos i).neg-1)+1 : ℤ))/2 = _
    push_cast
    have hDr : (D F i : ℝ)=(d2 F (pos i) : ℝ)+(d2 F (pos i).neg : ℝ) := by exact_mod_cast hD
    simp only [gap,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_ofNat]
    linarith
  · have hr : (gap F i : ℝ)<0 := by exact_mod_cast (lt_of_not_ge hg)
    rw [abs_of_neg hr]
    simp only [preferred,initialPreference,decide_eq_false hg]
    change ((D F i : ℝ)/2-((d2 F (pos i).neg.neg-d1 F (pos i).neg+d1 F (pos i).neg.neg-1)+1 : ℤ))/2 = _
    simp only [Literal.neg_neg]
    push_cast
    have hDr : (D F i : ℝ)=(d2 F (pos i) : ℝ)+(d2 F (pos i).neg : ℝ) := by exact_mod_cast hD
    simp only [gap,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_ofNat]
    linarith

theorem mean_statistic (F : Formula n) (P : Finset (Fin n)) (hF : wellFormed F) :
    average n (statistic F (initialPreference F) P) =
      (∑ i ∈ P, |(gap F i : ℝ)|)/4 := by
  unfold statistic
  rw [average_finset_sum]
  simp_rw [mean_initial_benefit F _ hF]
  rw [Finset.sum_div]

end
end Max2SAT.Bias
