import Max2SAT.Random.PathBudget
import Max2SAT.Random.FormulaGains
import Max2SAT.Random.SumFeasibility

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- The excess of a generated pruning constraint is the oriented original
score gain plus the strict-improvement offset. -/
theorem branch_cut_excess (F : Formula n) (hF : wellFormed F)
    (free : List (Fin n)) (y : Assignment n) (i : Fin n) (hi : i∈free) :
    ((Random.branchCut F free y i).lhs y:ℝ)-(Random.branchCut F free y i).bound =
      sign (Random.branchLiteral F free y i).positive*gain F i y+1 := by
  let v := Random.branchLiteral F free y i
  let R := (Residual.restrict free.toFinset y F).1
  have hv : v.var=i := rfl
  have hc : ∀ b, Compatible free.toFinset y (v.force b y) := by
    intro b j hj
    have hji : j≠i := by intro he; subst j; exact hj (List.mem_toFinset.mpr hi)
    simp [Literal.force,hv,Function.update,hji]
  have h0 := Residual.restrict_score F free.toFinset y (v.force false y) (hc false)
  have h1 := Residual.restrict_score F free.toFinset y (v.force true y) (hc true)
  have hp := pruning_gain_identity R v y (Residual.restrict_wellFormed F _ y hF)
  have he : (Random.branchCut F free y i).lhs y-(Random.branchCut F free y i).bound =
      score F (v.force true y)-score F (v.force false y)+1 := by
    change (pruningConstraint R v).lhs y-(pruningConstraint R v).bound = _
    change score F (v.force true y)=_+score R (v.force true y) at h1
    change score F (v.force false y)=_+score R (v.force false y) at h0
    omega
  have he' : ((Random.branchCut F free y i).lhs y:ℝ)-(Random.branchCut F free y i).bound =
      (score F (v.force true y):ℝ)-score F (v.force false y)+1 := by exact_mod_cast he
  rw [he']
  change _=sign v.positive*gain F i y+1
  cases hp : v.positive <;> simp [Literal.force,hv,hp,gain,sign]

/-- Sum on a fixed list order, before any early rejections. This gives a
semantic interpretation of the exact rational statistic used by the search. -/
def listComparison (F : Formula n) (w : Fin n → ℚ) (suffix : List (Fin n)) :
    List (Fin n) → Assignment n → ℝ
  | [], _ => 0
  | i::is, y =>
    let p := decide (0≤delta F (i::is++suffix).toFinset y i)
    (if y i≠p then (w i:ℝ)*(sign p*gain F i y+1) else 0)+listComparison F w suffix is y

theorem path_excess_score (F : Formula n) (hF : wellFormed F) (w : Fin n → ℚ)
    (suffix pre : List (Fin n)) (y : Assignment n) :
    (Random.pathExcess F w suffix pre y:ℝ)=listComparison F w suffix pre y := by
  induction pre with
  | nil => simp [Random.pathExcess,listComparison]
  | cons i is ih =>
    simp only [Random.pathExcess,listComparison,Rat.cast_add,ih,branch_preference]
    by_cases hh : y i≠decide (0≤delta F (i::is++suffix).toFinset y i)
    · simp only [ite_eq_left hh]
      push_cast
      rw [branch_cut_excess F hF _ y i (by simp),branch_preference]
    · simp only [ite_eq_right hh,Rat.cast_zero,zero_add]

theorem list_comparison_preprocess (F : Formula n) (hF : wellFormed F) (w : Fin n → ℚ)
    (suffix pre : List (Fin n)) (y : Assignment n) :
    listComparison (preprocess F).1 w suffix pre y=listComparison F w suffix pre y := by
  induction pre with
  | nil => rfl
  | cons i is ih => simp only [listComparison,delta_preprocess F hF,gain_preprocess,ih]

/-- This explicit premise says that the supplied list is the increasing
label order used in the exposure proof. It is independent of the formula. -/
def CanonicalPrefix (suffix pre : List (Fin n)) : Prop :=
  ∀ before i after, pre=before++i::after → (i::after++suffix).toFinset=orderedFree i.val

theorem canonical_tail (suffix : List (Fin n)) (i : Fin n) (is : List (Fin n))
    (h : CanonicalPrefix suffix (i::is)) : CanonicalPrefix suffix is := by
  intro before j after he
  apply h (i::before) j after
  simp [he]

theorem list_comparison_sum (E : Finset (Edge n)) (F : Formula n) (w : Fin n → ℚ)
    (suffix pre : List (Fin n)) (y : Assignment n)
    (hn : pre.Nodup) (ho : CanonicalPrefix suffix pre)
    (hw : ∀ i∈pre, (w i:ℝ)=supportWeight E i) :
    listComparison F w suffix pre y=comparisonSum E F pre.toFinset y := by
  induction pre with
  | nil => simp [listComparison,comparisonSum]
  | cons i is ih =>
    have hi := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    have hf := ho [] i is (by simp)
    rw [listComparison,hf,hw i (by simp),ih ht (canonical_tail suffix i is ho)
      (fun j hj => hw j (by simp [hj]))]
    simp [comparisonSum,hi]

end
end Max2SAT.RandomInput
