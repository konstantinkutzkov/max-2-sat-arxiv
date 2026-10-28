import Max2SAT.Random.FormulaGains
import Max2SAT.Random.ProductTools

/-! Delta is the average score gain over uniform unassigned values, as
defined in the paper. This is separate from averaging over random inputs. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {E : Finset (Edge n)}

theorem pairGain_average (left : Bool) (K : Pattern m) :
    expect fair (pairGain left K) = signedCount left K / 2 := by
  cases left <;>
    simp [expect,fair,pairGain,signedCount,endpoint,sign,Fintype.sum_prod_type] <;> ring

theorem conditional_pairGain (free : Finset (Fin n)) (x : Assignment n)
    (j : Fin n) (left : Bool) (K : Pattern m) :
    expect (condition (fairBits (Fin n)) (history (Finset.univ \ free) x)
      (fair_history_positive _ x)) (fun y => pairGain left K (y j)) =
      edgeDelta left K (decide (j ∈ free)) (x j) := by
  have hh := congrArg (fun p => expect p (pairGain left K))
    (push_product_apply (fun i => if i ∈ Finset.univ \ free then point (x i) else fair) j)
  rw [expect_push] at hh
  rw [condition_fair_history,hh]
  by_cases hj : j ∈ free
  · simp [hj,edgeDelta,pairGain_average]
  · simp [hj,edgeDelta,expect,point]

theorem suffix_average_gain (E : Finset (Edge n)) (K : E → Pattern m)
    (units : List (Literal n)) (free : Finset (Fin n)) (x : Assignment n)
    (i : Fin n) (hi : i ∈ free) :
    expect (condition (fairBits (Fin n)) (history (Finset.univ \ free) x)
      (fair_history_positive _ x)) (fun y => gain (generate E K units) i y) =
      delta (generate E K units) free x i := by
  simp_rw [generated_gain E K units i]
  rw [expect_add,expect_const,expect_sum,generated_delta E K units free i x hi]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases hl : i=e.val.val.1
  · simp only [hl,↓reduceIte]
    exact conditional_pairGain free x _ _ _
  · by_cases hr : i=e.val.val.2
    · simp only [ite_eq_right hl,ite_eq_left hr]
      exact conditional_pairGain free x _ _ _
    · simp [hl,hr]

end
end Max2SAT.RandomInput
