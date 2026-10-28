import Max2SAT.Random.OrderedExposure
import Max2SAT.Random.ConcentrationTools

/-! Independent edge inputs for the available variance. Bounded extension
outside the support lets bounded differences apply without extra assumptions
on zero-probability pair patterns. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

abbrev EdgeData (m : ℕ) := Pattern m × Signs

def clippedPattern (K : Pattern m) : Pattern m := if size K ≤ m then K else 0

theorem clipped_size (K : Pattern m) : size (clippedPattern K) ≤ m := by
  unfold clippedPattern
  split_ifs with h
  · exact h
  · simp [size]

theorem clipped_eq (K : Pattern m) (h : size K ≤ m) : clippedPattern K = K := by
  simp [clippedPattern,h]

def dataCoefficient (earlier left : Bool) (D : EdgeData m) : ℝ :=
  if earlier then pairGain left (clippedPattern D.1) (endpoint (!left) D.2)
  else signedCount left (clippedPattern D.1)/2

def edgeDataLaw (p : PairLaw m κ) : Law (EdgeData m) := tensor p.law uniformSigns

theorem data_coefficient_bound (earlier left : Bool) (D : EdgeData m) :
    |dataCoefficient earlier left D| ≤ m := by
  have hk : (size (clippedPattern D.1) : ℝ) ≤ m := by exact_mod_cast clipped_size D.1
  cases earlier
  · simp only [dataCoefficient, Bool.false_eq_true, ↓reduceIte, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hb := signedCount_bound left (clippedPattern D.1)
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  · exact (pairGain_bound left (clippedPattern D.1) _).trans hk

theorem pair_gain_square_mean (left : Bool) (K : Pattern m) :
    (signedCount left K)^2/4 ≤
      expect uniformSigns (fun r => (pairGain left K (endpoint (!left) r))^2) := by
  have h := sq_nonneg (pairGain left K true - pairGain left K false)
  have he : pairGain left K true + pairGain left K false = signedCount left K := by
    cases left <;> simp [pairGain,signedCount,endpoint,Fintype.sum_prod_type] <;> ring
  rw [← he]
  cases left <;> norm_num [expect,uniformSigns,endpoint,Fintype.sum_prod_type] <;> nlinarith

theorem data_coefficient_second (p : PairLaw m κ) (earlier left : Bool) :
    κ/4 ≤ expect (edgeDataLaw p) (fun D => (dataCoefficient earlier left D)^2) := by
  rw [edgeDataLaw, expect_tensor]
  have hh : expect p.law (fun K => (signedCount left K)^2/4) ≤
      expect p.law (fun K => expect uniformSigns (fun r => (dataCoefficient earlier left (K,r))^2)) := by
    apply expect_mono_support
    intro K hK
    have hclip := clipped_eq K (p.bounded K hK)
    cases earlier
    · norm_num [dataCoefficient,hclip,div_pow]
    · simpa only [dataCoefficient, ↓reduceIte, hclip] using pair_gain_square_mean left K
  have hscale : expect p.law (fun K => (signedCount left K)^2/4) =
      expect p.law (fun K => (signedCount left K)^2)/4 := by simp [expect, Finset.sum_div, mul_div_assoc]
  rw [hscale] at hh
  exact (div_le_div_of_nonneg_right (p.moment left) (by norm_num)).trans hh

def varianceData (E : Finset (Edge n)) (i : Fin n) (D : E → EdgeData m) : ℝ :=
  ∑ e : Incidence E i,
    (dataCoefficient (decide (partner i e.val.val < i)) (side i e.val.val) (D e.val))^2

theorem variance_data_bounds (i : Fin n) (D : E → EdgeData m) :
    0 ≤ varianceData E i D ∧ varianceData E i D ≤ (m:ℝ)^2*(incident E i).card := by
  refine ⟨Finset.sum_nonneg (fun _ _ => sq_nonneg _), ?_⟩
  calc
    _ ≤ ∑ _e : Incidence E i, (m:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro e _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg m)).2
        (data_coefficient_bound (decide (partner i e.val.val < i)) (side i e.val.val) (D e.val))
    _ = _ := by simp [mul_comm]

theorem variance_data_mean (p : E → PairLaw m κ) (i : Fin n) :
    κ*(incident E i).card/4 ≤
      expect (product (fun e => edgeDataLaw (p e))) (varianceData E i) := by
  unfold varianceData
  rw [expect_sum]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (e : Incidence E i) _ =>
    data_coefficient_second (p e.val) (decide (partner i e.val.val < i)) (side i e.val.val))
  have he : ∀ e : Incidence E i,
      expect (product (fun f => edgeDataLaw (p f)))
        (fun D => (dataCoefficient (decide (partner i e.val.val < i)) (side i e.val.val) (D e.val))^2) =
      expect (edgeDataLaw (p e.val))
        (fun D => (dataCoefficient (decide (partner i e.val.val < i)) (side i e.val.val) D)^2) := by
    intro e
    rw [← expect_push (product (fun f => edgeDataLaw (p f))) (fun D => D e.val)
      (fun D => (dataCoefficient (decide (partner i e.val.val < i)) (side i e.val.val) D)^2),
      push_product_apply]
  simp_rw [he]
  simpa [mul_comm, div_mul_eq_mul_div] using h

/-- A deterministic upper bound replaces the variance calculation in the
paper's former square-root argument. -/
theorem sqrt_bounded_below (Y L : ℝ) (hY : 0 ≤ Y) (hL : 0 < L) (hbound : Y ≤ L^2) :
    Y/L ≤ Real.sqrt Y := by
  have hs := (Real.sqrt_le_iff).2 ⟨hL.le,hbound⟩
  apply (div_le_iff₀ hL).2
  nlinarith [mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg Y), Real.sq_sqrt hY]

theorem sqrt_variance_mean (p : E → PairLaw m κ) (hm : 0 < m) (i : Fin n)
    (hd : 0 < (incident E i).card) :
    κ/(4*(m:ℝ)) * Real.sqrt ((incident E i).card : ℝ) ≤
      expect (product (fun e => edgeDataLaw (p e))) (fun D => Real.sqrt (varianceData E i D)) := by
  let d : ℝ := (incident E i).card
  have hd' : 0 < d := by change (0:ℝ) < (incident E i).card; exact_mod_cast hd
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd'
  have h := expect_mono (product (fun e => edgeDataLaw (p e))) (fun D =>
    sqrt_bounded_below (varianceData E i D) ((m:ℝ)*Real.sqrt d)
      (variance_data_bounds i D).1 (mul_pos hm' hs) (by
        rw [mul_pow,Real.sq_sqrt hd'.le]
        exact (variance_data_bounds i D).2))
  have he : expect (product (fun e => edgeDataLaw (p e)))
      (fun D => varianceData E i D/((m:ℝ)*Real.sqrt d)) =
      expect (product (fun e => edgeDataLaw (p e))) (varianceData E i)/((m:ℝ)*Real.sqrt d) := by
    simp [expect, Finset.sum_div, mul_div_assoc]
  rw [he] at h
  have hlow := div_le_div_of_nonneg_right (variance_data_mean p i) (mul_pos hm' hs).le
  apply le_trans ?_ (hlow.trans h)
  dsimp only [d] at *
  apply le_of_eq
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg (incident E i).card)]

end
end Max2SAT.RandomInput
