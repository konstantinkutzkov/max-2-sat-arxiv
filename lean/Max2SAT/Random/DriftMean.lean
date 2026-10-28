import Max2SAT.Random.EdgeDataLaw

/-! Lower mean of the available drift. The deterministic bound on Y gives
a shorter argument than estimating Var(Y), while preserving the paper's
stated constant. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

def requirementConstant (m : ℕ) (κ : ℝ) : ℝ :=
  Real.sqrt κ/(2*Real.sqrt (1+4*(m:ℝ)^4/κ^2))

theorem requirement_constant_bound (hm : 0 < m) (hk : 0 < κ) :
    requirementConstant m κ ≤ κ/(4*(m:ℝ)) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hr : 0 < Real.sqrt κ := Real.sqrt_pos.2 hk
  have hb : 0 < (1+4*(m:ℝ)^4/κ^2) := by positivity
  have hq : 0 < Real.sqrt (1+4*(m:ℝ)^4/κ^2) := Real.sqrt_pos.2 hb
  have he : (κ*Real.sqrt (1+4*(m:ℝ)^4/κ^2))^2 = κ^2+4*(m:ℝ)^4 := by
    rw [mul_pow, Real.sq_sqrt hb.le]
    field_simp
  have hs : 2*(m:ℝ)*Real.sqrt κ ≤ κ*Real.sqrt (1+4*(m:ℝ)^4/κ^2) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    rw [he]
    have hh := sq_nonneg (κ-2*(m:ℝ)^2)
    have hx := Real.sq_sqrt hk.le
    nlinarith
  unfold requirementConstant
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem requirement_constant_pos (hm : 0 < m) (hk : 0 < κ) :
    0 < requirementConstant m κ := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  unfold requirementConstant
  positivity

theorem support_weight_sqrt_bounds (i : Fin n) (hd : 0 < (incident E i).card) :
    (1:ℝ)/2 ≤ supportWeight E i*Real.sqrt ((incident E i).card : ℝ) ∧
    supportWeight E i*Real.sqrt ((incident E i).card : ℝ) ≤ 1 := by
  have h := Random.sqrt_denominator_bounds (incident E i).card hd
  have hd' : (0:ℝ) < ((Nat.sqrt ((incident E i).card-1)+1 : ℕ) : ℝ) := by positivity
  unfold supportWeight
  rw [one_div_mul_eq_div]
  constructor
  · apply (le_div_iff₀ hd').2
    linarith [h.2]
  · apply (div_le_one hd').2
    exact h.1

theorem drift_data_mean (p : E → PairLaw m κ) (hm : 0 < m) (hk : 0 < κ)
    (C : Finset (Fin n)) (hC : ∀ i∈C, 0 < (incident E i).card) :
    requirementConstant m κ*C.card/26 ≤
      expect (product (fun e => edgeDataLaw (p e))) (driftData E C) := by
  unfold driftData
  rw [expect_sum]
  have hpoint : ∀ i∈C, requirementConstant m κ/26 ≤
      expect (product (fun e => edgeDataLaw (p e)))
        (fun D => supportWeight E i*Real.sqrt (varianceData E i D)/13) := by
    intro i hi
    have hw := support_weight_sqrt_bounds i (hC i hi)
    have hmu := sqrt_variance_mean p hm i (hC i hi)
    have hmul := mul_le_mul_of_nonneg_left hmu (support_weight_pos (E:=E) i).le
    have he : expect (product (fun e => edgeDataLaw (p e)))
        (fun D => supportWeight E i*Real.sqrt (varianceData E i D)/13) =
        supportWeight E i * expect (product (fun e => edgeDataLaw (p e)))
          (fun D => Real.sqrt (varianceData E i D))/13 := by
      simp only [expect, mul_div_assoc, Finset.sum_div, Finset.mul_sum]
      congr 1
      funext D
      ring
    rw [he]
    have hconst := requirement_constant_bound hm hk
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    have hpos : 0 ≤ κ/(4*(m:ℝ)) := by positivity
    have hscale := mul_le_mul_of_nonneg_left hw.1 hpos
    nlinarith
  have hs := Finset.sum_le_sum hpoint
  simpa [mul_div_assoc,mul_comm] using hs

end
end Max2SAT.RandomInput
