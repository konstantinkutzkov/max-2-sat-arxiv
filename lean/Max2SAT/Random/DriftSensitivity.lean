import Max2SAT.Random.EdgeDataLaw

/-! Changing one independent edge input affects only its two endpoint
requirements. The sum of squared influences is controlled by degree
normalization, regardless of neighborhood overlap. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {E : Finset (Edge n)}

theorem sqrt_change_bound (X Y L : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hL : 0 ≤ L) (h : |X-Y| ≤ L^2) : |Real.sqrt X-Real.sqrt Y| ≤ L := by
  have hx := Real.sqrt_nonneg X
  have hy := Real.sqrt_nonneg Y
  have hx2 := Real.sq_sqrt hX
  have hy2 := Real.sq_sqrt hY
  rcases le_total X Y with hxy | hyx
  · have hs := Real.sqrt_le_sqrt hxy
    have habs := (abs_le.1 h).1
    have hp := mul_nonneg hx (sub_nonneg.2 hs)
    rw [abs_of_nonpos (sub_nonpos.2 hs)]
    nlinarith
  · have hs := Real.sqrt_le_sqrt hyx
    have habs := (abs_le.1 h).2
    have hp := mul_nonneg hy (sub_nonneg.2 hs)
    rw [abs_of_nonneg (sub_nonneg.2 hs)]
    nlinarith

theorem variance_data_update (i : Fin n) (D : E → EdgeData m) (e : E) (a : EdgeData m) :
    varianceData E i (Function.update D e a)-varianceData E i D =
      if i=e.val.val.1 ∨ i=e.val.val.2 then
        (dataCoefficient (decide (partner i e.val < i)) (side i e.val) a)^2 -
        (dataCoefficient (decide (partner i e.val < i)) (side i e.val) (D e))^2 else 0 := by
  unfold varianceData
  rw [sum_incident E i (fun f => (dataCoefficient (decide (partner i f.val < i)) (side i f.val)
      ((Function.update D e a) f))^2),
    sum_incident E i (fun f => (dataCoefficient (decide (partner i f.val < i)) (side i f.val) (D f))^2),
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single e]
  · by_cases he : i=e.val.val.1 ∨ i=e.val.val.2 <;> simp [he]
  · intro f _ hf
    simp [Function.update_of_ne hf]
  · simp

theorem sqrt_variance_update (i : Fin n) (D : E → EdgeData m) (e : E) (a : EdgeData m) :
    |Real.sqrt (varianceData E i (Function.update D e a))-Real.sqrt (varianceData E i D)| ≤
      if i=e.val.val.1 ∨ i=e.val.val.2 then (m:ℝ) else 0 := by
  by_cases hi : i=e.val.val.1 ∨ i=e.val.val.2
  · rw [ite_eq_left hi]
    apply sqrt_change_bound _ _ _ (variance_data_bounds i _).1 (variance_data_bounds i D).1 (Nat.cast_nonneg _)
    rw [variance_data_update, ite_eq_left hi]
    have ha := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg m)).2
      (data_coefficient_bound (decide (partner i e.val < i)) (side i e.val) a)
    have hb := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg m)).2
      (data_coefficient_bound (decide (partner i e.val < i)) (side i e.val) (D e))
    rw [sq_abs] at ha hb
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (dataCoefficient (decide (partner i e.val < i)) (side i e.val) a),
      sq_nonneg (dataCoefficient (decide (partner i e.val < i)) (side i e.val) (D e))]
  · have h := variance_data_update i D e a
    rw [ite_eq_right hi] at h ⊢
    rw [sub_eq_zero.1 h, sub_self, abs_zero]

def edgeInfluence (E : Finset (Edge n)) (m : ℕ) (e : E) : ℝ :=
  (m:ℝ)*(supportWeight E e.val.val.1+supportWeight E e.val.val.2)/13

theorem drift_data_update (C : Finset (Fin n)) (D : E → EdgeData m) (e : E) (a : EdgeData m) :
    |driftData E C (Function.update D e a)-driftData E C D| ≤ edgeInfluence E m e := by
  unfold driftData
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hs : ∀ i ∈ C,
      |supportWeight E i*Real.sqrt (varianceData E i (Function.update D e a))/13 -
        supportWeight E i*Real.sqrt (varianceData E i D)/13| ≤
      (if i=e.val.val.1 then (m:ℝ)*supportWeight E i/13 else 0) +
      (if i=e.val.val.2 then (m:ℝ)*supportWeight E i/13 else 0) := by
    intro i _
    have h := mul_le_mul_of_nonneg_left (sqrt_variance_update i D e a) (support_weight_pos (E:=E) i).le
    have he : supportWeight E i*Real.sqrt (varianceData E i (Function.update D e a))/13 -
        supportWeight E i*Real.sqrt (varianceData E i D)/13 =
        supportWeight E i*(Real.sqrt (varianceData E i (Function.update D e a))-Real.sqrt (varianceData E i D))/13 := by ring
    rw [he, abs_div, abs_mul, abs_of_pos (support_weight_pos (E:=E) i), abs_of_pos (by norm_num : (0:ℝ)<13)]
    by_cases hl : i=e.val.val.1 <;> by_cases hr : i=e.val.val.2
    · have hne := ne_of_lt e.val.property
      exact False.elim (hne (hl.symm.trans hr))
    · rw [ite_eq_left (Or.inl hl : i=e.val.val.1 ∨ i=e.val.val.2)] at h
      rw [ite_eq_left hl, ite_eq_right hr, add_zero]
      nlinarith
    · rw [ite_eq_left (Or.inr hr : i=e.val.val.1 ∨ i=e.val.val.2)] at h
      rw [ite_eq_right hl, ite_eq_left hr, zero_add]
      nlinarith
    · rw [ite_eq_right (not_or.2 ⟨hl,hr⟩), mul_zero] at h
      rw [ite_eq_right hl, ite_eq_right hr, zero_add]
      nlinarith
  apply (Finset.sum_le_sum hs).trans
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq']
  have h1 : (0:ℝ) ≤ (m:ℝ)*supportWeight E e.val.val.1/13 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (support_weight_pos (E:=E) _).le) (by norm_num)
  have h2 : (0:ℝ) ≤ (m:ℝ)*supportWeight E e.val.val.2/13 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (support_weight_pos (E:=E) _).le) (by norm_num)
  unfold edgeInfluence
  split_ifs <;> nlinarith

theorem degree_square_sum (w : Fin n → ℝ) :
    (∑ i, (w i)^2*(incident E i).card) =
      ∑ e : E, ((w e.val.val.1)^2+(w e.val.val.2)^2) := by
  have he : ∀ i, (w i)^2*(incident E i).card =
      ∑ e : E, if i=e.val.val.1 ∨ i=e.val.val.2 then (w i)^2 else 0 := by
    intro i
    rw [← sum_incident E i (fun _ => (w i)^2)]
    simp [mul_comm]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hi : ∀ i : Fin n,
      (if i=e.val.val.1 ∨ i=e.val.val.2 then (w i)^2 else 0) =
        (if i=e.val.val.1 then (w i)^2 else 0)+(if i=e.val.val.2 then (w i)^2 else 0) := by
    intro i
    have hn := ne_of_lt e.val.property
    by_cases h1 : i=e.val.val.1 <;> by_cases h2 : i=e.val.val.2 <;> simp_all
  simp_rw [hi]
  simp [Finset.sum_add_distrib]

theorem edge_influence_budget : (∑ e : E, (edgeInfluence E m e)^2) ≤ 2*(m:ℝ)^2*n/169 := by
  have h : (∑ e : E, (supportWeight E e.val.val.1+supportWeight E e.val.val.2)^2) ≤ 2*n := by
    calc
      _ ≤ ∑ e : E, 2*((supportWeight E e.val.val.1)^2+(supportWeight E e.val.val.2)^2) := by
        apply Finset.sum_le_sum
        intro e _
        nlinarith [sq_nonneg (supportWeight E e.val.val.1-supportWeight E e.val.val.2)]
      _ = 2*∑ i, (supportWeight E i)^2*(incident E i).card := by
        rw [← Finset.mul_sum, degree_square_sum]
      _ ≤ 2*∑ _i : Fin n, (1:ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum (fun i _ => support_weight_squared_degree i)
      _ = _ := by simp
  have he : (∑ e : E, (edgeInfluence E m e)^2) =
      (m:ℝ)^2*(∑ e : E, (supportWeight E e.val.val.1+supportWeight E e.val.val.2)^2)/169 := by
    simp only [edgeInfluence,div_pow,mul_pow]
    norm_num
    rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (m:ℝ))
  nlinarith

end
end Max2SAT.RandomInput
