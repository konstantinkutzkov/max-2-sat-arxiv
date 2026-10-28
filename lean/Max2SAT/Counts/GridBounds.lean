import Max2SAT.Counts.Grids

/-! The two quantitative projection-grid estimates in cor:spectral.
GridPrograms combines these estimates with the proved analytic theorem. -/
namespace Max2SAT.Counts

theorem radius_nonneg (v : Fin n → ℚ) : 0≤radius v :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem radius_le_sqrt (v : Fin n → ℚ) (hv : ∑ i, (v i : ℝ)^2≤1) :
    (radius v : ℝ)≤Real.sqrt n := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin n => (1:ℝ)) (fun i => |(v i : ℝ)|)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,sq_abs] at hh
  have he : (radius v : ℝ)=∑ i, |(v i : ℝ)| := by simp [radius]
  rw [←he] at hh
  have hmul := mul_le_mul_of_nonneg_left hv (show (0:ℝ)≤n by positivity)
  have hs := Real.sq_sqrt (show (0:ℝ)≤n by positivity)
  have hp := Real.sqrt_nonneg (n:ℝ)
  nlinarith

theorem allowance_total (lam : Fin r → ℚ) (v : Fin r → Fin n → ℚ)
    (δ : Fin r → ℚ) :
    (∑ t, allowance lam v δ t) =
      ∑ k, |lam k| * (δ k*radius (v k)+∑ t, (v k t)^2) := by
  unfold allowance
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [radius,Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    ring
  · apply Finset.sum_congr rfl
    intro t _
    rw [mul_assoc,show |v k t| * |v k t|=(v k t)^2 by rw [←sq, sq_abs]]

theorem allowance_nonneg (lam : Fin r → ℚ) (v : Fin r → Fin n → ℚ)
    (δ : Fin r → ℚ) (hδ : ∀ k, 0≤δ k) (t : Fin n) : 0≤allowance lam v δ t := by
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (add_nonneg (hδ k) (abs_nonneg _))

theorem prefix_allowance_bound (lam : Fin r → ℚ) (v : Fin r → Fin n → ℚ)
    (δ : ℚ) (hδ : 0≤δ) (hv : ∀ k, ∑ t, (v k t : ℝ)^2≤1)
    (P : Finset (Fin n)) :
    ((∑ t∈P, allowance lam v (fun _ => δ) t : ℚ) : ℝ) ≤
      ∑ k, |(lam k : ℝ)| * ((δ:ℝ)*Real.sqrt n+1) := by
  have hpre : (∑ t∈P, allowance lam v (fun _ => δ) t)≤∑ t, allowance lam v (fun _ => δ) t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P)
      (fun t _ _ => allowance_nonneg lam v _ (fun _ => hδ) t)
  have hpre' : ((∑ t∈P, allowance lam v (fun _ => δ) t : ℚ) : ℝ)≤
      ((∑ t, allowance lam v (fun _ => δ) t : ℚ) : ℝ) := by exact_mod_cast hpre
  apply hpre'.trans
  rw [allowance_total]
  push_cast
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hr := radius_le_sqrt (v k) (hv k)
  have hm := mul_le_mul_of_nonneg_left hr (show (0:ℝ)≤δ by exact_mod_cast hδ)
  linarith [hv k]

theorem tuples_length_real_bound (grids : Fin r → List ℚ) (B : ℝ)
    (hB : 0≤B) (hb : ∀ k, ((grids k).length : ℝ)≤B) :
    ((tuples grids).length : ℝ)≤B^r := by
  rw [tuples_length]
  have hl : ∀ l : List (Fin r),
      (((l.map (fun i => (grids i).length)).prod : ℕ) : ℝ)≤B^l.length := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons,List.prod_cons,List.length_cons,Nat.cast_mul,pow_succ]
      have hh := mul_le_mul (hb i) ih (by positivity) hB
      simpa only [mul_comm] using hh
  simpa using hl (List.finRange r)

theorem projection_grid_card_bound (v : Fin r → Fin n → ℚ) (δ : ℚ)
    (hδ : 0<δ) (hv : ∀ k, ∑ t, (v k t : ℝ)^2≤1) :
    ((projectionGrids v (fun _ => δ)).length : ℝ)≤
      (2*Real.sqrt n/(δ:ℝ)+3)^r := by
  apply tuples_length_real_bound
  · positivity
  · intro k
    have hh := coordinate_grid_length_bound (radius (v k)) δ (radius_nonneg _) hδ
    have hh' : ((coordinateGrid (radius (v k)) δ).length : ℝ)≤
        2*(radius (v k) : ℝ)/(δ:ℝ)+3 := by exact_mod_cast hh
    apply hh'.trans
    gcongr
    exact radius_le_sqrt (v k) (hv k)

end Max2SAT.Counts
